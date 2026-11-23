import Damp
import Damp.Optimize.LedgerMerge
import Damp.Ledger.Merkle

/-! Checks on `Circuit.ledgerMerge` (`Damp/Optimize/LedgerMerge.lean`): ledger
statements run as one request when the VM cannot tell the difference.

The pass is proved sound against the modelled ledger
(`Circuit.ledgerMerge_soundLedger`, from `ledgerOracle_merge` in
`Damp/Proofs/Ledger/OptMerge.lean`); these checks show the merge firing on the
common shapes (cell writes, reads, map inserts, counters, effects), each side
condition stopping it, runs through the executor against the VM model
(`oracles merkleHooks`) giving the same results and failures, and a chain of 64
writes staying within `maxMergeOps`. -/
namespace Examples.OptLedgerMerge
open Damp Damp.IR Damp.Impact Damp.Ledger

private def key (i : Nat) : Aligned Expr := fieldKey i
private def one : Expr := .const 1
private def fk (i : Int) : Aligned Expr := ⟨[.field], [.const i]⟩

/-- `Cell.read` of field `i` into `v`. -/
private def rd (i v : Nat) : Stmt :=
  .ledger one [v] [.dup 0, .idx false false [key i], .popeq false [.field] [.var v]]
/-- `Cell.write` of `e` to field `i`. -/
private def wr (i : Nat) (e : Expr) : Stmt :=
  .ledger one [] [.push false (key i), .push true ⟨[.field], [e]⟩, .ins false 1]
/-- `Counter.increment` of field `i` by 1. -/
private def inc (i : Nat) : Stmt :=
  .ledger one [] [.idx false true [key i], .addi (.const 1), .ins true 1]
/-- `Map.insert` into the map of field `i` at key `k`. -/
private def ins (i : Nat) (k : Aligned Expr) (e : Expr) : Stmt :=
  .ledger one [] [.idx false true [key i], .push false k, .push true ⟨[.field], [e]⟩, .ins false 1, .ins true 1]
/-- `Map.lookup` in the map of field `i` at key `k`, into `v`. -/
private def look (i : Nat) (k : Aligned Expr) (v : Nat) : Stmt :=
  .ledger one [v] [.dup 0, .idx false false [key i], .idx false false [k], .popeq false [.field] [.var v]]
/-- A write of the effects (slot 0 of the effects array: a hash set). -/
private def eff (e : Expr) : Stmt :=
  .ledger one [] [.swap 0, .idx true true [key 0], .push false ⟨[.bytes 32], [.const 0, e]⟩, .pushNull false,
    .ins true 2, .swap 0]
/-- A read of the call context (slot 2), cached: the context is fully cached. -/
private def ctx (v : Nat) : Stmt :=
  .ledger one [v] [.dup 2, .idx true false [key 2], .popeq false [.bytes 8] [.var v]]
/-- A cached read of the contract state: it misses in a request of its own. -/
private def rdCached (i v : Nat) : Stmt :=
  .ledger one [v] [.dup 0, .idx true false [key i], .popeq false [.field] [.var v]]

private def mk (n : Nat) (body : List Stmt) (outputs : List Expr) : Circuit where
  name := "t"
  args := []
  inputs := (List.range n).map fun v => { name := s!"x{v}", var := v, range := none }
  body := body.toArray
  result := .tuple []
  outputs := outputs

private def shape (c : Circuit) : String :=
  String.ofList (c.body.toList.map fun | .ledger .. => 'L' | .bind .. => 'B' | .witness .. => 'W' | _ => 'A')
private def after (c : Circuit) : String := shape c.ledgerMerge

private def opsOf : Stmt → List (Op Expr)
  | .ledger _ _ ops => ops
  | _ => []

/-! ### The analysis by itself -/

-- the common shapes may follow anything that leaves the stack as a request starts it
#guard mergeable (opsOf (wr 1 (.var 0))) (opsOf (wr 2 (.var 0)))
#guard mergeable (opsOf (rd 1 10)) (opsOf (rd 2 11))
#guard mergeable (opsOf (ins 3 (fk 5) (.var 0))) (opsOf (ins 3 (fk 6) (.var 0)))
#guard mergeable (opsOf (inc 4)) (opsOf (inc 4))
#guard mergeable (opsOf (wr 1 (.var 0))) (opsOf (eff (.var 0)))
#guard mergeable (opsOf (wr 1 (.var 0))) (opsOf (ctx 12))
-- a first program that changes the effects, keeping them in the form the runtime re-encodes them
-- to (Examples/OptLedgerMergeEffects.lean has the side conditions)
#guard mergeable (opsOf (eff (.var 0))) (opsOf (wr 1 (.var 0)))
-- a cached read of the contract state misses in a request of its own, not after a write of it
#guard !mergeable (opsOf (wr 1 (.var 0))) (opsOf (rdCached 1 10))
-- a first program leaving four entries, or a weak value as the contract state
#guard !mergeable [.push false (key 1)] (opsOf (wr 1 (.var 0)))
#guard !mergeable [.pop, .pushNull false] (opsOf (wr 1 (.var 0)))
-- a jump of the first program past its end
#guard !mergeable [.jmp 1] (opsOf (wr 1 (.var 0)))

/-! ### The pass -/

-- consecutive statements of every common shape become one
#guard after (mk 1 [wr 1 (.var 0), wr 2 (.var 0), inc 4, ins 3 (fk 5) (.var 0), rd 1 10, ctx 11, eff (.var 0)]
  [.var 10, .var 11]) == "L"
-- across statements that are not ledger statements, which the second does not depend on
#guard after (mk 1 [rd 1 10, .bind 20 "t" (.add (.var 10) (.const 1)), .assert (.var 10) "m", wr 2 (.var 0)]
  [.var 20]) == "LBA"
-- the second uses what the first reads (`composable_inner.add`): not merged
#guard after (mk 1 [rd 1 10, wr 1 (.add (.var 0) (.var 10))] []) == "LL"
-- the second uses what a statement between binds
#guard after (mk 1 [rd 1 10, .bind 20 "t" (.add (.var 10) (.const 1)), wr 2 (.var 20)] []) == "LBL"
-- different guards
#guard after (mk 1 [wr 1 (.var 0), .ledger (.var 0) [] (opsOf (wr 2 (.var 0)))] []) == "LL"
-- the effects first, then a state write, and the other way round: merged
#guard after (mk 1 [eff (.var 0), wr 1 (.var 0)] []) == "L"
#guard after (mk 1 [wr 1 (.var 0), eff (.var 0)] []) == "L"

/-! ### Runs through the executor against the VM model -/

private def σ₀ : LedgerState where
  context := .array [.cell ⟨[.bytes 32], [12345]⟩, .null, .cell (AV.ofU64 7)]
  effects := .array (List.replicate 9 (.map []))
  state := .array [.null, .cell ⟨[.field], [3]⟩, .cell ⟨[.field], [4]⟩,
    .map [(⟨[.field], [7]⟩, .cell ⟨[.field], [70]⟩)], .cell (AV.ofU64 9)]

private def noWitness : String → List Fr → Unit → Option (List Fr × Unit) := fun _ _ _ => none

private def runAt (σ : LedgerState) (c : Circuit) (inputs : List Nat) : String :=
  match Exec.run Crypto.prims (oracles merkleHooks (Exec.liftWitness noWitness)) c (inputs.map Fr.ofNat) () σ with
  | none => "fails"
  | some r => reprStr (r.outputs.map (·.val), r.priv.map (·.val), r.pub.map (·.val), r.ledger.state,
      r.ledger.context, r.ledger.effects)

private def run := runAt σ₀
-- the executor's whole result, public transcript included, is the same
private def same (c : Circuit) (inputs : List Nat) : Bool := run c inputs == run c.ledgerMerge inputs

private def c1 := mk 1 [wr 1 (.var 0), wr 2 (.var 0), inc 4, ins 3 (fk 5) (.var 0), rd 1 10, ctx 11,
  look 3 (fk 5) 12, eff (.var 0), rd 2 13] [.var 10, .var 11, .var 12, .var 13]
#guard after c1 == "L"
#guard same c1 [5]
#guard run c1 [5] != "fails"
-- a write of a field that does not exist fails, merged or not
private def c2 := mk 1 [wr 1 (.var 0), wr 9 (.var 0), rd 1 10] [.var 10]
#guard after c2 == "L"
#guard run c2 [5] == "fails"
#guard same c2 [5]
-- a lookup of a missing key fails, merged or not
private def c3 := mk 1 [wr 1 (.var 0), look 3 (fk 9) 10] [.var 10]
#guard after c3 == "L"
#guard run c3 [5] == "fails"
#guard same c3 [5]
-- a cached read of the state alone fails (a cache miss); it is never merged after a write
private def c4 := mk 1 [wr 1 (.var 0), rdCached 1 10] [.var 10]
#guard after c4 == "LL"
#guard run c4 [5] == "fails"
-- not run (guard 0): the reads are zero either way
private def c5 := mk 1 [.ledger (.const 0) [10] (opsOf (rd 1 10)), .ledger (.const 0) [] (opsOf (wr 2 (.var 0)))]
  [.var 10]
#guard after c5 == "L"
#guard same c5 [5]
#guard run c5 [5] != "fails"

/-! ### Size: a chain of 64 writes of distinct fields is merged into requests of at most
`maxMergeOps` instructions -/

private def chain (n : Nat) : Circuit :=
  mk 1 ((List.range n).map fun i => wr (i + 1) (.add (.var 0) (.const i))) []

private def opCount (c : Circuit) : List Nat := c.body.toList.map fun s => (opsOf s).length

#guard after (chain 32) == "L"
#guard opCount (chain 32).ledgerMerge == [96]
#guard opCount (chain 64).ledgerMerge == [192]
-- 400 writes (1200 instructions): cut where the next one would pass `maxMergeOps`
#guard opCount (chain 400).ledgerMerge == [1023, 177]
#guard (opCount (chain 400).ledgerMerge).all (· ≤ maxMergeOps)
private def σ₁ : LedgerState := { σ₀ with state := .array (List.replicate 70 (.cell ⟨[.field], [1]⟩)) }
#guard runAt σ₁ (chain 64) [3] == runAt σ₁ (chain 64).ledgerMerge [3]
#guard runAt σ₁ (chain 64) [3] != "fails"

end Examples.OptLedgerMerge
