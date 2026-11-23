import Damp
import Damp.Optimize.LedgerReuse
import Damp.Ledger.Merkle

/-! Checks on the frame reasoning of `Circuit.ledgerReuse` (`frameKeeps`,
`Damp/Optimize/LedgerFrame.lean`, proved in `Damp/Proofs/Ledger/OptFrame.lean`),
on reads through two `idx` (`Map.lookup`), and on map-insert facts.

The pass is proved sound against the modelled ledger
(`Circuit.ledgerReuse_soundLedger`); these checks show each new rewrite firing,
each side condition stopping it, runs through the executor against the VM model
(`oracles merkleHooks`) leaving the same outputs and ledger state, and a
depth-32 chain staying bounded. -/
namespace Examples.OptLedgerFrame
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
/-- `Map.remove` from the map of field `i` of key `k`. -/
private def rem (i : Nat) (k : Aligned Expr) : Stmt :=
  .ledger one [] [.idx false true [key i], .push false k, .rem false, .ins true 1]
/-- `Map.lookup` in the map of field `i` at key `k`, into `v`. -/
private def look (i : Nat) (k : Aligned Expr) (v : Nat) : Stmt :=
  .ledger one [v] [.dup 0, .idx false false [key i], .idx false false [k], .popeq false [.field] [.var v]]
/-- A write of the effects (slot 0 of the effects array: a hash set). -/
private def eff (e : Expr) : Stmt :=
  .ledger one [] [.swap 0, .idx true true [key 0], .push false ⟨[.bytes 32], [.const 0, e]⟩, .pushNull false,
    .ins true 2, .swap 0]
/-- A write at a key that is not a constant. -/
private def wrv (k : Nat) (e : Expr) : Stmt :=
  .ledger one [] [.push false ⟨[.bytes 1], [.var k]⟩, .push true ⟨[.field], [e]⟩, .ins false 1]

private def mk (n : Nat) (body : List Stmt) (outputs : List Expr) : Circuit where
  name := "t"
  args := []
  inputs := (List.range n).map fun v => { name := s!"x{v}", var := v, range := none }
  body := body.toArray
  result := .tuple []
  outputs := outputs

private def shape (c : Circuit) : String :=
  String.ofList (c.body.toList.map fun | .ledger .. => 'L' | .bind .. => 'B' | .witness .. => 'W' | _ => 'A')
private def after (c : Circuit) : String := shape c.ledgerReuse

/-! ### The frame analysis by itself -/

private def π (path : List (Aligned Expr)) : List AV := constPrefix maxFramePath path
private def opsOf : Stmt → List (Op Expr)
  | .ledger _ _ ops => ops
  | _ => []

-- writes of another field, of the effects, and reads keep field 1
#guard frameKeeps (π [key 1]) (opsOf (wr 2 (.var 0)))
#guard frameKeeps (π [key 1]) (opsOf (inc 2))
#guard frameKeeps (π [key 1]) (opsOf (ins 3 (fk 5) (.var 0)))
#guard frameKeeps (π [key 1]) (opsOf (rem 3 (fk 5)))
#guard frameKeeps (π [key 1]) (opsOf (eff (.var 0)))
#guard frameKeeps (π [key 1]) (opsOf (look 3 (fk 5) 9))
-- a write of the same field does not
#guard !frameKeeps (π [key 1]) (opsOf (wr 1 (.var 0)))
#guard !frameKeeps (π [key 1]) (opsOf (inc 1))
-- nor a write at a key that is not a constant
#guard !frameKeeps (π [key 1]) (opsOf (wrv 0 (.var 0)))
-- nested: another constant key of the same map keeps `[3, 7]`, the same key does not
#guard frameKeeps (π [key 3, fk 7]) (opsOf (ins 3 (fk 5) (.var 0)))
#guard frameKeeps (π [key 3, fk 7]) (opsOf (rem 3 (fk 5)))
#guard !frameKeeps (π [key 3, fk 7]) (opsOf (ins 3 (fk 7) (.var 0)))
#guard !frameKeeps (π [key 3, fk 7]) (opsOf (rem 3 (fk 7)))
#guard !frameKeeps (π [key 3, fk 7]) (opsOf (ins 3 ⟨[.field], [.var 0]⟩ (.var 0)))
-- the protected path is at most `maxFramePath` constant keys, and empty protects nothing
#guard (π [key 3, fk 7, fk 8, fk 9]).length == 3
#guard !frameKeeps [] (opsOf (wr 2 (.var 0)))

/-! ### The rewrites fire -/

-- a read survives writes of other fields: cell, counter, map, effects
#guard after (mk 1 [rd 1 10, wr 2 (.var 0), inc 4, ins 3 (fk 5) (.var 0), eff (.var 0), rd 1 11] [.var 11]) ==
  "LLLLLB"
-- a cell write survives writes of other fields
#guard after (mk 1 [wr 1 (.var 0), wr 2 (.var 0), rd 1 10] [.var 10]) == "LLB"
-- a map insert answers a lookup of the same key, across an insert at another key of the same map
#guard after (mk 1 [ins 3 (fk 7) (.var 0), ins 3 (fk 5) (.var 0), look 3 (fk 7) 10] [.var 10]) == "LLB"
-- a repeated lookup
#guard after (mk 0 [look 3 (fk 7) 10, look 3 (fk 7) 11] [.var 11]) == "LB"
-- a map insert at a key held in a variable answers a lookup of the same variable
#guard after (mk 2 [ins 3 ⟨[.field], [.var 1]⟩ (.var 0), look 3 ⟨[.field], [.var 1]⟩ 10] [.var 10]) == "LB"

/-! ### The side conditions stop it -/

-- a write of the same field in between
#guard after (mk 1 [rd 1 10, inc 1, rd 1 11] [.var 11]) == "LLL"
-- a write at a key that is not a constant
#guard after (mk 2 [rd 1 10, wrv 1 (.var 0), rd 1 11] [.var 11]) == "LLL"
-- an insert at the same key of the map in between, with another value: the later insert answers
#guard after (mk 2 [look 3 (fk 7) 10, ins 3 (fk 7) (.var 1), look 3 (fk 7) 11] [.var 11]) == "LLB"
-- a removal of the same key: the lookup stays (it may fail)
#guard after (mk 1 [ins 3 (fk 7) (.var 0), rem 3 (fk 7), look 3 (fk 7) 10] [.var 10]) == "LLL"
-- an insert at a variable key in between
#guard after (mk 2 [look 3 (fk 7) 10, ins 3 ⟨[.field], [.var 1]⟩ (.var 0), look 3 (fk 7) 11] [.var 11]) == "LLL"
-- the key variable of a map fact rebound
#guard after (mk 2 [ins 3 ⟨[.field], [.var 1]⟩ (.var 0), .bind 1 "k" (.const 4), look 3 ⟨[.field], [.var 1]⟩ 10]
  [.var 10]) == "LBL"

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
  | some r => reprStr (r.outputs.map (·.val), r.priv.map (·.val), r.ledger.state, r.ledger.context, r.ledger.effects)

private def run := runAt σ₀
private def same (c : Circuit) (inputs : List Nat) : Bool := run c inputs == run c.ledgerReuse inputs

private def c1 := mk 1 [rd 1 10, wr 2 (.var 0), inc 4, ins 3 (fk 5) (.var 0), eff (.var 0), rd 1 11,
  look 3 (fk 7) 12, ins 3 (fk 8) (.var 10), look 3 (fk 7) 13, look 3 (fk 8) 14]
  [.var 11, .var 13, .var 14]
#guard after c1 == "LLLLLBLLBB"
#guard same c1 [5]
#guard run c1 [5] != "fails"
-- a lookup of a missing key fails, and still fails when its repetition is dropped
private def c2 := mk 0 [look 3 (fk 9) 10, look 3 (fk 9) 11] [.var 11]
#guard after c2 == "LB"
#guard run c2 [] == "fails"
#guard same c2 []
-- an insert into a field that is not a map fails, on both sides
private def c3 := mk 1 [ins 1 (fk 7) (.var 0), look 1 (fk 7) 10] [.var 10]
#guard after c3 == "LB"
#guard run c3 [2] == "fails"
#guard same c3 [2]

/-! ### Size: a chain of 32 writes of distinct fields, each followed by reads of all
earlier ones, grows by a bounded amount per read (facts are capped at `maxFacts`) -/

private def chain (n : Nat) : Circuit :=
  mk 1 ((List.range n).flatMap fun i => [wr (i + 1) (.add (.var 0) (.const i)), rd 1 (100 + i)])
    ((List.range n).map fun i => .var (100 + i))

private def nodes (c : Circuit) : Nat :=
  c.body.toList.foldl (fun n s => n + match s with
    | .bind _ _ e => e.size
    | .ledger _ _ ops => 8 * ops.length
    | _ => 1) 0

#guard after (chain 32) == "LB" ++ String.ofList ((List.range 31).flatMap fun _ => ['L', 'B'])
#guard nodes (chain 32).ledgerReuse ≤ nodes (chain 32)
private def σ₁ : LedgerState := { σ₀ with state := .array (List.replicate 40 (.cell ⟨[.field], [1]⟩)) }
#guard runAt σ₁ (chain 32) [3] == runAt σ₁ (chain 32).ledgerReuse [3]
#guard runAt σ₁ (chain 32) [3] != "fails"

end Examples.OptLedgerFrame
