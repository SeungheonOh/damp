import Damp
import Damp.Optimize.LedgerReuse
import Damp.Ledger.Merkle

/-! Checks on the opt-in ledger pass `Circuit.ledgerReuse`, run by the build.

The pass is proved sound against the modelled ledger in
`Damp/Proofs/Optimize/LedgerReuse.lean` (`Circuit.ledgerReuse_soundLedger :
Pass.SoundLedger Circuit.ledgerReuse`). These checks show each rewrite firing,
each side condition stopping it, and runs through the executor against the VM
model (`oracles merkleHooks`) leaving the same outputs and ledger state. -/
namespace Examples.OptLedgerReuse
open Damp Damp.IR Damp.Impact Damp.Ledger

private def key (i : Nat) : Aligned Expr := fieldKey i
private def one : Expr := .const 1

/-- `Cell.read` of field `i` (alignment `field`) into `v`, under `g`. -/
private def rd (g : Expr) (i v : Nat) : Stmt :=
  .ledger g [v] [.dup 0, .idx false false [key i], .popeq false [.field] [.var v]]
/-- A cached read of the call context's slot 0 (32 bytes, two limbs) into `v`, `v+1`. -/
private def ctx (v : Nat) : Stmt :=
  .ledger one [v, v + 1] [.dup 2, .idx true false [key 0], .popeq true [.bytes 32] [.var v, .var (v + 1)]]
/-- `Cell.write` of `e` (alignment `field`) to field `i`, under `g`. -/
private def wr (g : Expr) (i : Nat) (e : Expr) : Stmt :=
  .ledger g [] [.push false (key i), .push true ⟨[.field], [e]⟩, .ins false 1]

private def mk (n : Nat) (body : List Stmt) (outputs : List Expr) : Circuit where
  name := "t"
  args := []
  inputs := (List.range n).map fun v => { name := s!"x{v}", var := v, range := none }
  body := body.toArray
  result := .tuple []
  outputs := outputs

/-- One letter per statement: `L` ledger, `B` binding, `W` witness, `A` other. -/
private def shape (c : Circuit) : String :=
  String.ofList (c.body.toList.map fun | .ledger .. => 'L' | .bind .. => 'B' | .witness .. => 'W' | _ => 'A')

private def after (c : Circuit) : String := shape c.ledgerReuse

/-! ### The rewrites fire -/

-- A repeated read of a field becomes a binding.
#guard after (mk 0 [rd one 1 10, rd one 1 11] [.var 10, .var 11]) == "LB"
-- A read after a write of the same field binds the written operand.
#guard after (mk 1 [wr one 1 (.var 0), rd one 1 10] [.var 10]) == "LB"
-- A read, a write of the same field, a read: the second read takes the written value.
#guard after (mk 1 [rd one 1 10, wr one 1 (.add (.var 10) (.var 0)), rd one 1 11] [.var 11]) == "LLB"
-- A read of the call context survives writes of the contract state.
#guard after (mk 1 [ctx 10, wr one 1 (.var 0), ctx 12] [.var 12]) == "LLBB"
-- Reads of other fields in between do not stop it.
#guard after (mk 0 [rd one 1 10, rd one 2 11, rd one 1 12] [.var 12]) == "LLB"
-- The same guard (a variable) on both reads.
#guard after (mk 1 [rd (.var 0) 1 10, rd (.var 0) 1 11] [.var 11]) == "LB"

/-! ### The side conditions stop it -/

-- A write of the field in between, with an operand too wide to forward (two atoms): the read stays.
#guard after (mk 1 [rd one 1 10,
    .ledger one [] [.push false (key 1), .push true ⟨[.field, .field], [.var 0, .var 0]⟩, .ins false 1],
    rd one 1 11] [.var 11]) == "LLL"
-- Any other ledger statement (here a counter increment of the same field) forgets state facts.
#guard after (mk 0 [rd one 1 10, .ledger one [] [.idx false true [key 1], .addi (.const 1), .ins true 1],
    rd one 1 11] [.var 11]) == "LLL"
-- A read under a guard does not answer a later read under another guard.
#guard after (mk 1 [rd (.var 0) 1 10, rd one 1 11] [.var 11]) == "LL"
#guard after (mk 1 [rd one 1 10, rd (.var 0) 1 11] [.var 11]) == "LL"
-- A guard whose variable is rebound in between.
#guard after (mk 1 [rd (.var 0) 1 10, .bind 0 "g" (.const 1), rd (.var 0) 1 11] [.var 11]) == "LBL"
-- A read whose earlier answer variable is rebound in between (by a witness).
#guard after (mk 0 [rd one 1 10, .witness one "w" [] [(10, none)] (.prim .field), rd one 1 11] [.var 11]) == "LWL"
-- A key whose variable is rebound in between.
#guard after (mk 1 [.ledger one [10] [.dup 0, .idx false false [⟨[.field], [.var 0]⟩], .popeq false [.field] [.var 10]],
    .bind 0 "k" (.const 5),
    .ledger one [11] [.dup 0, .idx false false [⟨[.field], [.var 0]⟩], .popeq false [.field] [.var 11]]] [.var 11]) == "LBL"
-- A cached `idx` on the contract state is not a plain read (it can miss the cache and fail).
#guard after (mk 0 [rd one 1 10, .ledger one [11] [.dup 0, .idx true false [key 1], .popeq false [.field] [.var 11]]]
    [.var 11]) == "LL"
-- A write of a byte string over 31 bytes (two limbs) is not forwarded.
#guard after (mk 2 [.ledger one [] [.push false (key 1), .push true ⟨[.bytes 40], [.var 0, .var 1]⟩, .ins false 1],
    .ledger one [10, 11] [.dup 0, .idx false false [key 1], .popeq false [.bytes 40] [.var 10, .var 11]]]
    [.var 10]) == "LL"
-- A written operand larger than `maxExprSize` is not copied.
#guard after (mk 1 [wr one 1 ((List.range 20).foldl (fun e _ => .add e (.var 0)) (.var 0)), rd one 1 10]
    [.var 10]) == "LL"

/-! ### Runs through the executor against the VM model -/

private def σ₀ : LedgerState where
  context := .array [.cell ⟨[.bytes 32], [12345]⟩, .null, .cell (AV.ofU64 7)]
  effects := .array (List.replicate 9 (.map []))
  state := .array [.null, .cell ⟨[.field], [3]⟩, .cell ⟨[.field], [4]⟩]

private def noWitness : String → List Fr → Unit → Option (List Fr × Unit) := fun _ _ _ => none

/-- The executor's outputs, private transcript and final ledger state, printed. -/
private def run (c : Circuit) (inputs : List Nat) : String :=
  match Exec.run Crypto.prims (oracles merkleHooks noWitness) c (inputs.map Fr.ofNat) () σ₀ with
  | none => "fails"
  | some r => reprStr (r.outputs.map (·.val), r.priv.map (·.val), r.ledger.state, r.ledger.context, r.ledger.effects)

private def same (c : Circuit) (inputs : List Nat) : Bool := run c inputs == run c.ledgerReuse inputs

private def c1 := mk 1 [rd one 1 10, wr one 2 (.add (.var 10) (.var 0)), rd one 2 11, rd one 1 12, ctx 13, ctx 15]
  [.var 11, .var 12, .var 13, .var 16]
-- the write of field 2 leaves what the pass knows of field 1 (frame reasoning, `frameKeeps`)
#guard after c1 == "LLBBLBB"
#guard same c1 [5]
#guard run c1 [5] != "fails"
-- a guard off: the reads are zeros, on both sides
private def c2 := mk 1 [rd (.var 0) 1 10, rd (.var 0) 1 11, wr (.var 0) 2 (.var 11), rd (.var 0) 2 12]
  [.var 10, .var 11, .var 12]
#guard after c2 == "LBLB"
#guard same c2 [0]
#guard same c2 [1]
-- a guard that is not a boolean: both fail
#guard same c2 [2]
#guard run c2 [2] == "fails"
-- a read of a missing field fails, and still fails when its repetition is dropped
private def c3 := mk 0 [rd one 7 10, rd one 7 11] [.var 11]
#guard after c3 == "LB"
#guard run c3 [] == "fails"
#guard same c3 []

/-! ### Size: a chain of 32 write-read pairs grows by a bounded amount per read -/

private def chain (n : Nat) : Circuit :=
  mk 1 ((List.range n).flatMap fun i => [wr one 1 (.add (.var (100 + i)) (.var 0)), rd one 1 (101 + i)])
    [.var (100 + n)]

private def nodes (c : Circuit) : Nat :=
  c.body.toList.foldl (fun n s => n + match s with
    | .bind _ _ e => e.size
    | .ledger _ _ ops => 8 * ops.length
    | _ => 1) 0

#guard after (chain 32) == String.ofList ((List.range 32).flatMap fun _ => ['L', 'B'])
#guard nodes (chain 32).ledgerReuse ≤ nodes (chain 32)
#guard same (chain 32) [3]

end Examples.OptLedgerReuse
