import Damp
import Damp.Optimize.AssertEq
import Damp.Optimize.Commute

/-! Checks on two small rewrites, run by the build: `assert (e == 1)` as
`assert e` (`Circuit.assertEq`, `--O2`) and canonical operand order of
commutative operations (`Circuit.commuteOpt`). Proved sound in
`Damp/Proofs/Optimize/AssertEq.lean` and `Damp/Proofs/Optimize/Commute.lean`. -/
namespace Examples.OptSmall
open Damp Damp.IR

/-- A circuit with inputs `0..n-1`, a body and outputs. -/
private def mk (n : Nat) (body : List Stmt) (outputs : List Expr) : Circuit where
  name := "t"
  args := []
  inputs := (List.range n).map fun v => { name := s!"x{v}", var := v, range := none }
  body := body.toArray
  result := .tuple []
  outputs := outputs

def prims : Zkir.Prims where
  transientHash xs := xs.foldl (· + ·) 0
  persistentHash _ xs := some (List.replicate 32 (xs.length % 256))
  transientCommit xs r := xs.foldl (· + ·) r

def accepts (c : Circuit) (inputs : List Fr) : Bool := (c.run prims inputs [] []).isSome

/-- The conditions of a circuit's `assert`s, in order. -/
private def conds (c : Circuit) : List Expr :=
  c.body.toList.filterMap fun | .assert e _ => some e | _ => none

/-! ### `assert (e == 1)` -/

private def ae := mk 1
  [.assert (.eq (.var 0) (.const 1)) "a",
   .assert (.eq (.const 1) (.var 0)) "b",
   .assert (.eq (.var 0) (.const 2)) "c"]
  []

-- Both sides fire; a comparison with another constant stays.
#guard conds (Circuit.assertEq ae) == [.var 0, .var 0, .eq (.var 0) (.const 2)]
-- No boolean knowledge is needed: on 0, 1 and 5 (not a boolean) the two
-- `assert`s pass and fail together.
private def one := mk 1 [.assert (.eq (.var 0) (.const 1)) "a"] []
#guard [0, 1, 5].all fun x => accepts one [x] == accepts (Circuit.assertEq one) [x]
#guard accepts one [1] && !accepts one [5]
-- The same rewrite inside a `select` would not be exact: `select (e == 1) a b`
-- is `b` for e = 5, while `select e a b` fails. The pass touches `assert` only.
#guard (Expr.select (.eq (.var 0) (.const 1)) (.const 7) (.const 8)).eval prims (fun _ => 5) == some 8
#guard (Expr.select (.var 0) (.const 7) (.const 8)).eval prims (fun _ => 5) == none

/-! ### Commutative duplicates -/

private def dup := mk 2
  [.bind 2 "p" (.eq (.var 0) (.var 1)),
   .bind 3 "q" (.eq (.var 1) (.var 0)),
   .ledger (.const 1) [] [.addi (.var 2), .addi (.var 3)]]
  []

/-- Number of ZKIR instructions of the emitted circuit (0 if it cannot be emitted). -/
def size (c : Circuit) : Nat :=
  match Emit.circuit c with
  | .ok src => src.instructions.size
  | .error _ => 0

-- `x == y` and `y == x` become one `test_eq`.
#guard size (Circuit.commuteOpt dup) + 1 == size dup
-- A circuit with nothing to share is left exactly as it was.
private def nodup := mk 2 [.ledger (.const 1) [] [.addi (.add (.var 1) (.var 0))]] []
#guard size (Circuit.commuteOpt nodup) == size nodup

/-! ### On a contract -/

ledger
  flags : Set Field

/-- Compact's `assert(flags.member(x) == true, ..)`: the read is not range
    checked, so only the `assert` rewrite removes the comparison. -/
circuit check (x : Field) : Unit := do
  require ((← flags.member (disclose x)) ==. .true) "missing"

contract optSmall

#guard size check.circuit.optimizeFull + 1 == size check.circuit.optimize

end Examples.OptSmall
