import Damp
import Damp.Optimize.Asserts

/-! Checks on `Circuit.asserts` (`Damp/Optimize/Asserts.lean`), run by the build.

Each rule is shown firing, and each side condition is shown blocking a
rewrite that would change what a run accepts, with the input on which the
naive rewrite would differ. The pass is proved sound in
`Damp/Proofs/Optimize/Asserts.lean` (`Circuit.asserts_sound`). -/
namespace Examples.OptAsserts
open Damp Damp.IR

def prims : Zkir.Prims where
  transientHash xs := xs.foldl (· + ·) 0
  persistentHash _ xs := some (List.replicate 32 (xs.length % 256))
  transientCommit xs r := xs.foldl (· + ·) r

/-- A circuit with inputs `0..n-1`, a body and outputs. -/
def mk (n : Nat) (body : List Stmt) (outputs : List Expr) : Circuit where
  name := "t"
  args := []
  inputs := (List.range n).map fun v => { name := s!"x{v}", var := v, range := none }
  body := body.toArray
  result := .tuple []
  outputs := outputs

/-- What a run produces that anyone can observe. -/
def observe (c : Circuit) (inputs priv pub : List Fr) : Option (List Nat × List (List Nat)) :=
  (c.run prims inputs priv pub).map fun o =>
    (o.outputs.map (·.val), (o.groups.filter (·.active)).map fun g => g.vals.map (·.val))

/-- The rewritten circuit behaves as the original on this run. -/
def agrees (c : Circuit) (inputs priv pub : List Fr) : Bool :=
  observe c inputs priv pub == observe c.asserts inputs priv pub

/-- The main expression of each statement: a binding's body, an assert's
    condition, a range check's subject, a witness or ledger statement's guard. -/
def mains (c : Circuit) : List Expr :=
  c.body.toList.map fun
    | .bind _ _ e | .assert e _ | .constrain e _ | .witness e .. | .ledger e .. => e

private def x : Expr := .var 0
private def y : Expr := .var 1
private def z : Expr := .var 2
private def bad : Expr := .lt 8 x (.const 1)   -- fails unless x fits in 8 bits

/-! ### Asserted conditions -/

-- A repeated assert is dropped.
private def dup := mk 2 [.assert (.lt 8 x y) "a", .assert (.lt 8 x y) "b"] []
#guard dup.asserts.body.size == 1
#guard agrees dup [3, 5] [] [] && agrees dup [5, 3] [] [] && agrees dup [300, 5] [] []

-- An asserted condition is 1 wherever it occurs again, also under `disclose`;
-- `select 1 x y` is then `x` (`y` is a variable: it has a value).
private def reuse := mk 2 [.assert (.lt 8 x y) "a",
  .bind 2 "r" (.select (.disclose (.lt 8 (.disclose x) y)) x y)] [z]
#guard mains reuse.asserts == [.lt 8 x y, x]
#guard agrees reuse [3, 5] [] [] && agrees reuse [5, 3] [] [] && agrees reuse [300, 5] [] []

-- An asserted equality with a constant is a substitution.
private def eqc := mk 1 [.assert (.eq x (.const 5)) "five", .bind 1 "d" (.add x x)] [y]
#guard mains eqc.asserts == [.eq x (.const 5), .add (.const 5) (.const 5)]
#guard mains eqc.asserts.simplify == [.eq x (.const 5)]
#guard eqc.asserts.simplify.outputs == [.const 10]
#guard agrees eqc [5] [] [] && agrees eqc [6] [] []
-- The other orientation too.
private def eqc' := mk 1 [.assert (.eq (.const 5) x) "five", .bind 1 "d" (.add x x)] [y]
#guard mains eqc'.asserts == [.eq (.const 5) x, .add (.const 5) (.const 5)]

-- A conjunction, as `&&.` builds it (`select a b 0`), makes both sides 1.
private def conj := mk 3 [.assert (.select (.eq x y) (.lt 8 y z) (.const 0)) "both",
  .bind 3 "p" (.eq x y), .bind 4 "q" (.lt 8 y z)] [.var 3, .var 4]
#guard mains conj.asserts == [.select (.eq x y) (.lt 8 y z) (.const 0), .const 1, .const 1]
#guard agrees conj [4, 4, 9] [] [] && agrees conj [4, 5, 9] [] [] && agrees conj [4, 4, 1] [] []

-- A negation, as `!.` builds it (`select a 0 1`), makes `a` 0: a witness
-- guarded by `a` gets the guard 0, and `simplify` then drops the call.
private def neg := mk 2 [.assert (.select (.eq x y) (.const 0) (.const 1)) "differ",
  .witness (.eq x y) "w" [] [(2, some (.bits 8))] (.prim .field)] [z]
#guard mains neg.asserts == [.select (.eq x y) (.const 0) (.const 1), .const 0]
#guard neg.asserts.simplify.body.size == 1
#guard agrees neg [1, 2] [] [] && agrees neg [1, 1] [7] []

-- A statement guarded by an asserted condition gets the guard 1.
private def guard1 := mk 2 [.assert (.eq x y) "same",
  .ledger (.eq x y) [] [.addi x]] []
#guard mains guard1.asserts == [.eq x y, .const 1]
#guard agrees guard1 [3, 3] [] [] && agrees guard1 [3, 4] [] []

-- Only a branch that is a constant other than the value says which branch was
-- taken. `select c a b` being 1 with `b` not constant says nothing about `c`:
-- for x0 = 0, x1 = 1 the condition below is 1 while `x0 == 1` is 0.
private def orish := mk 2 [.assert (.select (.eq x (.const 1)) (.const 1) y) "or",
  .bind 2 "c" (.eq x (.const 1))] [z]
#guard mains orish.asserts == [.select (.eq x (.const 1)) (.const 1) y, .eq x (.const 1)]
#guard observe orish [0, 1] [] [] == some ([0], [])
#guard agrees orish [0, 1] [] [] && agrees orish [1, 0] [] []

-- An equality of two variables is not used: renaming saves nothing.
private def eqv := mk 2 [.assert (.eq x y) "same", .bind 2 "s" (.add x y)] [z]
#guard mains eqv.asserts == [.eq x y, .add x y]

/-! ### Facts are about the current environment -/

-- After `x0` is rebound, the fact `x0 = 5` is forgotten.
private def rebind := mk 1 [.assert (.eq x (.const 5)) "five", .bind 0 "x" (.const 7),
  .bind 1 "d" (.add x (.const 1))] [y]
#guard mains rebind.asserts == [.eq x (.const 5), .const 7, .add x (.const 1)]
#guard observe rebind.asserts [5] [] [] == some ([8], [])
#guard agrees rebind [5] [] [] && agrees rebind [4] [] []
-- So is a fact about the read variable of a ledger statement, and the
-- statement's operands are left alone.
private def readv := mk 1 [.assert (.eq x (.const 5)) "five",
  .ledger (.const 1) [0] [.addi x, .popeq false [] [x]], .bind 1 "d" (.add x (.const 1))] [y]
#guard mains readv.asserts == [.eq x (.const 5), .const 1, .add x (.const 1)]
#guard agrees readv [5] [] [9] && agrees readv [5] [] []

/-! ### What has been evaluated

These rewrites drop a subexpression that could fail. `simplify` makes them
only when it cannot (`Expr.total`); here it is known to have been evaluated
already, in an environment that agrees on its variables. -/

-- `0 * e`: `e` was bound before.
private def mul0 := mk 1 [.bind 1 "b" bad, .bind 2 "z" (.mul (.const 0) bad)] [z]
#guard (Expr.mul (.const 0) bad).simp == .mul (.const 0) bad
#guard mains mul0.asserts == [bad, .const 0]
#guard agrees mul0 [0] [] [] && agrees mul0 [300] [] []
-- Not evaluated before: kept. The naive rewrite accepts x0 = 300, which the
-- original rejects.
private def mul0' := mk 1 [.bind 2 "z" (.mul (.const 0) bad)] [z]
#guard mains mul0'.asserts == [.mul (.const 0) bad]
#guard observe mul0' [300] [] [] == none
#guard observe (mk 1 [.bind 2 "z" (.const 0)] [z]) [300] [] [] == some ([0], [])

-- `e == e`: `e` is a subexpression of an asserted condition.
private def eqself := mk 2 [.assert (.select (.const 1) (.const 1) bad) "t",
  .bind 2 "e" (.eq bad bad)] [z]
#guard mains eqself.asserts == [.select (.const 1) (.const 1) bad, .const 1]
#guard agrees eqself [0] [] [] && agrees eqself [300] [] []
-- Not evaluated before: kept.
#guard mains (mk 1 [.bind 2 "e" (.eq bad bad)] [z]).asserts == [.eq bad bad]

-- `select 1 a b` with `b` a comparison whose operands are known to fit: the
-- range check of `x0` and the constant.
private def cmp := mk 2 [.constrain x (.bits 8), .assert (.eq y (.const 1)) "y",
  .bind 2 "s" (.select y x bad)] [z]
#guard mains cmp.asserts == [x, .eq y (.const 1), x]
#guard agrees cmp [3, 1] [] [] && agrees cmp [300, 1] [] [] && agrees cmp [3, 0] [] []
-- Without the range check the comparison may fail, and the conditional stays:
-- for x0 = 300 the naive rewrite (to `x0`) would accept.
private def cmp' := mk 2 [.assert (.eq y (.const 1)) "y", .bind 2 "s" (.select y x bad)] [z]
#guard mains cmp'.asserts == [.eq y (.const 1), .select (.const 1) x bad]
#guard observe cmp' [300, 1] [] [] == none
#guard observe (mk 2 [.assert (.eq y (.const 1)) "y", .bind 2 "s" x] [z]) [300, 1] [] [] ==
  some ([300], [])
-- A range check too wide to imply the comparison's width does not help.
private def cmpWide := mk 2 [.constrain x (.bits 16), .assert (.eq y (.const 1)) "y",
  .bind 2 "s" (.select y x bad)] [z]
#guard mains cmpWide.asserts == [x, .eq y (.const 1), .select (.const 1) x bad]
#guard agrees cmpWide [300, 1] [] []

-- `select c a a`: `c` has been evaluated and is 0 or 1.
private def same := mk 2 [.bind 2 "c" (.lt 8 x y), .bind 3 "s" (.select (.lt 8 x y) z z)] [.var 3]
#guard (Expr.select (.lt 8 x y) z z).simp == .select (.lt 8 x y) z z
#guard mains same.asserts == [.lt 8 x y, z]
#guard agrees same [3, 5, 7] [] [] && agrees same [300, 5, 7] [] []
-- A condition that has a value but may not be 0 or 1 is still checked.
private def same' := mk 3 [.bind 3 "c" (.add x y), .bind 4 "s" (.select (.add x y) z z)] [.var 4]
#guard mains same'.asserts == [.add x y, .select (.add x y) z z]
#guard observe same' [1, 1, 7] [] [] == none

/-! ### A contract

Compact-style code that asserts a condition and then tests it again: the
second test, and the conditional built on it, disappear. -/

ledger
  balance : Cell Uint16
  last : Cell Uint16

witness limit : Uint 8

circuit withdraw (amount : Uint16) (cap : Uint16) : Unit := do
  const amount := disclose amount
  const cap := disclose cap
  require (amount <=. cap) "over cap"
  const b ← balance.read
  -- Already known to hold.
  const r := select (amount <=. cap) amount b
  balance.write r

/-- Mirrors the `arith` circuit of `Examples/Counter.lean`: `a.sub b` asserts
    `!(a < b)`, so a later `a < b` is 0, and the comparison it guarded, whose
    operands are known to fit, need not be kept. -/
circuit reduce (a b : Uint8) : Unit := do
  const a := disclose a
  const b := disclose b
  const d := disclose (← limit)
  const m ← a.sub b
  const ok := a ==. b ||. a <. b &&. d <. 5
  require ok "nope"
  last.write m.widen

contract optAsserts

/-- Number of ZKIR instructions of the emitted circuit (0 if it cannot be emitted). -/
def size (c : Circuit) : Nat :=
  match Emit.circuit c with
  | .ok src => src.instructions.size
  | .error _ => 0

#guard size withdraw.circuit.optimizeFull < size withdraw.circuit.optimize
#guard size reduce.circuit.optimizeFull < size reduce.circuit.optimize

end Examples.OptAsserts
