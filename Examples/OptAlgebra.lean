import Damp
import Damp.Optimize.Algebra

/-! Checks on the algebra pass (`Circuit.algebra`), run by the build.

The pass is proved sound in `Damp/Proofs/Optimize/Algebra.lean`
(`Circuit.algebra_sound`). These checks pin down which rewrites fire, and show
for each side condition a run on which the rewrite without it would change the
result. -/
namespace Examples.OptAlgebra
open Damp Damp.IR

private def x : Expr := .var 0
private def y : Expr := .var 1
/-- Fails unless both sides fit in 8 bits. -/
private def bad : Expr := .lt 8 x y

def prims : Zkir.Prims where
  transientHash xs := xs.foldl (· + ·) 0
  persistentHash _ xs := some (List.replicate 32 (xs.length % 256))
  transientCommit xs r := xs.foldl (· + ·) r

/-- `x = 300`, `y = 2`: `bad` fails, `x` is not 0 or 1. -/
private def env300 : Env := fun v => if v = 0 then 300 else 2
/-- `x = 1`, `y = 2`. -/
private def env12 : Env := fun v => if v = 0 then 1 else 2
/-- `x = 2`, `y = 1`. -/
private def env2 : Env := fun v => if v = 0 then 2 else 1

/-! ### Linear normalization -/

#guard (Expr.add (.add x (.const 3)) (.const 4)).algebra == .add x (.const 7)
#guard (Expr.add (.add x x) x).algebra == .mul (.const 3) x
#guard (Expr.mul (.const 2) (.mul (.const 3) x)).algebra == .mul (.const 6) x
-- `(x - y) + y` is `x`: `y` cannot fail, so it may go.
#guard (Expr.add (.add x (.neg y)) y).algebra == x
-- `-(x + y) + x` is `-y`.
#guard (Expr.add (.neg (.add x y)) x).algebra == .neg y
-- `2·(x + 1) - 2` is `2·x`.
#guard (Expr.add (.mul (.const 2) (.add x (.const 1))) (.neg (.const 2))).algebra == .mul (.const 2) x
-- No smaller form, so nothing changes: `x + x` (`2·x` is one instruction too),
-- `-(x + y)` (`-x + -y` is three), `x - y`.
#guard (Expr.add x x).algebra == .add x x
#guard (Expr.neg (.add x y)).algebra == .neg (.add x y)
#guard (Expr.add x (.neg y)).algebra == .add x (.neg y)

-- A cancelled atom that can fail is kept, multiplied by 0: `(x - bad) + bad`
-- is not `x`, which would succeed where the original fails.
#guard (Expr.add (.add x (.neg bad)) bad).algebra == .add x (.mul (.const 0) bad)
#guard (Expr.add (.add x (.neg bad)) bad).eval prims env300 == none
#guard x.eval prims env300 == some 300
#guard (Expr.add x (.mul (.const 0) bad)).eval prims env300 == none

-- The whole expression is rewritten only if that removes instructions once
-- shared subexpressions are counted once. Here the long branch alone shrinks
-- (5 to 4), but it shares 3 instructions with the short one as written; after
-- the rewrite it would share none, so it is left alone.
private def short : Expr := .add (.add x (.mul y (.const 2))) (.var 2)
private def long : Expr := .add (.add short x) x
#guard (Expr.select (.var 3) long short).alg != .select (.var 3) long short
#guard (Expr.select (.var 3) long short).algebra == .select (.var 3) long short

/-! ### Comparisons -/

#guard (Expr.eq (.add x (.const 3)) (.const 10)).algebra == .eq x (.const 7)
#guard (Expr.eq (.const 10) (.add x (.const 3))).algebra == .eq (.const 7) x
#guard (Expr.eq (.neg x) (.neg y)).algebra == .eq x y
#guard (Expr.eq (.mul (.const 3) x) (.const 6)).algebra == .eq x (.const 2)
#guard (Expr.eq (.mul x (.const 3)) (.const 0)).algebra == .eq x (.const 0)
-- Normalization first, then the comparison: `(x + 3) + 4 == 9` is `x == 2`.
#guard (Expr.eq (.add (.add x (.const 3)) (.const 4)) (.const 9)).algebra == .eq x (.const 2)
-- `0` has no inverse: `0·bad == 0` is 1 whenever `bad` has a value, `bad == 0`
-- is not (for `x = 1`, `y = 2`, `bad` is 1).
#guard (Expr.eq (.mul (.const 0) bad) (.const 0)).algebra == .eq (.mul (.const 0) bad) (.const 0)
#guard (Expr.eq (.mul (.const 0) bad) (.const 0)).eval prims env12 == some 1
#guard (Expr.eq bad (.const 0)).eval prims env12 == some 0
-- (With a variable, `0·x` is first normalized to `0`: `x` cannot fail.)
#guard (Expr.eq (.mul (.const 0) x) (.const 0)).algebra == .eq (.const 0) (.const 0)
-- `e == 1` is `e` when `e` is certainly 0 or 1 ...
#guard (Expr.eq bad (.const 1)).algebra == bad
#guard (Expr.eq (.const 1) (.eq x y)).algebra == .eq x y
-- ... and not otherwise: for `x = 2`, `x == 1` is 0.
#guard (Expr.eq x (.const 1)).algebra == .eq x (.const 1)
#guard (Expr.eq x (.const 1)).eval prims env2 == some 0
#guard x.eval prims env2 == some 2

/-! ### Conditionals -/

private def c : Expr := .eq x y
-- `c && c` and `c || c` are `c` when `c` is certainly 0 or 1 ...
#guard (Expr.select c c (.const 0)).algebra == c
#guard (Expr.select c (.const 1) c).algebra == c
-- ... and not otherwise: for `x = 2` the conditional fails, `x` does not.
#guard (Expr.select x x (.const 0)).algebra == .select x x (.const 0)
#guard (Expr.select x x (.const 0)).eval prims env2 == none
#guard (Expr.select x (.const 1) x).algebra == .select x (.const 1) x

-- A conditional on the same condition inside a branch.
#guard (Expr.select c (.select c x y) (.const 5)).algebra == .select c x (.const 5)
#guard (Expr.select c (.const 5) (.select c x y)).algebra == .select c (.const 5) y
-- Not when the dropped branch can fail: for `x = 300`, `c'` holds, the inner
-- conditional fails on `bad`, and `select c' x 5` would be 300.
private def c' : Expr := .eq x (.const 300)
#guard (Expr.select c' (.select c' x bad) (.const 5)).algebra == .select c' (.select c' x bad) (.const 5)
#guard (Expr.select c' (.select c' x bad) (.const 5)).eval prims env300 == none
#guard (Expr.select c' x (.const 5)).eval prims env300 == some 300

/-! ### Whole circuits -/

/-- A circuit with inputs `0..n-1`, a body and outputs. -/
private def mk (n : Nat) (body : List Stmt) (outputs : List Expr) : Circuit where
  name := "t"
  args := []
  inputs := (List.range n).map fun v => { name := s!"x{v}", var := v, range := none }
  body := body.toArray
  result := .tuple []
  outputs := outputs

def observe (c : Circuit) (inputs priv pub : List Fr) : Option (List Nat × List (List Nat)) :=
  (c.run prims inputs priv pub).map fun o =>
    (o.outputs.map (·.val), (o.groups.filter (·.active)).map fun g => g.vals.map (·.val))

def agrees (c : Circuit) (inputs priv pub : List Fr) : Bool :=
  observe c inputs priv pub == observe (Circuit.algebra c) inputs priv pub

/-- Every kind of statement, and a ledger read: the operand of `addi` is
    rewritten, the `popeq` result stays the read variable. -/
private def whole := mk 2
  [.bind 2 "s" (.add (.add x (.const 3)) (.const 4)),
   .assert (.eq (.add (.var 2) (.const 1)) (.const 10)) "two",
   .constrain (.add (.add y y) y) (.bits 8),
   .witness (.const 1) "w" [.add (.add x (.neg y)) y] [] (.prim .field),
   .ledger (.const 1) [5] [.addi (.add (.add x (.const 1)) (.const 2)), .popeq false [.field] [.var 5]]]
  [.add (.add (.var 5) (.const 1)) (.const 1)]

#guard (Circuit.algebra whole).body.toList.map (fun
    | .bind _ _ e => [e] | .assert e _ => [e] | .constrain e _ => [e]
    | .witness _ _ args _ _ => args | .ledger _ _ ops => ops.flatMap (·.encode Expr.const)) ==
  [[.add x (.const 7)], [.eq (.var 2) (.const 9)], [.mul (.const 3) y], [x],
   [.const 14, .add x (.const 3), .const 12, .const 1, .const (-2), .var 5]]
#guard (Circuit.algebra whole).outputs == [.add (.var 5) (.const 2)]
#guard whole.checkLedger matches .ok ()
#guard (Circuit.algebra whole).checkLedger matches .ok ()
#guard agrees whole [2, 5] [] [9]
#guard agrees whole [3, 5] [] [9]
#guard agrees whole [2, 100] [] [9]
#guard agrees whole [2, 5] [] []
#guard (observe whole [2, 5] [] [9]).isSome

/-! ### A contract: the emitted ZKIR shrinks -/

ledger
  total : Cell Field
  hits : Cell Field

circuit tally (a b : Field) : Field := do
  let s := a + 3 + 4 + a + a - b + b
  total.write (disclose s)
  hits.write (disclose (s - a))
  total.read

private def size (c : Circuit) : Nat :=
  match Emit.circuit c with
  | .ok src => src.instructions.size
  | .error _ => 0

-- Default pipeline, then the algebra pass.
#guard size tally.circuit.simplify = 20
#guard size (Circuit.algebra tally.circuit.simplify) = 15
#guard size (Circuit.algebra tally.circuit.simplify).simplify = 15
-- And it behaves the same.
#guard agrees tally.circuit.simplify [3, 4] [] [7]
#guard (observe tally.circuit.simplify [3, 4] [] [7]).isSome
#guard agrees tally.circuit.simplify [3, 4] [] []

end Examples.OptAlgebra
