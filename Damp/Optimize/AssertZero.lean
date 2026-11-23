/-
`assert (a == b)` as `constrain (a - b) zero` (`--O2`, `--O3`).

An `assert (a == b)` is emitted as `test_eq` and `assert`; a `constrain e
zero` as one `constrain_eq e 0`, which the proof system checks with a copy
constraint and no row of its own (`bench/costs.py`: 20 `constrain_eq` add
no row; 20 `test_eq` + `assert` pairs add 60). Both pass exactly when `a` and
`b` evaluate and are equal, since `a - b = 0` exactly when `a = b` in a field,
and both fail otherwise: no knowledge about `a` or `b` is needed.

`Circuit.assertZero` rewrites the condition of every `assert` that is an
equality, and nothing else; the statement keeps its place:

* `a == k` (or `k == a`) with `k` a constant: `constrain (a + (-k)) zero`,
  the constant computed here, which the emitter writes as one
  `constrain_eq a (-k)` with no `add` (`Emit.zeroShift`; `constrain a zero`
  when `k` is 0);
* `a == b` otherwise: `constrain (a + -b) zero` (`neg` and `add`).

Measured on the benchmark (`--O3`): 26 rewrites, 70 rows, and
`adt_counter.test_all` from 123 to 111 rows, under the 122 of size class 7.
compactc keeps the comparison, so this runs at `--O2` and `--O3` only
(`Circuit.assertZero_sound` in `Damp/Proofs/Optimize/AssertZero.lean`).
-/
import Damp.IR.Semantics

namespace Damp.IR

/-- The constant `-k` in canonical form. -/
def negConst (k : Int) : Expr := .const (Int.ofNat (-(Fr.ofInt k)).val)

/-- `e - k`, written so that the emitter needs at most one `add`. -/
def subConst (e : Expr) (k : Int) : Expr :=
  if Fr.ofInt k = 0 then e else .add e (negConst k)

/-- The constant an expression is, if it is one. -/
def Expr.asConst : Expr → Option Int
  | .const k => some k
  | _ => none

/-- The expression an equality `a == b` asks to be zero. -/
def eqDiff (a b : Expr) : Expr :=
  match b.asConst with
  | some k => subConst a k
  | none =>
      match a.asConst with
      | some k => subConst b k
      | none => .add a (.neg b)

/-- An `assert` of an equality as a `constrain _ zero`. -/
def Stmt.assertZero : Stmt → Stmt
  | .assert (.eq a b) _ => .constrain (eqDiff a b) .zero
  | s => s

/-- Rewrite every `assert` of an equality. -/
def Circuit.assertZero (c : Circuit) : Circuit := { c with body := c.body.map Stmt.assertZero }

end Damp.IR
