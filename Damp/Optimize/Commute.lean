/-
Canonical operand order for commutative operations.

`x + y` and `y + x` (also `*` and `==`) have the same value and fail together,
but the emitter shares only syntactically equal expressions, so a circuit that
computes both pays twice (`x != y` in one branch and `y != x` in the other:
two `test_eq`s). `Expr.commute` rewrites an expression bottom up and puts the
two operands of every `add`, `mul` and `eq` in a canonical order: by a
structural hash (`Expr.commuteK` returns it with the expression; it is
invariant under the reordering, so equal-up-to-commutation subexpressions get
equal keys). A tie leaves the order as written. The order is a heuristic only;
the rewrite is exact whatever it decides (`Expr.commute_eval`).

`Circuit.commuteOpt` applies it to every expression of a circuit
(`Circuit.mapExprs`) and keeps the result only when the emitted circuit has
strictly fewer instructions, so a circuit with nothing to share is left
exactly as it was. `--O2` and `--O3` only.
-/
import Damp.Optimize.Forward

namespace Damp.IR

/-- Order two operands with their keys; the key of the result does not depend
    on the order they came in. -/
def commuteNode (tag : UInt64) (mk : Expr → Expr → Expr) (a : Expr × UInt64) (b : Expr × UInt64) :
    Expr × UInt64 :=
  if b.2 < a.2 then (mk b.1 a.1, mixHash tag (mixHash b.2 a.2))
  else (mk a.1 b.1, mixHash tag (mixHash a.2 b.2))

mutual
/-- `e` with the operands of every `add`, `mul` and `eq` in canonical order,
    and its key. -/
def Expr.commuteK : Expr → Expr × UInt64
  | .add a b => commuteNode 3 .add a.commuteK b.commuteK
  | .mul a b => commuteNode 4 .mul a.commuteK b.commuteK
  | .eq a b => commuteNode 5 .eq a.commuteK b.commuteK
  | .neg a =>
      let a' := a.commuteK
      (.neg a'.1, mixHash 6 a'.2)
  | .lt bits a b =>
      let a' := a.commuteK
      let b' := b.commuteK
      (.lt bits a'.1 b'.1, mixHash 7 (mixHash (Hashable.hash bits) (mixHash a'.2 b'.2)))
  | .select c a b =>
      let c' := c.commuteK
      let a' := a.commuteK
      let b' := b.commuteK
      (.select c'.1 a'.1 b'.1, mixHash 8 (mixHash c'.2 (mixHash a'.2 b'.2)))
  | .divmod quot bits a =>
      let a' := a.commuteK
      (.divmod quot bits a'.1, mixHash 9 (mixHash (Hashable.hash (quot, bits)) a'.2))
  | .hash xs =>
      let xs' := Expr.commuteKList xs
      (.hash xs'.1, mixHash 10 xs'.2)
  | .phash high align xs =>
      let xs' := Expr.commuteKList xs
      (.phash high align xs'.1, mixHash 11 (mixHash (Hashable.hash (high, align.length)) xs'.2))
  | .disclose a =>
      let a' := a.commuteK
      (.disclose a'.1, mixHash 12 a'.2)
  | .var v => (.var v, mixHash 1 (Hashable.hash v))
  | .const c => (.const c, mixHash 2 (Hashable.hash c))
  | .invalid msg => (.invalid msg, mixHash 13 (Hashable.hash msg))
def Expr.commuteKList : List Expr → List Expr × UInt64
  | [] => ([], 14)
  | x :: xs =>
      let x' := x.commuteK
      let xs' := Expr.commuteKList xs
      (x'.1 :: xs'.1, mixHash x'.2 xs'.2)
end

/-- `e` with the operands of every `add`, `mul` and `eq` in canonical order. -/
def Expr.commute (e : Expr) : Expr := e.commuteK.1

/-- Canonical operand order everywhere, kept only when the emitted circuit is
    strictly smaller. -/
def Circuit.commuteOpt : Pass :=
  Pass.choose (Circuit.mapExprs Expr.commute) (fun c => c) Circuit.emitsSmaller

end Damp.IR
