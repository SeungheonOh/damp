/-
Value-range analysis with the facts `b ≤ a` that checked subtractions assert.

`Circuit.bounds` (`Damp/Optimize/Bounds.lean`) tracks upper bounds of single
variables, so the result of `a.sub b` has none: `Uint.sub` emits
`assert (select (lt n a b) 0 1)` (that is, `¬ a < b`) and then the value
`a + -b`, or, under a guard `g`, `assert (select g (select (lt n a b) 0 1) 1)`
and `select g (a + -b) 0`. A negation has no bound, so neither does the
difference, and a range check of it later is kept.

`Circuit.bounds2` is `Circuit.bounds` with one more kind of fact, carried
along the statements next to the bounds of variables:

* `(g, a, b)`: whenever `g` has the value 1 and `a` and `b` have values,
  `b ≤ a` (canonical values). Learned from a passing `assert` of either shape
  above (`g` is the constant 1 for the unguarded one). Sound with no side
  condition: the comparison had a value, so its operands had values, and it
  was 0. A fact is forgotten when a statement binds any variable it mentions.

and two more rules for the bound of an expression (`ub2`), used where
`bounds` uses `ub` to learn the bound of a bound variable and to decide
whether a range check is implied:

* `a + -b` with the fact `(1, a, b)`: at most `ub a` (no wrap-around: the
  value is `a - b ≥ 0`);
* `select g (a + -b) d` with the fact `(g, a, b)`: at most `max (ub a) (ub d)`
  (if `g` is 1 the value is `a - b`, otherwise `d`).

Otherwise `ub2` is `ub`. Everything else is exactly `Circuit.bounds`: same
statements kept (a range check is dropped when the bound from `ub2` implies
it, which includes every check `bounds` drops), same rewriting of expressions
(`Bounds.tighten`, with the variable bounds), so `bounds2` subsumes `bounds`.
Proved sound in `Damp/Proofs/Optimize/Bounds2.lean`.
-/
import Damp.Optimize.Bounds

namespace Damp.IR
namespace Bounds2
open Bounds

/-- Relational facts: `(g, a, b)` says `b ≤ a` whenever `g` is 1. -/
abbrev Rel := List (Expr × Expr × Expr)

/-- Forget the facts that mention a variable about to be bound. -/
def forgetRel (R : Rel) (vs : List Var) : Rel :=
  R.filter fun q => !((q.1.vars ++ q.2.1.vars ++ q.2.2.vars).any vs.contains)

/-- What a passing `assert c` says about the order of two values. -/
def assertRel (R : Rel) : Expr → Rel
  | .select (.lt _ a b) (.const 0) (.const 1) => (.const 1, a, b) :: R
  | .select g (.select (.lt _ a b) (.const 0) (.const 1)) (.const 1) => (g, a, b) :: R
  | _ => R

/-- An upper bound on the canonical value of an expression, using the facts. -/
def ub2 (f : UB) (R : Rel) (e : Expr) : Option Nat :=
  match e with
  | .add a (.neg b) => if R.contains (.const 1, a, b) then ub f a else ub f e
  | .select g (.add a (.neg b)) d =>
      if R.contains (g, a, b) then
        match ub f a, ub f d with
        | some x, some y => some (max x y)
        | _, _ => ub f e
      else ub f e
  | _ => ub f e

/-- The range check of `e` certainly passes. -/
def implied2 (f : UB) (R : Rel) (e : Expr) (r : Range) : Bool :=
  totalB f e && (match ub2 f R e with | some x => within x r | none => false)

/-- Rewrite one statement: the statements replacing it, the bounds and the
    facts after it. -/
def stmt (f : UB) (R : Rel) (st : Stmt) : List Stmt × UB × Rel :=
  match st with
  | .bind v hint e => ([.bind v hint (tighten f e)], learn (forget f [v]) v (ub2 f R e), forgetRel R [v])
  | .assert c _ => ((Bounds.stmt f st).1, (Bounds.stmt f st).2, assertRel R c)
  | .constrain e r =>
      (if implied2 f R e r then [] else (Bounds.stmt f st).1, (Bounds.stmt f st).2, R)
  | .witness _ _ _ outs _ => ((Bounds.stmt f st).1, (Bounds.stmt f st).2, forgetRel R (outs.map (·.1)))
  | .ledger _ reads _ => ((Bounds.stmt f st).1, (Bounds.stmt f st).2, forgetRel R reads)

/-- Rewrite a list of statements in order; with the bounds known at the end. -/
def stmts (f : UB) (R : Rel) : List Stmt → List Stmt × UB
  | [] => ([], f)
  | s :: rest =>
      let r := stmt f R s
      let q := stmts r.2.1 r.2.2 rest
      (r.1 ++ q.1, q.2)

end Bounds2

/-- `Circuit.bounds` with the facts `b ≤ a` asserted by checked subtractions
    (see the header). -/
def Circuit.bounds2 (c : Circuit) : Circuit :=
  let r := Bounds2.stmts [] [] c.body.toList
  { c with body := r.1.toArray, outputs := c.outputs.map (Bounds.tighten r.2) }

end Damp.IR
