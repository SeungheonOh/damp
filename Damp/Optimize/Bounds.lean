/-
Value-range analysis: upper bounds on field values, derived through arithmetic.

Range checks and comparisons dominate the cost of a circuit. `Circuit.simplify`
drops a range check only when the same expression was checked before; this
pass derives an upper bound on the canonical value (`Fr.val`) of an expression
from the bounds of its parts, and uses it to drop checks and fold operations
that the bound decides.

The analysis walks the statements in order, carrying `UB`: a list of upper
bounds `v ≤ B` on variables, each true of the current environment. Bounds are
learned from

* a range check `constrain (.var v) r` (kept or dropped): `v ≤ Range.ub r`;
* a binding `v := e` when `e` has a bound (`ub`);
* the results of a witness call that carry a range check (each is checked as it
  arrives, active or not; inactive results are 0, which passes every check that
  the call passes), when the call names each result once;
* `assert (lt bits (.var v) b)`: `v ≤ ub b - 1`, and
  `assert (select (lt bits a (.var v)) 0 1)` (that is, `v ≤ a`): `v ≤ ub a`.

Every statement that binds a variable first forgets what was known about it,
so the pass needs no hypothesis that variables are bound once: a bound only
ever mentions the one variable it is about. Ledger reads have no bound.

The bound of an expression (`ub`), valid whenever the expression has a value:
constants; variables from the facts; `a + b` and `a * b` when the bound of the
result is below the field modulus (no wrap-around); the larger branch of a
`select`; 1 for comparisons; for `divmod`, `ub a / 2 ^ bits` for the quotient
and `min (ub a) (2 ^ bits - 1)` for the remainder; `disclose e` as `e`. Nothing
for negation and hashes.

Rules, each with its exact side condition:

1. `constrain e r` is dropped when `e` certainly has a value (`totalB`) and its
   bound implies the check (`within`: `bits n` needs `n < 255` and
   `ub e < 2 ^ n`; `below b w` needs `w < 255`, `ub e < 2 ^ w`, `b`'s value
   `< 2 ^ w` and `ub e < b`; `bool` needs `ub e ≤ 1`; `zero` needs `ub e = 0`).
   `totalB` is `Expr.total` strengthened by the analysis: a comparison cannot
   fail when its operands cannot and both bounds fit its width (below 255
   bits), and a `select` cannot fail when its condition cannot and has bound 1.
2. Inside expressions, `divmod` by `2 ^ bits` of an `a` with `ub a < 2 ^ bits`
   and `bits ≤ 248`: the remainder is `a` itself (both fail exactly when `a`
   does); the quotient is `0`, provided also `totalB a` (otherwise kept).
3. Inside expressions, `lt bits a b` is folded to a constant when `totalB a`,
   `totalB b`, `bits < 255`, both bounds fit `bits`, and either
   `ub a < lower b` (to 1) or `lower a ≥ ub b` (to 0), where the lower bound
   `lower` is a constant's value and 0 otherwise.

Only `bind`, `assert` and `constrain` statements and the outputs are rewritten
(their expressions in place); witness and ledger statements are kept exactly as they
are, so oracle questions, `popeq` results and `IR.Circuit.checkLedger` are
untouched. The environment is never changed, so the rewritten circuit runs
through exactly the same states as the original: `Circuit.bounds_sound` in
`Damp/Proofs/Optimize/Bounds.lean`.

Run it after `Circuit.simplify` (which substitutes copies and constants, so
checks see the expressions they test) and run `simplify` again afterwards to
fold the constants this pass introduces.
-/
import Damp.IR.Semantics

namespace Damp.IR
namespace Bounds
open Damp.Zkir (fitsBits)

/-- Upper bounds on variables: `(v, B)` says `(env v).val ≤ B`. -/
abbrev UB := List (Var × Nat)

/-- Forget the bounds of variables that are about to be bound. -/
def forget (f : UB) (vs : List Var) : UB := f.filter fun (u, _) => !vs.contains u

/-- An upper bound on the canonical value of an expression, valid whenever the
    expression has a value. -/
def ub (f : UB) : Expr → Option Nat
  | .var v => f.lookup v
  | .const c => some (Fr.ofInt c).val
  | .add a b =>
      match ub f a, ub f b with
      | some x, some y => if x + y < Fr.modulus then some (x + y) else none
      | _, _ => none
  | .mul a b =>
      match ub f a, ub f b with
      | some x, some y => if x * y < Fr.modulus then some (x * y) else none
      | _, _ => none
  | .select _ a b =>
      match ub f a, ub f b with
      | some x, some y => some (max x y)
      | _, _ => none
  | .lt .. | .eq .. => some 1
  | .divmod true bits a => (ub f a).map (· / 2 ^ bits)
  | .divmod false bits a =>
      match ub f a with
      | some x => some (min x (2 ^ bits - 1))
      | none => some (2 ^ bits - 1)
  | .disclose e => ub f e
  | _ => none

/-- A lower bound on the canonical value of an expression: a constant's value, 0 otherwise. -/
def lower : Expr → Nat
  | .const c => (Fr.ofInt c).val
  | .disclose e => lower e
  | _ => 0

/-- The expression's bound is below `2 ^ bits`. -/
def fits (f : UB) (bits : Nat) (e : Expr) : Bool :=
  match ub f e with
  | some x => decide (x < 2 ^ bits)
  | none => false

/-- The expression's bound is at most 1. -/
def isBit (f : UB) (e : Expr) : Bool :=
  match ub f e with
  | some x => decide (x ≤ 1)
  | none => false

mutual
/-- Whether an expression certainly has a value, given the bounds: `Expr.total`
    with comparisons whose operands fit and conditionals whose condition is
    known to be 0 or 1. -/
def totalB (f : UB) : Expr → Bool
  | .var _ | .const _ => true
  | .add a b | .mul a b | .eq a b => totalB f a && totalB f b
  | .neg a | .disclose a => totalB f a
  | .divmod _ bits a => decide (bits ≤ 248) && totalB f a
  | .select c a b => isBit f c && totalB f c && totalB f a && totalB f b
  | .lt bits a b => decide (bits < 255) && fits f bits a && fits f bits b && totalB f a && totalB f b
  | .hash xs => totalBList f xs
  | .phash .. | .invalid _ => false
/-- Every expression in the list is `totalB`. -/
def totalBList (f : UB) : List Expr → Bool
  | [] => true
  | x :: xs => totalB f x && totalBList f xs
end

/-- The value of `lt bits a b` when the bounds decide it and it cannot fail. -/
def decideLt (f : UB) (bits : Nat) (a b : Expr) : Option Bool :=
  if decide (bits < 255) && fits f bits a && fits f bits b && totalB f a && totalB f b then
    match ub f a, ub f b with
    | some x, some y =>
        if x < lower b then some true
        else if y ≤ lower a then some false
        else none
    | _, _ => none
  else none

/-- Rewrite an expression with what the bounds decide (rules 2 and 3). Hashes
    are left as they are. -/
def tighten (f : UB) : Expr → Expr
  | .add a b => .add (tighten f a) (tighten f b)
  | .mul a b => .mul (tighten f a) (tighten f b)
  | .neg a => .neg (tighten f a)
  | .eq a b => .eq (tighten f a) (tighten f b)
  | .select c a b => .select (tighten f c) (tighten f a) (tighten f b)
  | .disclose e => .disclose (tighten f e)
  | .lt bits a b =>
      match decideLt f bits a b with
      | some true => .const 1
      | some false => .const 0
      | none => .lt bits (tighten f a) (tighten f b)
  | .divmod quot bits a =>
      if decide (bits ≤ 248) && fits f bits a then
        if quot then
          if totalB f a then .const 0 else .divmod quot bits (tighten f a)
        else tighten f a
      else .divmod quot bits (tighten f a)
  | e => e

/-- An upper bound on every value passing the range check. -/
def Range.ub : Range → Nat
  | .zero => 0
  | .bool => 1
  | .bits n => 2 ^ n - 1
  | .below b _ => (Fr.ofInt (b : Int)).val - 1

/-- Whether every value at most `x` passes the range check, as `Range.holds`
    decides it. -/
def within (x : Nat) : Range → Bool
  | .zero => x == 0
  | .bool => decide (x ≤ 1)
  | .bits n => decide (n < 255) && decide (x < 2 ^ n)
  | .below b w =>
      decide (w < 255) && decide (x < 2 ^ w) && decide ((Fr.ofInt (b : Int)).val < 2 ^ w) &&
        decide (x < (Fr.ofInt (b : Int)).val)

/-- Record a bound for `v`, if there is one. -/
def learn (f : UB) (v : Var) : Option Nat → UB
  | some x => (v, x) :: f
  | none => f

/-- What a passing `assert c` says about a variable's bound. -/
def assertFacts (f : UB) : Expr → UB
  | .lt _ (.var v) b => learn f v ((ub f b).map (· - 1))
  | .select (.lt _ a (.var v)) (.const 0) (.const 1) => learn f v (ub f a)
  | _ => f

/-- The bounds of the results of a witness call, from their range checks, when
    each result is named once. -/
def witnessBounds (outs : List (Var × Option Range)) : UB :=
  if (outs.map (·.1)).Nodup then outs.filterMap fun (v, r) => r.map fun r => (v, Range.ub r)
  else []

/-- The bounds after a range check of `e` passes. -/
def constrainFacts (f : UB) (e : Expr) (r : Range) : UB :=
  match e with
  | .var v => (v, Range.ub r) :: f
  | _ => f

/-- Rule 1: the range check of `e` certainly passes. -/
def implied (f : UB) (e : Expr) (r : Range) : Bool :=
  totalB f e && (match ub f e with | some x => within x r | none => false)

/-- Rewrite one statement: the statements replacing it and the bounds after it. -/
def stmt (f : UB) : Stmt → List Stmt × UB
  | .bind v hint e => ([.bind v hint (tighten f e)], learn (forget f [v]) v (ub f e))
  | .assert c msg => ([.assert (tighten f c) msg], assertFacts f c)
  | .constrain e r =>
      if implied f e r then
        ([], constrainFacts f e r)
      else ([.constrain (tighten f e) r], constrainFacts f e r)
  | .witness g name args outs shape =>
      ([.witness g name args outs shape], witnessBounds outs ++ forget f (outs.map (·.1)))
  | .ledger g reads ops => ([.ledger g reads ops], forget f reads)

/-- Rewrite a list of statements in order. -/
def stmts (f : UB) : List Stmt → List Stmt
  | [] => []
  | s :: rest => (stmt f s).1 ++ stmts (stmt f s).2 rest

/-- The bounds known after a list of statements. -/
def final (f : UB) : List Stmt → UB
  | [] => f
  | s :: rest => final (stmt f s).2 rest

end Bounds

/-- Value-range analysis: drop range checks implied by derived upper bounds,
    and fold `divmod` and comparisons that the bounds decide, in the body and
    in the outputs (with the bounds known at the end). -/
def Circuit.bounds (c : Circuit) : Circuit :=
  { c with body := (Bounds.stmts [] c.body.toList).toArray,
           outputs := c.outputs.map (Bounds.tighten (Bounds.final [] c.body.toList)) }

end Damp.IR
