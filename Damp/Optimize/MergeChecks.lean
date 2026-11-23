/-
Checks repeated under complementary guards, merged (`--O2`, `--O3`).

Compact code that checks the same thing in both branches of an `if`

    if (b) { assert(x != y, ..); .. x as Uint<16> .. }
    else   { assert(y != x, ..); .. x as Uint<16> .. }

becomes, after the branches are flattened, a pair of checks under the guard
`b` and its negation `!b` (`select b 0 1`, as the language writes it):

    assert (select b c 1)        assert (select !b c 1)
    constrain (select b x 0) r   constrain (select !b x 0) r

Together each pair says that the guard is 0 or 1 and that `c` is 1 (that `x`
passes `r`, when 0 does): `assert (select b c c)` (`constrain (select b x x)
r`), which the next `simplify` turns into `assert c` (`constrain x r`) when
`b` is known to be 0 or 1. `Circuit.mergeChecks` replaces the first check of
such a pair by the merged one and drops the second, when no statement between
them binds a variable of the second: the second then has the same value at the
first's place, and a run fails at the first place exactly when it failed at
one of the two (the run fails as a whole either way, so where does not
matter). That the guard of one is the negation of the other is read from the
bindings before the first (`Defs`): a guard variable bound to `select g 0 1`
is the negation of `g`, as long as nothing it mentions is rebound.

Measured: `assert_misc.myswitch` 128 -> 117 rows at `--O3` (two
`constrain_bits 16`, a `cond_select` and an `assert`), under the 122 rows of
size class 7. Nothing else in the benchmark has such pairs. Proved sound
(`Circuit.mergeChecks_sound`, `Damp/Proofs/Optimize/MergeChecks.lean`).
-/
import Damp.Optimize.HashRanges
import Damp.Optimize.Commute
import Damp.IR.Semantics

namespace Damp.IR

/-- Variables whose value is known to be that of an expression: `(v, e)` says
    that `v` holds the value of `e` in the current environment. -/
abbrev Defs := List (Var × Expr)

/-- `e`, or the expression a variable `e` is known to hold. -/
def Defs.resolve (D : Defs) : Expr → Expr
  | .var v => (D.lookup v).getD (.var v)
  | e => e

/-- What is still known after a statement: entries that mention a variable it
    binds are forgotten, and a binding `v := e` is recorded when `e` does not
    mention `v`. -/
def Defs.after (D : Defs) (s : Stmt) : Defs :=
  let D' := D.filter fun (v, e) => !s.binds.contains v && e.vars.all fun u => !s.binds.contains u
  match s with
  | .bind v _ e => if e.vars.contains v then D' else (v, e) :: D'
  | _ => D'

/-- Equality of ranges, as a function the proofs can unfold. -/
def Range.same : Range → Range → Bool
  | .zero, .zero | .bool, .bool => true
  | .bits n, .bits m => n == m
  | .below b w, .below b' w' => b == b' && w == w'
  | _, _ => false

/-- `g'` is known to be the negation of `g`. -/
def Defs.isNot (D : Defs) (g' g : Expr) : Bool := D.resolve g' == .select g (.const 0) (.const 1)

/-- The check that passes exactly when both `s` and `t` do, if the pass knows
    one: `s` and `t` check the same thing under complementary guards. "The
    same thing" is up to the order of operands of `+`, `*` and `==`
    (`Expr.commute`): Compact's `x != y` in one branch and `y != x` in the
    other. -/
def mergePair (D : Defs) : Stmt → Stmt → Option Stmt
  | .assert (.select g1 c1 (.const 1)) m, .assert (.select g2 c2 (.const 1)) _ =>
      if c1.commute == c2.commute && (D.isNot g1 g2 || D.isNot g2 g1) then some (.assert (.select g1 c1 c1) m) else none
  | .constrain (.select g1 x1 (.const 0)) r1, .constrain (.select g2 x2 (.const 0)) r2 =>
      if x1.commute == x2.commute && r1.same r2 && r1.holds 0 && (D.isNot g1 g2 || D.isNot g2 g1) then
        some (.constrain (.select g1 x1 x1) r1)
      else none
  | _, _ => none

/-- The variables a check reads. -/
def Stmt.checkVars : Stmt → List Var
  | .assert c _ => c.vars
  | .constrain e _ => e.vars
  | _ => []

/-- Whether a statement is a check (`assert` or `constrain`). -/
def Stmt.isCheck : Stmt → Bool
  | .assert .. | .constrain .. => true
  | _ => false

/-- A later check that merges with `s`, with nothing before it binding one of
    its variables (`bound` collects what the statements passed over bind): the
    merged check, and the statements without the partner. -/
def findPartner (D : Defs) (s : Stmt) : List Var → List Stmt → Option (Stmt × List Stmt)
  | _, [] => none
  | bound, t :: ts =>
      let later := fun (_ : Unit) => (findPartner D s (bound ++ t.binds) ts).map fun r => (r.1, t :: r.2)
      match mergePair D s t with
      | some m => if t.checkVars.all (fun v => !bound.contains v) then some (m, ts) else later ()
      | none => later ()

/-- Merge checks, first to last; `n` bounds the number of statements visited. -/
def mergeGo : Nat → Defs → List Stmt → List Stmt
  | 0, _, l => l
  | _ + 1, _, [] => []
  | n + 1, D, s :: rest =>
      if s.isCheck then
        match findPartner D s [] rest with
        | some (m, rest') => m :: mergeGo n D rest'
        | none => s :: mergeGo n D rest
      else s :: mergeGo n (D.after s) rest

/-- Merge checks repeated under complementary guards. -/
def Circuit.mergeChecks (c : Circuit) : Circuit :=
  { c with body := (mergeGo c.body.size [] c.body.toList).toArray }

end Damp.IR
