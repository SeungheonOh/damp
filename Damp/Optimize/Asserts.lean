/-
Learning from what a circuit has already established.

`Circuit.asserts` walks the statements in order, carrying facts about the
current environment, and rewrites each expression with them. It never adds,
removes or renames a binding: it rewrites expressions in place and drops
`assert`s that are known to pass, so the original and the rewritten circuit
run through exactly the same environments. The proof
(`Damp/Proofs/Optimize/Asserts.lean`) is therefore an equality of runs.

The facts (`Asserts.Known`):

* `eqs`: pairs `(e, r)` such that `e` has a value and `r` has the same value,
  where `r` is a constant. They come from asserted conditions: after
  `assert c` passes, `c` has the value 1, and `Known.assumeConst` records that
  and takes it apart:
  - `select c a b` has the value `k`, and the branch `b` (resp. `a`) is a
    constant other than `k`: then `c` is 1 and `a` is `k` (resp. `c` is 0 and
    `b` is `k`). This covers the conjunctions (`select a b 0`) and negations
    (`select a 0 1`) the surface language builds. No side condition: the
    `select` had a value, so its condition was 0 or 1 and both branches had
    values.
  - `eq a b` has the value 1: `a` and `b` have the same value. When one side
    is a constant, the other is that constant (taken apart again). Equalities
    of two non-constant sides are not used for substitution: replacing one
    variable by another never shrinks the emitted circuit and only renames
    operands (it changed four Tokens circuits without saving anything).
* `evald`: expressions known to have a value: the bodies of bindings, the
  conditions of asserts, the subjects of range checks and the guards of
  witness and ledger statements, each evaluated (before the statement's
  variables are bound) by any run that gets past the statement. Every
  subexpression of an expression that has a value has one too (both branches
  of a `select` are evaluated), so `Known.evals` also looks inside.
* `ranged`: expressions known to have a value passing a range check (range
  check subjects, and witness results as `witnessChecks` records them), so
  that a comparison `lt n a b` is known to have a value when `a` and `b` do and
  are known to fit in `n` bits.

A fact mentions variables of the current environment, so when a statement
binds variables every fact mentioning one is dropped (`Known.forget`). There
is no single-assignment assumption and nothing to give up on.

The rewrite (`Known.rw`) is one top-down pass: a subexpression equal to the
left side of a fact (compared with `disclose` markers removed) is replaced by
its right side, a constant, so the circuit never grows. On the way back up,
these rules use what is known to have a value (`Known.evals`), where
`Circuit.simplify` would need the dropped part to be `total`:

* `select 1 a b` is `a` when `b` is known to have a value (`select 0 a b` is
  `b` when `a` is);
* `0 * e` and `e * 0` are `0` when `e` is known to have a value;
* `eq e e` is `1` when `e` is known to have a value;
* `select c a a` is `a` when `c` is known to have a value and `c.isBool []`.

Statements: an `assert` whose rewritten condition is the constant 1 is
dropped (a duplicate, or one implied by earlier ones); guards, arguments of
witness calls, bodies, conditions and range check subjects are rewritten, so
a statement guarded by an asserted condition gets the guard 1, and one guarded
by an asserted negation the guard 0 (which `Circuit.simplify` then drops).
The operands of ledger instructions are left alone (they are evaluated both
before and after the reads are bound, and the `popeq` results must stay plain
read variables), so `checkLedger` is preserved trivially; only a ledger
statement's guard is rewritten. Run `Circuit.simplify` afterwards to fold what
the rewrite exposes.
-/
import Damp.Optimize.Simplify

namespace Damp.IR
namespace Asserts

/-! ## Expressions without disclosure markers -/

mutual
/-- Drop the `disclose` markers. The disclosure check has already run. -/
def strip : Expr → Expr
  | .disclose e => strip e
  | .add a b => .add (strip a) (strip b)
  | .mul a b => .mul (strip a) (strip b)
  | .neg a => .neg (strip a)
  | .lt n a b => .lt n (strip a) (strip b)
  | .eq a b => .eq (strip a) (strip b)
  | .select c a b => .select (strip c) (strip a) (strip b)
  | .divmod q n a => .divmod q n (strip a)
  | .hash xs => .hash (stripList xs)
  | .phash h al xs => .phash h al (stripList xs)
  | .var v => .var v
  | .const c => .const c
  | .invalid m => .invalid m
/-- `strip` on each element. -/
def stripList : List Expr → List Expr
  | [] => []
  | x :: xs => strip x :: stripList xs
end

mutual
/-- Whether `s` is a subexpression of an expression (or the expression itself). -/
def hasSub : Expr → Expr → Bool
  | .var v, s => Expr.var v == s
  | .const c, s => Expr.const c == s
  | .invalid m, s => Expr.invalid m == s
  | .disclose a, s => Expr.disclose a == s || hasSub a s
  | .add a b, s => Expr.add a b == s || hasSub a s || hasSub b s
  | .mul a b, s => Expr.mul a b == s || hasSub a s || hasSub b s
  | .neg a, s => Expr.neg a == s || hasSub a s
  | .lt n a b, s => Expr.lt n a b == s || hasSub a s || hasSub b s
  | .eq a b, s => Expr.eq a b == s || hasSub a s || hasSub b s
  | .select c a b, s => Expr.select c a b == s || hasSub c s || hasSub a s || hasSub b s
  | .divmod q n a, s => Expr.divmod q n a == s || hasSub a s
  | .hash xs, s => Expr.hash xs == s || hasSubList xs s
  | .phash h al xs, s => Expr.phash h al xs == s || hasSubList xs s
/-- `hasSub` for some element of a list. -/
def hasSubList : List Expr → Expr → Bool
  | [], _ => false
  | x :: xs, s => hasSub x s || hasSubList xs s
end

/-! ## Facts -/

/-- What is known at a point of the circuit, about the current environment. -/
structure Known where
  /-- `(e, r)`: `e` has a value, and `r` has the same one. `r` is a constant. -/
  eqs : List (Expr × Expr) := []
  /-- Expressions known to have a value. -/
  evald : List Expr := []
  /-- Expressions known to have a value that passes the range check. -/
  ranged : List (Expr × Range) := []

namespace Known

/-- The replacement known for an expression, if any. -/
def lookup (K : Known) (e : Expr) : Option Expr := (K.eqs.find? fun q => q.1 == e).map (·.2)

/-- Whether `e` occurs in an expression known to have a value. -/
def seen (K : Known) (e : Expr) : Bool :=
  K.evald.any (hasSub · e) || K.eqs.any (hasSub ·.1 e)

/-- Whether `e` is known to fit in `n` bits: a constant that does, or an
    expression that passed a range check implying it. -/
def fits (K : Known) (n : Nat) : Expr → Bool
  | .const k => Zkir.fitsBits (Fr.ofInt k) n
  | e => K.ranged.any fun q => q.1 == e && q.2.implies (.bits n)

/-- Whether `e` is known to have a value: it occurs in an expression that has
    one, or it is built from such expressions by operations that cannot fail. -/
def evals (K : Known) : Expr → Bool
  | .var _ | .const _ => true
  | .add a b => K.seen (.add a b) || (K.evals a && K.evals b)
  | .mul a b => K.seen (.mul a b) || (K.evals a && K.evals b)
  | .eq a b => K.seen (.eq a b) || (K.evals a && K.evals b)
  | .neg a => K.seen (.neg a) || K.evals a
  | .disclose a => K.seen (.disclose a) || K.evals a
  | .divmod q n a => K.seen (.divmod q n a) || (decide (n ≤ 248) && K.evals a)
  | .select c a b => K.seen (.select c a b) || (c.isBool [] && K.evals c && K.evals a && K.evals b)
  | .hash xs => K.seen (.hash xs) || Expr.totalList [] xs
  | .lt n a b => K.seen (.lt n a b) || (K.evals a && K.evals b && K.fits n a && K.fits n b)
  | e => K.seen e

/-- Whether a constant is the field element 1 (resp. 0). -/
def isOne : Expr → Bool
  | .const k => decide (Fr.ofInt k = 1)
  | _ => false

def isZero : Expr → Bool
  | .const k => decide (Fr.ofInt k = 0)
  | _ => false

/-- `a * b`, with a factor 0 absorbing a factor known to have a value. `ea` and
    `eb` say whether `a` and `b` are known to have values. -/
def mkMul (a b : Expr) (ea eb : Bool) : Expr :=
  if isZero a && eb then .const 0
  else if isZero b && ea then .const 0
  else .mul a b

/-- `a == b`, which is 1 when both sides are the same expression known to have a value. -/
def mkEq (a b : Expr) (ea : Bool) : Expr :=
  if a == b && ea then .const 1 else .eq a b

/-- `select c a b` with a known condition, or equal branches, when what is
    dropped is known to have a value. -/
def mkSel (c a b : Expr) (ec ea eb : Bool) : Expr :=
  if isOne c && eb then a
  else if isZero c && ea then b
  else if a == b && ec && c.isBool [] then a
  else .select c a b

mutual
/-- Rewrite an expression without `disclose` markers with what is known. -/
def rwS (K : Known) (e : Expr) : Expr :=
  match K.lookup e with
  | some r => r
  | none =>
    match e with
    | .add a b => .add (K.rwS a) (K.rwS b)
    | .mul a b =>
        let a' := K.rwS a
        let b' := K.rwS b
        mkMul a' b' (K.evals a || K.evals a') (K.evals b || K.evals b')
    | .neg a => .neg (K.rwS a)
    | .lt n a b => .lt n (K.rwS a) (K.rwS b)
    | .eq a b =>
        let a' := K.rwS a
        mkEq a' (K.rwS b) (K.evals a || K.evals a')
    | .select c a b =>
        let c' := K.rwS c
        let a' := K.rwS a
        let b' := K.rwS b
        mkSel c' a' b' (K.evals c || K.evals c') (K.evals a || K.evals a') (K.evals b || K.evals b')
    | .divmod q n a => .divmod q n (K.rwS a)
    | .hash xs => .hash (K.rwSList xs)
    | .phash h al xs => .phash h al (K.rwSList xs)
    | .disclose a => .disclose (K.rwS a)
    | .var v => .var v
    | .const c => .const c
    | .invalid m => .invalid m
/-- `rwS` on each element. -/
def rwSList (K : Known) : List Expr → List Expr
  | [] => []
  | x :: xs => K.rwS x :: K.rwSList xs
end

/-- Rewrite an expression with what is known. -/
def rw (K : Known) (e : Expr) : Expr := K.rwS (strip e)

/-- The integer of a constant. -/
def constVal? : Expr → Option Int
  | .const k => some k
  | _ => none

/-- Whether an expression is a constant whose value is not `k`'s. -/
def constOther (e : Expr) (k : Int) : Bool :=
  match e with
  | .const j => decide (Fr.ofInt j ≠ Fr.ofInt k)
  | _ => false

/-- What is known once `e` is known to have the value `k`: that, and what
    follows from it. -/
def assumeConst (K : Known) : Expr → Int → Known
  | .select c a b, k =>
      let K := { K with eqs := (.select c a b, .const k) :: K.eqs }
      -- The other branch would not give `k`, so this one was taken.
      if constOther b k then (K.assumeConst c 1).assumeConst a k
      else if constOther a k then (K.assumeConst c 0).assumeConst b k
      else K
  | .eq a b, k =>
      let K := { K with eqs := (.eq a b, .const k) :: K.eqs }
      if Fr.ofInt k = 1 then
        match constVal? b, constVal? a with
        | some kb, _ => K.assumeConst a kb
        | none, some ka => K.assumeConst b ka
        | none, none => K
      else K
  | e, k => { K with eqs := (e, .const k) :: K.eqs }

/-- Forget every fact that mentions one of these variables, which are about to
    be bound. -/
def forget (K : Known) (vs : List Var) : Known where
  eqs := K.eqs.filter fun q => (q.1.vars ++ q.2.vars).all (!vs.contains ·)
  evald := K.evald.filter fun e => e.vars.all (!vs.contains ·)
  ranged := K.ranged.filter fun q => q.1.vars.all (!vs.contains ·)

/-- After a statement that evaluated `es` and then bound `vs`. -/
def after (K : Known) (es : List Expr) (vs : List Var) : Known :=
  ({ K with evald := es ++ K.evald } : Known).forget vs

/-- Rewrite one statement: what replaces it, and what is known after it. -/
def stmt (K : Known) : Stmt → List Stmt × Known
  | .bind v hint e =>
      let e' := K.rw e
      ([.bind v hint e'], K.after [strip e, e'] [v])
  | .assert c msg =>
      let c' := K.rw c
      if isOne c' then ([], K)
      else ([.assert c' msg], (K.assumeConst (strip c) 1).assumeConst c' 1)
  | .constrain e r =>
      let e' := K.rw e
      let K1 := K.after [strip e, e'] []
      ([.constrain e' r], { K1 with ranged := (strip e, r) :: (e', r) :: K1.ranged })
  | .witness g name args outs shape =>
      let g' := K.rw g
      let K1 := K.after [strip g, g'] (outs.map (·.1))
      ([.witness g' name (args.map K.rw) outs shape],
        { K1 with ranged := witnessChecks outs ++ K1.ranged })
  | .ledger g reads ops =>
      let g' := K.rw g
      ([.ledger g' reads ops], K.after [strip g, g'] reads)

/-- Rewrite a list of statements in order. -/
def stmts (K : Known) : List Stmt → List Stmt × Known
  | [] => ([], K)
  | s :: rest =>
      let r1 := K.stmt s
      let r2 := r1.2.stmts rest
      (r1.1 ++ r2.1, r2.2)

end Known
end Asserts

/-- Learn from asserts and from what has been evaluated (see the header). -/
def Circuit.asserts (c : Circuit) : Circuit :=
  let r := Asserts.Known.stmts {} c.body.toList
  { c with body := r.1.toArray, outputs := c.outputs.map r.2.rw }

end Damp.IR
