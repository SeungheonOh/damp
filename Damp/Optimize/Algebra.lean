/-
Algebraic rewriting of expressions: an expression-level pass.

`Circuit.algebra` rewrites every expression of every statement (bind bodies,
assert conditions, constrained values, witness guards and arguments, ledger
guards and operands) and the outputs with `Expr.algebra`, which preserves
`Expr.eval` exactly, failures included (`Expr.algebra_eval` in
`Damp/Proofs/Optimize/Algebra.lean`). Nothing else changes: no statement is
added, dropped or reordered, so every oracle question stays where it was.

## The generic vehicle

`Circuit.mapExprs g` applies any `g : Expr → Expr` that way. It leaves
variables and constants alone whatever `g` does (`Expr.keepLeaves`), so a
`popeq` result, which a well-formed ledger statement has as a plain variable,
stays that variable. On a ledger statement it keeps the rewritten instructions
only if `ledgerProblem` finds nothing wrong with them, and otherwise keeps the
original ones, so `checkLedger` holds of the result whenever it held of the
input, for every `g` (`Circuit.mapExprs_checkLedger`). If `g` preserves
`Expr.eval`, the pass is sound (`Circuit.mapExprs_sound`); later passes of the
same kind need to prove only that.

## The rewrites (`Expr.alg`, bottom up)

* **Linear normalization.** A maximal tree of `add`, `neg` and multiplication
  by a constant is read as `k + Σ cᵢ·aᵢ` over its other subexpressions (the
  atoms, themselves rewritten). Syntactically equal atoms are combined
  (`x + x + x` is `3·x`, `x + -x` is `0·x`); a term with coefficient 0 is dropped
  only when its atom is `total []` (it cannot fail), otherwise it is kept as
  `0·a` so that its failure is kept. The result is rebuilt as
  `c₁·a₁ + (c₂·a₂ + … ) + k` with `1·a` written `a`, `-1·a` written `-a`, and no
  `+ 0`. It replaces the tree only when it has strictly fewer instructions
  (`Algebra.cost`: one per `add`, `mul`, `neg`, comparison, `select`, hash or
  `divmod`; constants and variables are free immediates), so `x + x` stays
  (`2·x` is one instruction too). Exact because
  addition and multiplication never fail, so the rewritten expression fails
  exactly when one of its atoms does, as the original does.
* **Comparisons with constants**, after the operands are rewritten:
  `(x + a) == b` becomes `x == b - a` (also with the sides swapped);
  `-x == -y` becomes `x == y`; `k·x == b` (or `x·k == b`) becomes
  `x == k⁻¹·b` when the pass finds an inverse of `k` (it checks `k·k⁻¹ = 1`,
  so `k = 0` never qualifies); `e == 1` (either side) becomes `e` when
  `e.isBool []`, since `e` is then 0 or 1 whenever it has a value.
* **Conditionals**, after the operands are rewritten:
  `select c c 0` (`c && c`) and `select c 1 c` (`c || c`) become `c` when
  `c.isBool []` (otherwise the original fails on a non-boolean `c`, and `c`
  does not); `select c (select c a b) d` becomes `select c a d` when `b` is
  `total []`, and `select c a (select c b d)` becomes `select c a d` when `b`
  is `total []` (the dropped branch must not be able to fail; the condition is
  still checked by the outer `select`).

Whole expressions: the rewritten expression is used only when it has strictly
fewer distinct instructions (`Algebra.dagCost`, which counts shared
subexpressions once, as the emitter does); otherwise the expression is left
exactly as it was. So the pass never makes an expression bigger, and does not
reshuffle expressions it cannot shrink.
-/
import Damp.Optimize.Simplify
import Damp.IR.LedgerCheck

namespace Damp.IR

/-! ## The generic vehicle: rewriting every expression -/

/-- `g`, except that variables and constants are left alone. -/
def Expr.keepLeaves (g : Expr → Expr) : Expr → Expr
  | .var v => .var v
  | .const k => .const k
  | e => g e

/-- Rewrite every expression of a statement. On a ledger statement the
    rewritten instructions are kept only when `ledgerProblem` accepts them. -/
def Stmt.mapExprs (g : Expr → Expr) : Stmt → Stmt
  | .bind v hint e => .bind v hint (g e)
  | .assert cond msg => .assert (g cond) msg
  | .constrain e r => .constrain (g e) r
  | .witness guard name args outs shape => .witness (g guard) name (args.map g) outs shape
  | .ledger guard reads ops =>
      let ops' := ops.map (·.map g)
      .ledger (g guard) reads (if (IR.ledgerProblem reads ops').isNone then ops' else ops)

/-- Rewrite every expression of a circuit: statements and outputs. -/
def Circuit.mapExprs (g : Expr → Expr) (c : Circuit) : Circuit :=
  { c with body := c.body.map (Stmt.mapExprs (Expr.keepLeaves g)),
           outputs := c.outputs.map (Expr.keepLeaves g) }

namespace Algebra

/-! ## Size -/

mutual
/-- Instructions the emitter produces for an expression, counted as a tree. -/
def cost : Expr → Nat
  | .var _ | .const _ | .invalid _ => 0
  | .disclose e => cost e
  | .add a b | .mul a b | .lt _ a b | .eq a b => cost a + cost b + 1
  | .neg a | .divmod _ _ a => cost a + 1
  | .select c a b => cost c + cost a + cost b + 1
  | .hash xs | .phash _ _ xs => costList xs + 1
def costList : List Expr → Nat
  | [] => 0
  | x :: xs => cost x + costList xs
end

mutual
/-- The subexpressions that become instructions, with repetitions. -/
def nodes : Expr → List Expr
  | .var _ | .const _ | .invalid _ => []
  | .disclose e => nodes e
  | .add a b => .add a b :: (nodes a ++ nodes b)
  | .mul a b => .mul a b :: (nodes a ++ nodes b)
  | .lt n a b => .lt n a b :: (nodes a ++ nodes b)
  | .eq a b => .eq a b :: (nodes a ++ nodes b)
  | .neg a => .neg a :: nodes a
  | .divmod q n a => .divmod q n a :: nodes a
  | .select c a b => .select c a b :: (nodes c ++ nodes a ++ nodes b)
  | .hash xs => .hash xs :: nodesList xs
  | .phash h al xs => .phash h al xs :: nodesList xs
def nodesList : List Expr → List Expr
  | [] => []
  | x :: xs => nodes x ++ nodesList xs
end

/-- Instructions the emitter produces for an expression, counting repeated
    subexpressions once (the emitter shares them). -/
def dagCost (e : Expr) : Nat := (nodes e).eraseDups.length

/-! ## Linear forms -/

/-- `k + Σ c·a` over the terms `(c, a)`. -/
structure Lin where
  k : Fr
  ts : List (Fr × Expr)

def Lin.const (c : Fr) : Lin := ⟨c, []⟩
def Lin.atom (e : Expr) : Lin := ⟨0, [(1, e)]⟩
def Lin.add (A B : Lin) : Lin := ⟨A.k + B.k, A.ts ++ B.ts⟩
def Lin.scale (c : Fr) (A : Lin) : Lin := ⟨c * A.k, A.ts.map fun t => (c * t.1, t.2)⟩

/-- Add a term, combining it with a term over the same atom if there is one;
    otherwise it goes last. -/
def insertTerm (t : Fr × Expr) : List (Fr × Expr) → List (Fr × Expr)
  | [] => [t]
  | u :: rest => if u.2 == t.2 then (u.1 + t.1, u.2) :: rest else u :: insertTerm t rest

/-- Combine the terms over equal atoms, in order of first appearance. -/
def combine (acc : List (Fr × Expr)) : List (Fr × Expr) → List (Fr × Expr)
  | [] => acc
  | t :: ts => combine (insertTerm t acc) ts

/-- A term worth keeping: coefficient not 0, or an atom that can fail. -/
def keepTerm (t : Fr × Expr) : Bool := !(t.1 == 0 && t.2.total [])

/-- `c·a` as an expression. -/
def term (t : Fr × Expr) : Expr :=
  if t.1 = 1 then t.2 else if t.1 = -1 then .neg t.2 else .mul (canon t.1) t.2

/-- The sum of the terms, right-nested; `0` for none. -/
def sumTerms : List (Fr × Expr) → Expr
  | [] => .const 0
  | [t] => term t
  | t :: ts => .add (term t) (sumTerms ts)

/-- The terms (normalized) plus the constant. -/
def mkSum (ts : List (Fr × Expr)) (k : Fr) : Expr :=
  if ts.isEmpty then canon k
  else if k = 0 then sumTerms ts
  else .add (sumTerms ts) (canon k)

/-- Rebuild a linear form as an expression. -/
def Lin.rebuild (L : Lin) : Expr := mkSum ((combine [] L.ts).filter keepTerm) L.k

/-- A linear form with the expression it came from (atoms rewritten), the
    rebuilt form if it is strictly smaller, else that expression. -/
def fin (q : Lin × Expr) : Expr :=
  let r := q.1.rebuild
  if cost r < cost q.2 then r else q.2

/-- A subexpression that is not linear: its own linear form. -/
def atomOf (e : Expr) : Lin × Expr := (Lin.atom e, e)

def linAdd (qa qb : Lin × Expr) : Lin × Expr := (qa.1.add qb.1, .add qa.2 qb.2)
def linNeg (qa : Lin × Expr) : Lin × Expr := (qa.1.scale (-1), .neg qa.2)

/-- A product is linear when one side is a constant. -/
def linMul (a b : Expr) (qa qb : Lin × Expr) : Lin × Expr :=
  match a, b with
  | .const k, _ => (qb.1.scale (Fr.ofInt k), .mul (.const k) qb.2)
  | _, .const k => (qa.1.scale (Fr.ofInt k), .mul qa.2 (.const k))
  | _, _ => atomOf (.mul (fin qa) (fin qb))

/-! ## Comparisons and conditionals -/

/-- `x ^ e` by repeated squaring, `fuel` bits of `e` at most. -/
def powFuel (x : Fr) : Nat → Nat → Fr
  | 0, _ => 1
  | fuel + 1, e =>
      if e = 0 then 1
      else
        let r := powFuel (x * x) fuel (e / 2)
        if e % 2 = 1 then x * r else r

/-- A candidate inverse (Fermat); the caller checks it. -/
def invCandidate (x : Fr) : Fr := powFuel x 256 (Fr.modulus - 2)

/-- `k · x == c` as `x == k⁻¹ · c`, when an inverse of `k` is found. -/
def eqScaled (k c : Int) (x : Expr) (orig : Expr) : Expr :=
  let i := invCandidate (Fr.ofInt k)
  if Fr.ofInt k * i = 1 then .eq x (canon (i * Fr.ofInt c)) else orig

/-- `e == 1` as `e`, for `e` certainly 0 or 1. -/
def eqOne (e : Expr) (orig : Expr) : Expr := if e.isBool [] then e else orig

/-- Equality of two rewritten operands. -/
def mkEqA (a b : Expr) : Expr :=
  match a, b with
  | .add x (.const k), .const c => .eq x (canon (Fr.ofInt c - Fr.ofInt k))
  | .const c, .add x (.const k) => .eq (canon (Fr.ofInt c - Fr.ofInt k)) x
  | .neg x, .neg y => .eq x y
  | .mul (.const k) x, .const c => eqScaled k c x (.eq a b)
  | .mul x (.const k), .const c => eqScaled k c x (.eq a b)
  | e, .const 1 => eqOne e (.eq a b)
  | .const 1, e => eqOne e (.eq a b)
  | _, _ => .eq a b

/-- `select c a b` when the else branch might restate the condition. -/
def selElse (c a b : Expr) : Expr :=
  match b with
  | .select c' b1 d => if c' == c && b1.total [] then .select c a d else .select c a b
  | _ => .select c a b

/-- A conditional of rewritten operands. -/
def mkSelectA (c a b : Expr) : Expr :=
  if a == c && b == .const 0 && c.isBool [] then c
  else if a == .const 1 && b == c && c.isBool [] then c
  else
    match a with
    | .select c' a1 b1 => if c' == c && b1.total [] then selElse c a1 b else selElse c a b
    | _ => selElse c a b

/-! ## The rewrite -/

mutual
/-- The linear form of an expression, and the expression with its atoms
    rewritten but its own linear shape kept. -/
def algL : Expr → Lin × Expr
  | .var v => atomOf (.var v)
  | .const k => (Lin.const (Fr.ofInt k), .const k)
  | .invalid m => atomOf (.invalid m)
  | .add a b => linAdd (algL a) (algL b)
  | .neg a => linNeg (algL a)
  | .mul a b => linMul a b (algL a) (algL b)
  | .lt n a b => atomOf (.lt n (fin (algL a)) (fin (algL b)))
  | .eq a b => atomOf (mkEqA (fin (algL a)) (fin (algL b)))
  | .select c a b => atomOf (mkSelectA (fin (algL c)) (fin (algL a)) (fin (algL b)))
  | .divmod q n a => atomOf (.divmod q n (fin (algL a)))
  | .hash xs => atomOf (.hash (algList xs))
  | .phash h al xs => atomOf (.phash h al (algList xs))
  | .disclose e => atomOf (.disclose (fin (algL e)))
def algList : List Expr → List Expr
  | [] => []
  | x :: xs => fin (algL x) :: algList xs
end

end Algebra

/-- Rewrite an expression (see the header), bottom up. -/
def Expr.alg (e : Expr) : Expr := Algebra.fin (Algebra.algL e)

/-- `Expr.alg`, used only when it makes the expression strictly smaller. -/
def Expr.algebra (e : Expr) : Expr :=
  let e' := e.alg
  if Algebra.dagCost e' < Algebra.dagCost e then e' else e

/-- The pass: `Expr.algebra` on every expression of the circuit. -/
def Circuit.algebra : Circuit → Circuit := Circuit.mapExprs Expr.algebra

end Damp.IR
