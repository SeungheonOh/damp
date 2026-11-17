/-
Optimization of the circuit IR.

Two layers:

* `Expr.simp` rewrites expressions: constant folding, arithmetic identities,
  conditionals with a known condition, negated conditions. It is proved to
  preserve `Expr.eval` exactly, failures included (`Expr.simp_eval` in
  `Damp/OptimizeCorrect.lean`).
* `Circuit.optimize` walks the statements: it propagates constants and copies,
  drops checks that are known to hold or are implied by an earlier check,
  drops witness calls and ledger operations whose guard is the constant 0, and
  removes conditionals that only restate a boolean. It is proved not to change
  what a run produces that anyone can observe (`Circuit.optimize_correct`),
  nor what the executor asks its oracles and leaves behind
  (`Exec.optimize_correct` in `Damp/OptimizeExecutor.lean`).
  On a circuit that rebinds a variable whose old value it still relies on (the
  emitter rejects such circuits anyway) it gives up and changes nothing.

Expression evaluation is partial (see `Damp/Semantics.lean`), and a circuit
must not start accepting inputs it used to reject. So a rewrite that drops a
subexpression requires it to be `total` (it cannot fail), and a rewrite that
drops the requirement that a condition is 0 or 1 requires it to be `isBool`.

The optimized circuit is what both the ZKIR emitter and the executor see, so
they stay in agreement by construction.
-/
import Damp.Semantics

namespace Damp.IR
open Damp.Zkir (fitsBits)

/-! ## What cannot fail -/

/-- Whether an expression is certainly 0 or 1 when it has a value, given the
    variables known to be. -/
def Expr.isBool (bools : List Var) : Expr → Bool
  | .var v => bools.contains v
  | .const c => c == 0 || c == 1
  | .lt .. | .eq .. => true
  | .select _ a b => a.isBool bools && b.isBool bools
  | .disclose e => e.isBool bools
  | _ => false

mutual
/-- Whether an expression certainly has a value, given the variables known to
    be 0 or 1. Comparisons and persistent hashes can fail; so can a conditional
    whose condition might not be 0 or 1. -/
def Expr.total (bools : List Var) : Expr → Bool
  | .var _ | .const _ => true
  | .add a b | .mul a b | .eq a b => a.total bools && b.total bools
  | .neg a | .disclose a => a.total bools
  | .divmod _ bits a => decide (bits ≤ 248) && a.total bools
  | .select c a b => c.isBool bools && c.total bools && a.total bools && b.total bools
  | .hash xs => Expr.totalList bools xs
  | .lt .. | .phash .. | .invalid _ => false
/-- Every expression in the list is `total`. -/
def Expr.totalList (bools : List Var) : List Expr → Bool
  | [] => true
  | x :: xs => x.total bools && Expr.totalList bools xs
end

/-! ## Expressions -/

/-- A field element as a constant expression. -/
def canon (x : Fr) : Expr := .const (Int.ofNat x.val)

def mkAdd : Expr → Expr → Expr
  | .const x, .const y => canon (Fr.ofInt x + Fr.ofInt y)
  | .const 0, e => e
  | e, .const 0 => e
  | a, b => .add a b

/-- `0 * e` is `0` only when `e` cannot fail. -/
def mkMul : Expr → Expr → Expr
  | .const x, .const y => canon (Fr.ofInt x * Fr.ofInt y)
  | .const 0, e => if e.total [] then .const 0 else .mul (.const 0) e
  | e, .const 0 => if e.total [] then .const 0 else .mul e (.const 0)
  | .const 1, e => e
  | e, .const 1 => e
  | a, b => .mul a b

def mkNeg : Expr → Expr
  | .const x => canon (- Fr.ofInt x)
  | .neg e => e
  | e => .neg e

/-- A comparison of constants is folded only when both fit the width; otherwise
    it fails at run time and is left to do so. -/
def mkLt (bits : Nat) : Expr → Expr → Expr
  | .const x, .const y =>
      if fitsBits (Fr.ofInt x) bits && fitsBits (Fr.ofInt y) bits then
        canon (Fr.ofBool ((Fr.ofInt x).val < (Fr.ofInt y).val))
      else .lt bits (.const x) (.const y)
  | a, b => .lt bits a b

/-- `e == e` is `1` only when `e` cannot fail. -/
def mkEq : Expr → Expr → Expr
  | .const x, .const y => canon (Fr.ofBool (Fr.ofInt x = Fr.ofInt y))
  | a, b => if a == b && a.total [] then .const 1 else .eq a b

/-- `select` when the two branches differ. A constant condition picks a branch
    only when the dropped branch cannot fail. -/
def mkSelectDistinct : Expr → Expr → Expr → Expr
  | .const c, a, b =>
      if Fr.ofInt c = 1 ∧ b.total [] then a
      else if Fr.ofInt c = 0 ∧ a.total [] then b
      else .select (.const c) a b
  | .select s (.const 0) (.const 1), a, b => .select s b a
  | c, a, b => .select c a b

/-- A conditional whose branches are the same expression is that expression,
    provided the condition cannot fail and is certainly 0 or 1. -/
def mkSelect (c a b : Expr) : Expr :=
  if a == b && c.total [] && c.isBool [] then a else mkSelectDistinct c a b

mutual
/-- Simplify an expression, bottom up. -/
def Expr.simp : Expr → Expr
  | .add a b => mkAdd a.simp b.simp
  | .mul a b => mkMul a.simp b.simp
  | .neg a => mkNeg a.simp
  | .lt bits a b => mkLt bits a.simp b.simp
  | .eq a b => mkEq a.simp b.simp
  | .select c a b => mkSelect c.simp a.simp b.simp
  | .divmod quot bits a => .divmod quot bits a.simp
  | .hash xs => .hash (Expr.simpList xs)
  | .phash high align xs => .phash high align (Expr.simpList xs)
  | .var v => .var v
  | .const c => .const c
  | .invalid msg => .invalid msg
  -- The disclosure check has run by now; the marker is dropped.
  | .disclose e => e.simp
def Expr.simpList : List Expr → List Expr
  | [] => []
  | x :: xs => x.simp :: Expr.simpList xs
end

/-! ## Statements -/

mutual
/-- Replace variables by what is known about them. -/
def Expr.subst (σ : List (Var × Expr)) : Expr → Expr
  | .var v => (σ.lookup v).getD (.var v)
  | .const c => .const c
  | .invalid msg => .invalid msg
  | .disclose e => .disclose (e.subst σ)
  | .add a b => .add (a.subst σ) (b.subst σ)
  | .mul a b => .mul (a.subst σ) (b.subst σ)
  | .neg a => .neg (a.subst σ)
  | .lt bits a b => .lt bits (a.subst σ) (b.subst σ)
  | .eq a b => .eq (a.subst σ) (b.subst σ)
  | .select c a b => .select (c.subst σ) (a.subst σ) (b.subst σ)
  | .divmod quot bits a => .divmod quot bits (a.subst σ)
  | .hash xs => .hash (Expr.substList σ xs)
  | .phash high align xs => .phash high align (Expr.substList σ xs)
def Expr.substList (σ : List (Var × Expr)) : List Expr → List Expr
  | [] => []
  | x :: xs => x.subst σ :: Expr.substList σ xs
end

/-- Whether every value passing the first range check passes the second, as
    `Range.holds` decides them. Widths of 255 bits or more never pass, and a
    `below` check also needs its bound to fit its width. -/
def Range.implies : Range → Range → Bool
  | .zero, r => r.holds 0
  | _, .zero => false
  | .bool, r => r.holds 0 && r.holds 1
  | .bits n, .bool => n ≤ 1
  | .bits n, .bits m => n ≤ m && m < Zkir.frBits
  | .bits n, .below b w => n ≤ w && fitsBits (Fr.ofInt b) w && 2 ^ n ≤ (Fr.ofInt b).val
  | .below b _, .bool => (Fr.ofInt b).val ≤ 2
  | .below b _, .bits m => (Fr.ofInt b).val ≤ 2 ^ m && m < Zkir.frBits
  | .below b _, .below b' w' => (Fr.ofInt b).val ≤ (Fr.ofInt b').val && fitsBits (Fr.ofInt b') w'

mutual
/-- `select c 1 0` is `c` when `c` is 0 or 1, and `select c a a` is `a` when
    `c` cannot fail and is 0 or 1. -/
def Expr.boolSimp (bools : List Var) : Expr → Expr
  | .select c a b =>
      let c := c.boolSimp bools
      let a := a.boolSimp bools
      let b := b.boolSimp bools
      if a == b && c.total bools && c.isBool bools then a
      else
        match a, b with
        | .const 1, .const 0 => if c.isBool bools then c else .select c a b
        | _, _ => .select c a b
  | .add a b => .add (a.boolSimp bools) (b.boolSimp bools)
  | .mul a b => .mul (a.boolSimp bools) (b.boolSimp bools)
  | .neg a => .neg (a.boolSimp bools)
  | .lt bits a b => .lt bits (a.boolSimp bools) (b.boolSimp bools)
  | .eq a b => .eq (a.boolSimp bools) (b.boolSimp bools)
  | .divmod quot bits a => .divmod quot bits (a.boolSimp bools)
  | .hash xs => .hash (Expr.boolSimpList bools xs)
  | .phash high align xs => .phash high align (Expr.boolSimpList bools xs)
  | .disclose e => .disclose (e.boolSimp bools)
  | .var v => .var v
  | .const c => .const c
  | .invalid msg => .invalid msg
def Expr.boolSimpList (bools : List Var) : List Expr → List Expr
  | [] => []
  | x :: xs => x.boolSimp bools :: Expr.boolSimpList bools xs
end

/-- What the pass knows at a point of the circuit. `known` relates the
    original circuit's variables to expressions over the optimized circuit's
    variables (bindings of constants and copies are not emitted); `bools` and
    `checked` are facts about the optimized circuit's variables. -/
structure Facts where
  /-- Variables known to equal a constant or another variable. -/
  known : List (Var × Expr) := []
  /-- Variables known to be 0 or 1. -/
  bools : List Var := []
  /-- Expressions known to have a value that passes the range check. -/
  checked : List (Expr × Range) := []

/-- Rewrite an expression with what is known. -/
def Facts.rw (f : Facts) (e : Expr) : Expr := ((e.subst f.known).simp).boolSimp f.bools

/-- Forget every fact about these variables, which are about to be bound. -/
def Facts.forget (f : Facts) (vs : List Var) : Facts where
  known := f.known.filter fun (u, _) => !vs.contains u
  bools := f.bools.filter (!vs.contains ·)
  checked := f.checked.filter fun (e, _) => e.vars.all (!vs.contains ·)

/-- Whether binding these variables would change a value the pass relies on: a
    known value that mentions one of them, for a variable that is not itself
    rebound. This cannot happen when every variable is bound once before it is
    used, which the emitter enforces; if it does, the pass gives up. -/
def Facts.clash (f : Facts) (vs : List Var) : Bool :=
  f.known.any fun (u, e) => !vs.contains u && e.vars.any vs.contains

/-- Whether the pass knows a value for one of these variables. A ledger
    statement's instructions are sent to the ledger before its reads are bound,
    so there a read variable still has its old value; if that value is only
    known to the pass (its binding was not emitted), the optimized circuit does
    not hold it, and the pass gives up. This cannot happen when every variable
    is bound once. -/
def Facts.knows (f : Facts) (vs : List Var) : Bool :=
  vs.any fun v => (f.known.lookup v).isSome

/-- Whether a range check of `e` is known to pass: a constant in range, or
    implied by an earlier check. -/
def Facts.passes (f : Facts) (e : Expr) (r : Range) : Bool :=
  (match e with
   | .const c => r.holds (Fr.ofInt c)
   | _ => false) ||
  f.checked.any fun (e0, r0) => e0 == e && r0.implies r

/-- The variables known to be 0 or 1 once `e` has passed the range check `r`. -/
def Facts.boolsAfter (f : Facts) (e : Expr) (r : Range) : List Var :=
  match e, r.implies .bool with
  | .var v, true => v :: f.bools
  | _, _ => f.bools

/-- A witness call that certainly asks nothing: the guard is the constant 0 and
    zero passes the range check of every result. A call with no results is kept
    unless its guard is 0: the circuit ignores it, but the executor runs it for
    its effect on the private state. -/
def witnessSkipped (g : Expr) (outs : List (Var × Option Range)) : Bool :=
  match g with
  | .const c => Fr.ofInt c = 0 && outs.all fun (_, r) => r.all (Range.holds 0)
  | _ => false

/-- The range checks a witness call's results are known to pass afterwards:
    each is checked as it arrives. With a variable named twice only the last
    value stays, so then nothing is recorded. -/
def witnessChecks (outs : List (Var × Option Range)) : List (Expr × Range) :=
  if (outs.map (·.1)).Nodup then outs.filterMap fun (v, r) => r.map fun r => (Expr.var v, r)
  else []

/-- The results of a witness call known to be 0 or 1 afterwards. -/
def witnessBools (outs : List (Var × Option Range)) : List Var :=
  if (outs.map (·.1)).Nodup then
    outs.filterMap fun (v, r) =>
      match r with
      | some r => if r.implies .bool then some v else none
      | none => none
  else []

/-- The operands of an on-chain instruction, as they are evaluated. -/
def opOperands (op : Impact.Op Expr) : List Expr := op.encode Expr.const

/-- A ledger statement that certainly runs nothing observable: the guard is the
    constant 0 and every operand (evaluated even then) cannot fail, or there is
    nothing in it. -/
def ledgerSkipped (g : Expr) (bools : List Var) (reads : List Var) (ops : List (Impact.Op Expr)) : Bool :=
  match g with
  | .const c =>
      (reads.isEmpty && ops.isEmpty) ||
      (Fr.ofInt c = 0 && ops.all fun op => Expr.totalList bools (opOperands op))
  | _ => false

/-- Optimize one statement: the statements that replace it and the facts after
    it, or `none` if the pass gives up (see `Facts.clash` and `Facts.knows`). -/
def Stmt.optimize (f : Facts) : Stmt → Option (List Stmt × Facts)
  | .bind v hint e =>
      match f.rw e with
      | .const c => some ([], { f with known := (v, .const c) :: f.known })
      | .var w => some ([], { f with known := (v, .var w) :: f.known })
      | e' =>
          if f.clash [v] then none
          else
            let f' := f.forget [v]
            some ([.bind v hint e'],
                  if e'.isBool f.bools then { f' with bools := v :: f'.bools } else f')
  | .assert cond msg =>
      match f.rw cond with
      | .const 1 => some ([], f)
      | c => some ([.assert c msg], f)
  | .constrain e r =>
      let e' := f.rw e
      if f.passes e' r then some ([], f)
      else some ([.constrain e' r], { f with checked := (e', r) :: f.checked, bools := f.boolsAfter e' r })
  | .witness guard name args outs shape =>
      let g := f.rw guard
      let vs := outs.map (·.1)
      if witnessSkipped g outs then
        -- Never asked: its results are zero.
        some ([], { f with known := vs.map (fun v => (v, Expr.const 0)) ++ f.known })
      else if f.clash vs then none
      else
        let f' := f.forget vs
        some ([.witness g name (args.map f.rw) outs shape],
              { f' with checked := witnessChecks outs ++ f'.checked,
                        bools := witnessBools outs ++ f'.bools })
  | .ledger guard reads ops =>
      let g := f.rw guard
      -- If nothing runs, the reads are zero, and the operands are evaluated with them.
      let f0 := { f with known := reads.map (fun v => (v, Expr.const 0)) ++ f.known }
      if ledgerSkipped g f0.bools reads (ops.map (·.map f0.rw)) then some ([], f0)
      else if f.clash reads then none
      else if f.knows reads then none
      else
        -- The public inputs are evaluated after the reads, the instructions
        -- sent to the ledger before them (see `Facts.knows`).
        let f' := f.forget reads
        some ([.ledger g reads (ops.map (·.map f'.rw))], f')

/-- Optimize a list of statements in order. -/
def Stmt.optimizeAll (f : Facts) : List Stmt → Option (List Stmt × Facts)
  | [] => some ([], f)
  | s :: rest => do
      let (a, f1) ← s.optimize f
      let (b, f2) ← Stmt.optimizeAll f1 rest
      pure (a ++ b, f2)

/-- Optimize a circuit. A circuit the pass gives up on is returned unchanged. -/
def Circuit.optimize (c : Circuit) : Circuit :=
  match Stmt.optimizeAll {} c.body.toList with
  | some (body, f) => { c with body := body.toArray, outputs := c.outputs.map f.rw }
  | none => c

end Damp.IR
