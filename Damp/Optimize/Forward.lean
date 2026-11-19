/-
Forward substitution across statements.

The expression-level passes see one expression at a time, so they cannot
combine `v6 := v0 + -v1` with a later `v6 + v1`. `Circuit.forward` walks the
statements in order, remembering bindings `v := e` (with `e` itself already
substituted), and replaces later uses of `v` by `e`, so that `algebra` and
`simplify`, run afterwards, see the whole computation.

## What it keeps

* Every statement stays, in place: a `bind` whose variable is inlined
  everywhere is still there (so a binding that fails still fails the run, and
  the environments of the original and the rewritten circuit are equal
  throughout). The emitter drops a binding nothing reads (`Emit.pruneDeadBinds`).
* Witness and ledger statements keep their place, names, guards and
  arguments' values: only their expressions are rewritten, and a substituted
  expression has the same value as what it replaces.

## When `v` is replaced by `e` (the side conditions)

Remembered after `bind v _ e` (with `e` substituted):

* only when `e` does not mention `v` (otherwise, after the binding, `e` means
  something else: `v := v + 1`);
* only when the eligibility test accepts it (`Forward.elig`: `v` is used at most
  once in the whole circuit, or `e` costs no instruction). This is a cost
  heuristic; soundness does not depend on it.

Forgotten, before anything else is remembered:

* a remembered `w := e` is forgotten as soon as a statement binds `w` again or
  binds a variable that `e` mentions (a `bind`, a witness's results, a ledger
  statement's reads). No single-assignment assumption is needed: a circuit that
  rebinds variables simply gets fewer substitutions.

Ledger statements: the guard is evaluated before the reads, the operands both
before (for the request sent to the ledger, by the executor) and after (for the
public inputs). So operands are substituted only with what is remembered
after forgetting everything that touches a read variable; such a substitution
means the same thing on both sides of the reads. A `popeq` result, a plain read
variable, is therefore never replaced; and the rewritten instructions are kept
only when `ledgerProblem` accepts them, otherwise the original ones are, so
`checkLedger` is preserved whatever the input.

Proved sound in `Damp/Proofs/Optimize/Forward.lean`: runs of the rewritten
circuit are exactly the runs of the original (`Circuit.forwardWith_run`,
`Circuit.forwardWith_exec`).

## Cashing in

Substitution alone changes nothing the emitter produces (it shares equal
expressions, and drops bindings nothing reads); it pays only through the passes
run after it. `Circuit.forwardOpt` runs `forward`, then `algebra` and
`simplify`, and keeps the result only when the emitted circuit is strictly
smaller (`Pass.choose`), so it never makes a circuit bigger.
-/
import Damp.Optimize.Algebra
import Damp.Optimize.Choose
import Damp.Compile.Emit

namespace Damp.IR

namespace Forward

/-- Remembered bindings: each variable with an expression of the same value. -/
abbrev Map := List (Var × Expr)

/-- Forget every binding of a variable in `vs` and every binding whose
    expression mentions one. -/
def kill (m : Map) (vs : List Var) : Map :=
  m.filter fun q => !(vs.contains q.1) && !(q.2.vars.any vs.contains)

/-- Rewrite one statement with what is remembered; and what is remembered after it. -/
def stmt (elig : Var → Expr → Bool) (m : Map) : Stmt → Stmt × Map
  | .bind v hint e =>
      let e' := e.subst m
      let m' := kill m [v]
      (.bind v hint e', if elig v e' && !(e'.vars.contains v) then (v, e') :: m' else m')
  | .assert c msg => (.assert (c.subst m) msg, m)
  | .constrain e r => (.constrain (e.subst m) r, m)
  | .witness g name args outs shape =>
      (.witness (g.subst m) name (args.map (Expr.subst m)) outs shape, kill m (outs.map (·.1)))
  | .ledger g reads ops =>
      let m' := kill m reads
      let ops' := ops.map (·.map (Expr.subst m'))
      (.ledger (g.subst m) reads (if (IR.ledgerProblem reads ops').isNone then ops' else ops), m')

/-- Rewrite a list of statements; and what is remembered at the end. -/
def go (elig : Var → Expr → Bool) : Map → List Stmt → List Stmt × Map
  | m, [] => ([], m)
  | m, st :: rest =>
      let r := stmt elig m st
      let q := go elig r.2 rest
      (r.1 :: q.1, q.2)

/-- Every variable occurrence in a circuit's statements and outputs. -/
def occurrences (c : Circuit) : List Var :=
  c.body.toList.flatMap Emit.uses ++ c.outputs.flatMap Expr.vars

/-- Which bindings to inline: a variable used at most once, or an expression
    that costs no instruction. -/
def elig (c : Circuit) : Var → Expr → Bool :=
  let occ := occurrences c
  fun v e => occ.count v ≤ 1 || Algebra.cost e == 0

end Forward

/-- Forward substitution with a given eligibility test. -/
def Circuit.forwardWith (elig : Var → Expr → Bool) (c : Circuit) : Circuit :=
  let r := Forward.go elig [] c.body.toList
  { c with body := r.1.toArray, outputs := c.outputs.map (Expr.subst r.2) }

/-- The pass: forward substitution of bindings used at most once (see the header). -/
def Circuit.forward (c : Circuit) : Circuit := c.forwardWith (Forward.elig c)

/-- Forward substitution of every binding it may (no cost test). -/
def Circuit.forwardAll (c : Circuit) : Circuit := c.forwardWith fun _ _ => true

/-- Number of instructions emitted for a circuit, if it can be emitted. -/
def Circuit.emittedSize (c : Circuit) : Option Nat :=
  match Emit.circuit c with
  | .ok src => some src.instructions.size
  | .error _ => none

/-- Whether the first circuit emits to strictly fewer instructions than the second. -/
def Circuit.emitsSmaller (a b : Circuit) : Bool :=
  match a.emittedSize, b.emittedSize with
  | some x, some y => x < y
  | _, _ => false

/-- `forward`, then `algebra` and `simplify` to cash it in, kept only when the
    emitted circuit is strictly smaller. -/
def Circuit.forwardOpt : Pass :=
  Pass.choose (fun c => (Circuit.forward c).algebra.simplify) (fun c => c) Circuit.emitsSmaller

end Damp.IR
