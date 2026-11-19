/-
The executor, as a definition.

When a user calls a circuit, something on their machine has to run it for
real: evaluate the expressions, ask the witnesses, run the ledger operations
against the current public state, and write down everything the prover needs.
That is the executor. The one that ships is JavaScript
(`executor/src/executor.mjs`); this file says what it must do, in Lean, so
that it can be reasoned about. `Damp/Proofs/Executor.lean` proves that every
call this executor completes is one the circuit accepts, with the transcripts
and public inputs the executor recorded. `test/executor.sh` checks that the
JavaScript executor does the same thing as this definition, step for step.

The two things the executor cannot compute for itself are parameters:

* the witnesses, which run the user's own code against their private state;
* the ledger, Midnight's on-chain virtual machine, which runs the public
  instructions against the contract's state and reports what they read.
-/
import Damp.IR.Semantics

namespace Damp.Exec
open Damp.IR
open Damp.Zkir (Prims Group)

/-- What the executor is given to work with. `ω` is the user's private state,
    `σ` the public ledger state. Either may refuse (`none`). -/
structure Oracles (ω σ : Type) where
  /-- Run the named witness on its arguments: the field elements of its
      result, and the private state afterwards. -/
  witness : String → List Fr → ω → Option (List Fr × ω)
  /-- Run on-chain instructions: the field elements they read, in order, and
      the ledger state afterwards. Each `popeq` arrives with an empty result. -/
  ledger : List (Impact.Op Fr) → σ → Option (List Fr × σ)

structure State (ω σ : Type) where
  env : Env
  /-- The private transcript recorded so far: every witness result, in order. -/
  priv : List Fr := []
  /-- The values read from the ledger so far, in order. -/
  pub : List Fr := []
  /-- The public inputs declared so far. -/
  groups : List Group := []
  private_ : ω
  ledger : σ

/-- Bind variables to values, checking each against its range. The counts must match. -/
def assign (env : Env) : List (Var × Option Range) → List Fr → Option Env
  | [], [] => some env
  | (v, range) :: rest, x :: xs =>
      match range with
      | some r => if r.holds x then assign (env.set v x) rest xs else none
      | none => assign (env.set v x) rest xs
  | _, _ => none

/-- An instruction as it is sent to the ledger: what it reads is not yet known. -/
def blank : Impact.Op Fr → Impact.Op Fr
  | .popeq cached align _ => .popeq cached align []
  | op => op

/-- The instructions of a ledger statement with their operands evaluated. -/
def request (p : Prims) (env : Env) : List (Impact.Op Expr) → Option (List (Impact.Op Fr))
  | [] => some []
  | op :: ops => do
      let op' ← op.mapM (Expr.eval p env)
      let rest ← request p env ops
      pure (blank op' :: rest)

/-- Run one statement. `none` means the call fails. -/
def step (p : Prims) (O : Oracles ω σ) (s : State ω σ) : Stmt → Option (State ω σ)
  | .bind v _ e => do
      let x ← e.eval p s.env
      pure { s with env := s.env.set v x }
  | .assert cond _ => do
      let c ← cond.eval p s.env
      let c ← asBool c
      if c then pure s else none
  | .constrain e r => do
      let x ← e.eval p s.env
      if r.holds x then pure s else none
  | .witness guard name args outs _ => do
      let g ← guard.eval p s.env
      if outs.isEmpty then
        -- Nothing for the circuit to read, so the circuit ignores it. It still
        -- runs when its guard holds: such a witness exists to update the
        -- private state.
        if g = 1 then
          let argVals ← Expr.evalList p s.env args
          let (vals, private_) ← O.witness name argVals s.private_
          if vals.isEmpty then pure { s with private_ } else none
        else pure s
      else
        let active ← asBool g
        if active then
          let argVals ← Expr.evalList p s.env args
          let (vals, private_) ← O.witness name argVals s.private_
          let env ← assign s.env outs vals
          pure { s with env, private_, priv := s.priv ++ vals }
        else
          -- Not asked: its results are zero, and nothing is recorded.
          let env ← assign s.env outs (outs.map fun _ => 0)
          pure { s with env }
  | .ledger guard reads ops => do
      let g ← guard.eval p s.env
      if reads.isEmpty && ops.isEmpty then pure s
      else
        let active ← asBool g
        if active then
          let req ← request p s.env ops
          let (vals, ledger) ← O.ledger req s.ledger
          let env ← assign s.env (reads.map fun v => (v, none)) vals
          let groups ← ledgerGroups p env true ops
          pure { s with env, ledger, pub := s.pub ++ vals, groups := s.groups ++ groups }
        else
          -- Not run: its reads are zero, and it declares zeroed public inputs.
          let env ← assign s.env (reads.map fun v => (v, none)) (reads.map fun _ => 0)
          let groups ← ledgerGroups p env false ops
          pure { s with env, groups := s.groups ++ groups }

def steps (p : Prims) (O : Oracles ω σ) : List Stmt → State ω σ → Option (State ω σ)
  | [], s => some s
  | stmt :: rest, s => do
      let s' ← step p O s stmt
      steps p O rest s'

/-- What a completed call leaves behind. The first four fields are the proof
    data: with the inputs, they are what the prover is given. -/
structure Result (ω σ : Type) where
  outputs : List Fr
  /-- The private transcript. -/
  priv : List Fr
  /-- The values read from the ledger. -/
  pub : List Fr
  /-- The public inputs, one group per on-chain instruction. -/
  groups : List Group
  private_ : ω
  ledger : σ

/-- Run a circuit on inputs, from a private state and a ledger state. -/
def run (p : Prims) (O : Oracles ω σ) (c : Circuit) (inputs : List Fr) (private_ : ω) (ledger : σ) :
    Option (Result ω σ) := do
  let env ← bindInputs (fun _ => 0) c.inputs inputs
  let s ← steps p O c.body.toList { env, private_, ledger }
  let outputs ← Expr.evalList p s.env c.outputs
  pure { outputs, priv := s.priv, pub := s.pub, groups := s.groups,
         private_ := s.private_, ledger := s.ledger }

end Damp.Exec
