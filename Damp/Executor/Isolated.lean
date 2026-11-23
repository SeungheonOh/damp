/-
The executor whose witnesses cannot touch the ledger, and that it is a special
case of `Exec.run`.

Until the witness oracle was given the ledger state (`Exec.WitnessOracle`,
`Damp/Executor/Spec.lean`), a witness saw only the private state:
`String → List Fr → ω → Option (List Fr × ω)`, and the executor threaded the
ledger state unchanged across every witness statement. That executor is kept
here, word for word, as `Exec.Iso.run`. `Exec.run_lift` shows it is `Exec.run`
with the witness oracle `liftWitness w`, the one that ignores the ledger state
and hands it back unchanged. So every statement proved of the old executor is a
statement about `Exec.run` under the hypothesis that the witnesses leave the
ledger alone, which in the runtime holds of `ownPublicKey`, `createZswapInput`
and cross-contract calls, and not of user witnesses (they read the contract
state) nor of `createZswapOutput` (it writes the call context): see
`Damp/Executor/Witnesses.lean`.
-/
import Damp.Executor.Spec

namespace Damp.Exec
open Damp.IR
open Damp.Zkir (Prims)

/-- The oracles of the executor whose witnesses see only the private state. -/
structure IsoOracles (ω σ : Type) where
  witness : String → List Fr → ω → Option (List Fr × ω)
  ledger : List (Impact.Op Fr) → σ → Option (List Fr × σ)

/-- As oracles of `Exec.run`: the witnesses neither see nor change the ledger. -/
def IsoOracles.lift {ω σ : Type} (O : IsoOracles ω σ) : Oracles ω σ :=
  { witness := liftWitness O.witness, ledger := O.ledger }

namespace Iso
variable {ω σ : Type}

/-- `Exec.step` with a witness that sees only the private state. -/
def step (p : Prims) (O : IsoOracles ω σ) (s : State ω σ) : Stmt → Option (State ω σ)
  | .witness guard name args outs _ => do
      let g ← guard.eval p s.env
      if outs.isEmpty then
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
          let env ← assign s.env outs (outs.map fun _ => 0)
          pure { s with env }
  | stmt => Exec.step p O.lift s stmt

def steps (p : Prims) (O : IsoOracles ω σ) : List Stmt → State ω σ → Option (State ω σ)
  | [], s => some s
  | stmt :: rest, s => do
      let s' ← step p O s stmt
      steps p O rest s'

def run (p : Prims) (O : IsoOracles ω σ) (c : Circuit) (inputs : List Fr) (private_ : ω) (ledger : σ) :
    Option (Result ω σ) := do
  let env ← bindInputs (fun _ => 0) c.inputs inputs
  let s ← steps p O c.body.toList { env, private_, ledger }
  let outputs ← Expr.evalList p s.env c.outputs
  pure { outputs, priv := s.priv, pub := s.pub, groups := s.groups,
         private_ := s.private_, ledger := s.ledger }

end Iso

variable {ω σ : Type}

theorem step_lift (p : Prims) (O : IsoOracles ω σ) (s : State ω σ) (stmt : Stmt) :
    Exec.step p O.lift s stmt = Iso.step p O s stmt := by
  cases stmt with
  | witness guard name args outs shape =>
    simp only [Exec.step, Iso.step, IsoOracles.lift, liftWitness]
    cases guard.eval p s.env with
    | none => rfl
    | some g =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      split
      · split
        · cases Expr.evalList p s.env args with
          | none => rfl
          | some a =>
            simp only [Option.bind_some]
            cases O.witness name a s.private_ with
            | none => rfl
            | some r => obtain ⟨r, w'⟩ := r; rfl
        · rfl
      · cases asBool g with
        | none => rfl
        | some b =>
          simp only [Option.bind_some]
          split
          · cases Expr.evalList p s.env args with
            | none => rfl
            | some a =>
              simp only [Option.bind_some]
              cases O.witness name a s.private_ with
              | none => rfl
              | some r => obtain ⟨r, w'⟩ := r; rfl
          · rfl
  | _ => rfl

theorem steps_lift (p : Prims) (O : IsoOracles ω σ) :
    ∀ (stmts : List Stmt) (s : State ω σ), Exec.steps p O.lift stmts s = Iso.steps p O stmts s
  | [], _ => rfl
  | stmt :: rest, s => by
      simp only [Exec.steps, Iso.steps, step_lift p O s stmt]
      cases Iso.step p O s stmt with
      | none => rfl
      | some s' => exact steps_lift p O rest s'

/-- **The executor whose witnesses cannot touch the ledger is `Exec.run` with
    `liftWitness`.** -/
theorem run_lift (p : Prims) (O : IsoOracles ω σ) (c : Circuit) (inputs : List Fr) (private_ : ω) (ledger : σ) :
    Exec.run p O.lift c inputs private_ ledger = Iso.run p O c inputs private_ ledger := by
  simp only [Exec.run, Iso.run, steps_lift]

/-- Under such witnesses a witness statement leaves the ledger state as it was. -/
theorem Iso.step_witness_ledger (p : Prims) (O : IsoOracles ω σ) (s s' : State ω σ) (guard : Expr) (name : String)
    (args : List Expr) (outs : List (Var × Option Range)) (shape : Shape)
    (h : Iso.step p O s (.witness guard name args outs shape) = some s') : s'.ledger = s.ledger := by
  simp only [Iso.step] at h
  cases hg : guard.eval p s.env with
  | none => simp [hg] at h
  | some g =>
    simp only [hg, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · split at h
      · cases ha : Expr.evalList p s.env args with
        | none => simp [ha] at h
        | some a =>
          cases hw : O.witness name a s.private_ with
          | none => simp [ha, hw] at h
          | some r =>
            obtain ⟨vals, w'⟩ := r
            simp only [ha, hw, Option.bind_some] at h
            split at h
            · cases h; rfl
            · simp at h
      · cases h; rfl
    · cases hb : asBool g with
      | none => simp [hb] at h
      | some b =>
        simp only [hb, Option.bind_some] at h
        split at h
        · cases ha : Expr.evalList p s.env args with
          | none => simp [ha] at h
          | some a =>
            cases hw : O.witness name a s.private_ with
            | none => simp [ha, hw] at h
            | some r =>
              obtain ⟨vals, w'⟩ := r
              simp only [ha, hw, Option.bind_some] at h
              cases he : assign s.env outs vals with
              | none => simp [he] at h
              | some env => simp [he] at h; cases h; rfl
        · cases he : assign s.env outs (outs.map fun _ => 0) with
          | none => simp [he] at h
          | some env => simp [he] at h; cases h; rfl

end Damp.Exec
