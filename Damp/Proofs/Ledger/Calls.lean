/-
The cross-contract call assumption, stated and used.

In Damp's IR a call of another contract is a witness statement with a
reserved name (`call:<Interface>.<circuit>`, `Damp/Lang/Calls.lean`), a hash,
and the kernel claim `Kernel.claimContractCall`. To the executor's definition
(`Damp/Executor/Spec.lean`) the call is therefore answered by the witness
oracle, `String → List Fr → ω → Option (List Fr × ω)`, which sees neither the
caller's ledger state nor can it return one: by its type, `Exec.run` threads the
caller's ledger state unchanged across the call statement
(`step_witness_ledger`). Every theorem about `Exec.run`, `--ledger-opt`'s
(`Pass.SoundLedger`) included, is therefore about callers whose callees cannot
touch their ledger state. That is an assumption about the real executor, which
runs the callee for real (`callWitness` in `executor/src/executor.mjs`).

This file makes the assumption explicit. It defines the executor with the most
general call oracle (`CallOracle`): one that is given the caller's ledger state
and returns one (`stepC`, `stepsC`, `runC`; every other statement as
`Exec.step`). The assumption is `CallIsolated C c`: the call oracle `C` is
`c`, an oracle that does not look at the caller's ledger state, with the
ledger state handed back unchanged. Under it:

* `runC_eq_run`: the general executor is `Exec.run` with `c` answering the
  calls (`Oracles.withCalls`), so every theorem about `Exec.run` applies;
* `Pass.SoundLedger.runC`: in particular a pass sound against the ledger
  (`--ledger-opt`) keeps outputs, private transcript, private state and ledger
  state of the general executor, against the modelled ledger, from a
  well-formed state, for every isolated call oracle.

Without it no such statement can hold in general (not proved here, an
illustration): a call oracle that read the caller's ledger state could observe
a write that `ledgerDeadStore` removed as overwritten later, and one that wrote
it could invalidate a value `ledgerReuse` forwarded across the call.

The assumption is tested, not proved, against the runtime
(`test/calls-isolation.sh`): every query of every contract taking part in a
call is logged, and each contract's queries thread (each starts from the
contract state and effects the previous one of the same contract left), across
calls, nested calls and a Damp contract running as a callee between two
calls; re-entrant calls (A calls B calls A, and A calling itself) are refused
by the runtime (`assertNoReentrancy`) before the inner call runs.
-/
import Damp.Proofs.Optimize.LedgerSound
import Damp.Proofs.Ledger.Effects

namespace Damp.Exec
open Damp.IR
open Damp.Zkir (Prims)

/-- Whether a witness name is that of a cross-contract call (`callWitnessName`). -/
def isCallName (n : String) : Bool := n.startsWith "call:"

/-- The most general answer to a call: given the witness name, the field
    elements of the address and arguments, the private state and the CALLER's
    ledger state, the result's field elements, the private state and the
    caller's ledger state afterwards. -/
abbrev CallOracle (ω σ : Type) := String → List Fr → ω → σ → Option (List Fr × ω × σ)

/-- **The call assumption.** The call oracle `C` is `c`, which does not look at
    the caller's ledger state, and it hands the caller's ledger state back
    unchanged: a callee runs against its own state, and neither reads nor writes
    the caller's. -/
def CallIsolated {ω σ : Type} (C : CallOracle ω σ) (c : String → List Fr → ω → Option (List Fr × ω)) : Prop :=
  ∀ n args w l, C n args w l = (c n args w).map fun (r, w') => (r, w', l)

/-- The witness oracle with calls answered by `c`. -/
def Oracles.withCalls {ω σ : Type} (O : Oracles ω σ) (c : String → List Fr → ω → Option (List Fr × ω)) :
    Oracles ω σ :=
  { O with witness := fun n => if isCallName n then c n else O.witness n }

section
variable {ω σ : Type}

/-- `Exec.step` with calls answered by the general call oracle `C`, which sees
    and returns the caller's ledger state. A call is `Exec.step`'s witness case
    with `C` in place of `O.witness`; every other statement, other witnesses
    included, is `Exec.step`. -/
def stepC (p : Prims) (C : CallOracle ω σ) (O : Oracles ω σ) (s : State ω σ) : Stmt → Option (State ω σ)
  | .witness guard name args outs shape =>
      if isCallName name then do
        let g ← guard.eval p s.env
        if outs.isEmpty then
          if g = 1 then
            let argVals ← Expr.evalList p s.env args
            let (vals, private_, ledger) ← C name argVals s.private_ s.ledger
            if vals.isEmpty then pure { s with private_, ledger } else none
          else pure s
        else
          let active ← asBool g
          if active then
            let argVals ← Expr.evalList p s.env args
            let (vals, private_, ledger) ← C name argVals s.private_ s.ledger
            let env ← assign s.env outs vals
            pure { s with env, private_, ledger, priv := s.priv ++ vals }
          else
            let env ← assign s.env outs (outs.map fun _ => 0)
            pure { s with env }
      else Exec.step p O s (.witness guard name args outs shape)
  | stmt => Exec.step p O s stmt

def stepsC (p : Prims) (C : CallOracle ω σ) (O : Oracles ω σ) : List Stmt → State ω σ → Option (State ω σ)
  | [], s => some s
  | stmt :: rest, s => do
      let s' ← stepC p C O s stmt
      stepsC p C O rest s'

/-- `Exec.run` with calls answered by `C`. -/
def runC (p : Prims) (C : CallOracle ω σ) (O : Oracles ω σ) (c : Circuit) (inputs : List Fr) (private_ : ω)
    (ledger : σ) : Option (Result ω σ) := do
  let env ← bindInputs (fun _ => 0) c.inputs inputs
  let s ← stepsC p C O c.body.toList { env, private_, ledger }
  let outputs ← Expr.evalList p s.env c.outputs
  pure { outputs, priv := s.priv, pub := s.pub, groups := s.groups, private_ := s.private_, ledger := s.ledger }

/-- Under the call assumption, a statement runs as `Exec.step` with the calls
    answered by `c`. -/
theorem stepC_eq {p : Prims} {C : CallOracle ω σ} {c : String → List Fr → ω → Option (List Fr × ω)}
    (hC : CallIsolated C c) (O : Oracles ω σ) (s : State ω σ) (stmt : Stmt) :
    stepC p C O s stmt = Exec.step p (O.withCalls c) s stmt := by
  unfold CallIsolated at hC
  cases stmt with
  | witness guard name args outs shape =>
    by_cases hn : isCallName name
    · simp only [stepC, hn, ite_true, Exec.step, Oracles.withCalls, hC]
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
              cases c name a s.private_ with
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
                cases c name a s.private_ with
                | none => rfl
                | some r => obtain ⟨r, w'⟩ := r; rfl
            · rfl
    · simp only [stepC, hn]
      simp [Exec.step, Oracles.withCalls, hn]
  | _ => simp only [stepC]; cases s; rfl

theorem stepsC_eq {p : Prims} {C : CallOracle ω σ} {c : String → List Fr → ω → Option (List Fr × ω)}
    (hC : CallIsolated C c) (O : Oracles ω σ) :
    ∀ (stmts : List Stmt) (s : State ω σ), stepsC p C O stmts s = Exec.steps p (O.withCalls c) stmts s
  | [], _ => rfl
  | stmt :: rest, s => by
      simp only [stepsC, Exec.steps, stepC_eq hC O s stmt]
      cases Exec.step p (O.withCalls c) s stmt with
      | none => rfl
      | some s' => exact stepsC_eq hC O rest s'

/-- **Under the call assumption the general executor is `Exec.run`**, with the
    calls answered by `c`: every theorem about `Exec.run` applies to it. -/
theorem runC_eq_run {p : Prims} {C : CallOracle ω σ} {c : String → List Fr → ω → Option (List Fr × ω)}
    (hC : CallIsolated C c) (O : Oracles ω σ) (circ : Circuit) (inputs : List Fr) (private_ : ω) (ledger : σ) :
    runC p C O circ inputs private_ ledger = Exec.run p (O.withCalls c) circ inputs private_ ledger := by
  simp only [runC, Exec.run, stepsC_eq hC O]

/-- **`Exec.step` threads the ledger state unchanged across every witness
    statement, a call's included**: the witness oracle cannot return a ledger
    state. -/
theorem step_witness_ledger (p : Prims) (O : Oracles ω σ) (s s' : State ω σ) (guard : Expr) (name : String)
    (args : List Expr) (outs : List (Var × Option Range)) (shape : Shape)
    (h : Exec.step p O s (.witness guard name args outs shape) = some s') : s'.ledger = s.ledger := by
  simp only [Exec.step] at h
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

/-- And across a `bind` (the call's commitment). -/
theorem step_bind_ledger (p : Prims) (O : Oracles ω σ) (s s' : State ω σ) (v : Var) (hint : String) (e : Expr)
    (h : Exec.step p O s (.bind v hint e) = some s') : s'.ledger = s.ledger := by
  simp only [Exec.step] at h
  cases he : e.eval p s.env with
  | none => simp [he] at h
  | some x => simp [he] at h; cases h; rfl

end

end Damp.Exec

namespace Damp.IR
open Damp.Exec Damp.Ledger
open Damp.Zkir (Prims)

/-- The modelled ledger's oracles with calls answered by `c`: the modelled
    ledger with the witness oracle that answers the calls by `c`. -/
theorem oracles_withCalls {ω : Type} (H : Hooks) (w : String → List Fr → ω → Option (List Fr × ω))
    (c : String → List Fr → ω → Option (List Fr × ω)) :
    (oracles H w).withCalls c = oracles H (fun n => if isCallName n then c n else w n) := rfl

/-- **`--ledger-opt` under the call assumption.** A pass sound against the
    ledger keeps, for the executor whose calls may see and change the caller's
    ledger state, what `Pass.SoundLedger` keeps (outputs, private transcript,
    private state, ledger state), against the modelled ledger, from a
    well-formed state, for every call oracle that satisfies the assumption. -/
theorem Pass.SoundLedger.runC {f : Pass} (hf : Pass.SoundLedger f) {ω : Type} (H : Hooks) (p : Prims)
    (w : String → List Fr → ω → Option (List Fr × ω)) (C : CallOracle ω LedgerState)
    (c : String → List Fr → ω → Option (List Fr × ω)) (hC : CallIsolated C c)
    (circ : Circuit) (inputs : List Fr) (private_ : ω) (σ : LedgerState) (hσ : σ.WF) :
    (runC p C (oracles H w) (f circ) inputs private_ σ).map Result.ledgerObservable =
      (runC p C (oracles H w) circ inputs private_ σ).map Result.ledgerObservable := by
  rw [runC_eq_run hC, runC_eq_run hC, oracles_withCalls]
  exact hf.exec H p _ circ inputs private_ σ hσ

end Damp.IR
