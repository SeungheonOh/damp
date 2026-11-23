/-
The cross-contract call assumption, stated and used.

In Damp's IR a call of another contract is a witness statement with a
reserved name (`call:<Interface>.<circuit>`, `Damp/Lang/Calls.lean`), a hash,
and the kernel claim `Kernel.claimContractCall`. To the executor's definition
(`Damp/Executor/Spec.lean`) the call is answered by the witness oracle, which
is given the caller's ledger state and returns one
(`Exec.WitnessOracle`): the definition itself lets a call read and change the
caller's ledger state. The real executor runs the callee
(`callWitness` in `executor/src/executor.mjs`) against the callee's own query
context and restores the caller's afterwards.

The assumption is `Exec.CallIsolated W` (`Damp/Executor/Witnesses.lean`): every
call's answer and private state do not depend on the caller's ledger state,
which comes back unchanged (contract state, effects and call context). It is
part of `WitnessesOK`, the hypothesis of `Pass.SoundLedger`: a call is an
isolated witness. Here:

* `runC`: the executor whose calls are answered by a separate call oracle `C`
  (`Oracles.withCalls`), every other witness by the oracles' own;
* `runC_eq_run`: under `CallIsolatedBy C c` (`C` is `c`, an oracle of calls
  that sees only the private state, lifted), `runC` is `Exec.run` with the
  calls answered by `liftWitness c`;
* `Pass.SoundLedger.runC`: a pass sound against the ledger keeps outputs,
  private transcript, private state and ledger state of `runC`, against the
  modelled ledger, from a well-formed state, for every isolated call oracle and
  every other witness doing what the runtime's do.

Without it no such statement can hold in general (not proved here, an
illustration): a call oracle that read the caller's ledger state could observe
a write that `ledgerDeadStore` removed as overwritten later, and one that wrote
it could invalidate a value `ledgerReuse` forwarded across the call.

The assumption is tested, not proved, against the runtime
(`test/calls-isolation.sh`): every query of every contract taking part in a
call is logged, and each contract's queries thread (each starts from the
contract state, effects and call context the previous one of the same contract
left), across calls, nested calls and a Damp contract running as a callee
between two calls; re-entrant calls (A calls B calls A, and A calling itself)
are refused by the runtime (`assertNoReentrancy`) before the inner call runs.
-/
import Damp.Proofs.Optimize.LedgerSound
import Damp.Proofs.Ledger.Effects
import Damp.Executor.Isolated

namespace Damp.Exec
open Damp.IR
open Damp.Zkir (Prims)

/-- The most general answer to a call: a witness oracle, given the caller's
    ledger state and returning one. -/
abbrev CallOracle (ω σ : Type) := WitnessOracle ω σ

/-- **The call assumption, for one call oracle.** The call oracle `C` is `c`,
    which does not look at the caller's ledger state, with the ledger state
    handed back unchanged. -/
def CallIsolatedBy {ω σ : Type} (C : CallOracle ω σ) (c : String → List Fr → ω → Option (List Fr × ω)) : Prop :=
  ∀ n args w l, C n args w l = (c n args w).map fun (r, w') => (r, w', l)

/-- The witness oracle with calls answered by `c`. -/
def Oracles.withCalls {ω σ : Type} (O : Oracles ω σ) (c : WitnessOracle ω σ) : Oracles ω σ :=
  { O with witness := fun n => if isCallName n then c n else O.witness n }

section
variable {ω σ : Type}

/-- `Exec.run` with calls answered by `C`. -/
def runC (p : Prims) (C : CallOracle ω σ) (O : Oracles ω σ) (c : Circuit) (inputs : List Fr) (private_ : ω)
    (ledger : σ) : Option (Result ω σ) :=
  Exec.run p (O.withCalls C) c inputs private_ ledger

theorem CallIsolatedBy.eq {C : CallOracle ω σ} {c : String → List Fr → ω → Option (List Fr × ω)}
    (hC : CallIsolatedBy C c) : C = liftWitness c := by
  funext n args w l; exact hC n args w l

/-- **Under the call assumption the executor with calls answered by `C` is
    `Exec.run`** with the calls answered by `liftWitness c`. -/
theorem runC_eq_run {p : Prims} {C : CallOracle ω σ} {c : String → List Fr → ω → Option (List Fr × ω)}
    (hC : CallIsolatedBy C c) (O : Oracles ω σ) (circ : Circuit) (inputs : List Fr) (private_ : ω) (ledger : σ) :
    runC p C O circ inputs private_ ledger = Exec.run p (O.withCalls (liftWitness c)) circ inputs private_ ledger := by
  simp only [runC, hC.eq]

/-- An isolated call oracle makes every call isolated. -/
theorem CallIsolatedBy.callIsolated {O : Oracles ω σ} {C : CallOracle ω σ}
    {c : String → List Fr → ω → Option (List Fr × ω)} (hC : CallIsolatedBy C c) :
    CallIsolated (O.withCalls C).witness := by
  intro n hn
  refine ⟨c n, fun args x l => ?_⟩
  simp only [Oracles.withCalls, hn, ite_true]
  exact hC n args x l

/-- **A witness statement whose witness keeps the ledger leaves it as it was**:
    a call under the call assumption, and every witness but
    `createZswapOutput` under `WitnessesOK`. -/
theorem step_witness_ledger (p : Prims) (O : Oracles ω σ) (s s' : State ω σ) (guard : Expr) (name : String)
    (args : List Expr) (outs : List (Var × Option Range)) (shape : Shape) (hk : KeepsLedger O.witness name)
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
          cases hw : O.witness name a s.private_ s.ledger with
          | none => simp [ha, hw] at h
          | some r =>
            obtain ⟨vals, w', l'⟩ := r
            simp only [ha, hw, Option.bind_some] at h
            split at h
            · cases h; exact hk _ _ _ _ _ _ hw
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
            cases hw : O.witness name a s.private_ s.ledger with
            | none => simp [ha, hw] at h
            | some r =>
              obtain ⟨vals, w', l'⟩ := r
              simp only [ha, hw, Option.bind_some] at h
              cases he : assign s.env outs vals with
              | none => simp [he] at h
              | some env => simp [he] at h; cases h; exact hk _ _ _ _ _ _ hw
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

/-- The modelled ledger's oracles with calls answered by `c`. -/
theorem oracles_withCalls {ω : Type} (H : Hooks) (w : WitnessOracle ω LedgerState) (c : WitnessOracle ω LedgerState) :
    (oracles H w).withCalls c = oracles H (fun n => if isCallName n then c n else w n) := rfl

/-- With witnesses that see only the private state on both sides. -/
theorem oracles_withCalls_lift {ω : Type} (H : Hooks) (w c : String → List Fr → ω → Option (List Fr × ω)) :
    (oracles H (liftWitness w)).withCalls (liftWitness c) =
      oracles H (liftWitness fun n => if isCallName n then c n else w n) := by
  simp only [oracles_withCalls]
  congr 1
  funext n
  by_cases hn : isCallName n <;> funext a x l <;> simp [hn, liftWitness]

/-- Answering the calls by an isolated call oracle keeps the witnesses doing what the runtime's do. -/
theorem _root_.Damp.Ledger.WitnessesOK.withCalls {ω : Type} {w : WitnessOracle ω LedgerState} (hw : WitnessesOK w)
    {C : CallOracle ω LedgerState} {c : String → List Fr → ω → Option (List Fr × ω)} (hC : CallIsolatedBy C c) :
    WitnessesOK (fun n => if isCallName n then C n else w n) := by
  intro n
  by_cases hn : isCallName n
  · have hcls : witnessClass n = .isolated := by
      unfold witnessClass
      have : (n == "createZswapOutput") = false := by
        cases h' : (n == "createZswapOutput") with
        | false => rfl
        | true => rw [beq_iff_eq.mp h'] at hn; simp [isCallName] at hn
      simp [this, hn]
    rw [hcls]
    exact ⟨c n, fun args x l => by simp only [hn, ite_true]; exact hC n args x l⟩
  · have := hw n
    have e : (fun n => if isCallName n = true then C n else w n) n = w n := by simp [hn]
    show WitnessFootprint (witnessClass n) (fun n => if isCallName n = true then C n else w n) n
    cases hc : witnessClass n <;> rw [hc] at this <;>
      simp only [WitnessFootprint, Isolated, CtxSlotWriter, ReadsLedger, hn, Bool.false_eq_true, ite_false] at this ⊢ <;>
      exact this

/-- **`--ledger-opt` under the call assumption.** A pass sound against the
    ledger keeps, for the executor whose calls are answered by a separate call
    oracle `C`, what `Pass.SoundLedger` keeps (outputs, private transcript,
    private state, ledger state), against the modelled ledger, from a
    well-formed state, for every call oracle that satisfies the assumption and
    every other witness doing what the runtime's do. -/
theorem Pass.SoundLedger.runC {f : Pass} (hf : Pass.SoundLedger f) {ω : Type} (H : Hooks) (p : Prims)
    (w : WitnessOracle ω LedgerState) (hw : WitnessesOK w) (C : CallOracle ω LedgerState)
    (c : String → List Fr → ω → Option (List Fr × ω)) (hC : CallIsolatedBy C c)
    (circ : Circuit) (inputs : List Fr) (private_ : ω) (σ : LedgerState) (hσ : σ.WF) :
    (runC p C (oracles H w) (f circ) inputs private_ σ).map Result.ledgerObservable =
      (runC p C (oracles H w) circ inputs private_ σ).map Result.ledgerObservable := by
  simp only [Exec.runC, oracles_withCalls]
  exact hf.exec H p _ (hw.withCalls hC) circ inputs private_ σ hσ

end Damp.IR
