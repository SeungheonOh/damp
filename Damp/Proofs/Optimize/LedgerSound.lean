/-
Soundness of a pass against the modelled ledger.

`Pass.Sound` (`Sound.lean`) asks a pass to keep what the executor does *for
every* ledger oracle: the ledger is a black box that may answer the same
question differently twice, so a sound pass must send the ledger exactly the
statements the original sends. That rules out every rewrite of the ledger
statements themselves: reading a field once instead of twice, using a value
just written instead of reading it back.

`Pass.SoundLedger` fixes the ledger oracle to the one Midnight's VM induces,
as modelled in `Damp/Ledger/` (`ledgerOracle H`, differentially tested
against the runtime by `test/vm.sh`), and constrains the witnesses only by what
the runtime's witnesses can do (`WitnessesOK`, `Damp/Executor/Witnesses.lean`:
`ownPublicKey`, `createZswapInput` and calls isolated from the ledger,
`createZswapOutput` writing call-context slot 1 only, a user's witness reading
the contract state and the call context). It asks: for every circuit, hash
functions, root hook, inputs, witness oracle meeting `WitnessesOK`, private
state, and every *well-formed* ledger state `σ` (`σ.WF`), the executor running
the rewritten circuit completes exactly when it completes on the original, and
then leaves

* the same outputs,
* the same private transcript (witness results),
* the same private state,
* the same ledger state: contract state, call context and effects.

What it does **not** promise, by design:

* the public transcript (`Result.pub`, the values the ledger reads returned)
  and the public inputs (`Result.groups`): the rewritten circuit sends fewer
  or different Impact programs, so its transcript is different, and so is its
  verifier key;
* gas, which is a function of the programs sent (and is not modelled);
* anything about ledger oracles other than the model (a pass sound in this
  sense may be wrong against a ledger that answers two identical reads
  differently, which the real one does not);
* anything about a ledger state that is not well formed;
* anything about witnesses that do more than `WitnessesOK` allows.

The executor's own theorems still apply to the rewritten circuit as to any
circuit: what it records on `f c`, the ZKIR emitted for `f c` accepts
(`Exec.run_accepted_by_emitted`). So a build with such a pass ships a circuit
and an executor that agree with each other, and agree with the original on
everything above.

* A sound pass is sound against the ledger (`Pass.Sound.soundLedger`).
* Passes sound against the ledger compose (`Pass.SoundLedger.comp`,
  `runPasses_soundLedger`).
-/
import Damp.Proofs.Optimize.Sound
import Damp.Proofs.Ledger.Basic
import Damp.Executor.Witnesses

namespace Damp.IR
open Damp.Zkir (Prims)
open Damp.Exec Damp.Ledger

/-- What a completed call leaves that `Pass.SoundLedger` keeps: the outputs,
    the private transcript, the private state and the ledger state. Not the
    public transcript or the public inputs. -/
def _root_.Damp.Exec.Result.ledgerObservable {ω σ : Type} (r : Exec.Result ω σ) :
    List Fr × List Fr × ω × σ :=
  (r.outputs, r.priv, r.private_, r.ledger)

/-- The pass does not change what the executor does against the modelled
    ledger, with witnesses that do what the runtime's do (`WitnessesOK`), from
    any well-formed ledger state, except for the public transcript and the
    public inputs. -/
structure Pass.SoundLedger (f : Pass) : Prop where
  exec : ∀ {ω : Type} (H : Hooks) (p : Prims) (w : WitnessOracle ω LedgerState), WitnessesOK w →
    ∀ (c : Circuit) (inputs : List Fr) (private_ : ω) (σ : LedgerState), σ.WF →
    (Exec.run p (oracles H w) (f c) inputs private_ σ).map Result.ledgerObservable =
      (Exec.run p (oracles H w) c inputs private_ σ).map Result.ledgerObservable

theorem Result.ledgerObservable_of_observable {ω σ : Type} (r r' : Exec.Result ω σ)
    (h : r.observable = r'.observable) : r.ledgerObservable = r'.ledgerObservable := by
  simp only [Result.observable, Prod.mk.injEq] at h
  simp only [Result.ledgerObservable, h]

/-- A sound pass is sound against the ledger: it keeps more, for every oracle. -/
theorem Pass.Sound.soundLedger {f : Pass} (h : Pass.Sound f) : Pass.SoundLedger f := by
  refine ⟨fun {ω} H p w _ c inputs private_ σ _ => ?_⟩
  have e := h.exec p (oracles H w) c inputs private_ σ
  cases h1 : Exec.run p (oracles H w) (f c) inputs private_ σ <;>
    cases h2 : Exec.run p (oracles H w) c inputs private_ σ <;> rw [h1, h2] at e <;> simp at e ⊢
  exact Result.ledgerObservable_of_observable _ _ e

theorem Pass.SoundLedger.id : Pass.SoundLedger (fun c => c) := ⟨fun _ _ _ _ _ _ _ _ _ => rfl⟩

/-- Passes sound against the ledger compose. -/
theorem Pass.SoundLedger.comp {f g : Pass} (hf : Pass.SoundLedger f) (hg : Pass.SoundLedger g) :
    Pass.SoundLedger (fun c => g (f c)) := 
  ⟨fun H p w hw c i pr σ hσ => (hg.exec H p w hw (f c) i pr σ hσ).trans (hf.exec H p w hw c i pr σ hσ)⟩

/-- A list of passes sound against the ledger, applied in order, is sound against the ledger. -/
theorem runPasses_soundLedger (ps : List Pass) (h : ∀ f ∈ ps, Pass.SoundLedger f) :
    Pass.SoundLedger (runPasses ps) := by
  induction ps with
  | nil => exact Pass.SoundLedger.id
  | cons f ps ih =>
      have hf := h f (List.mem_cons_self ..)
      have hps := ih fun g hg => h g (List.mem_cons_of_mem _ hg)
      exact Pass.SoundLedger.comp (f := f) (g := runPasses ps) hf hps

/-- A sound pass followed by passes sound against the ledger (the shape of a
    pipeline with the ledger passes appended). -/
theorem Pass.SoundLedger.after_sound {f g : Pass} (hf : Pass.Sound f) (hg : Pass.SoundLedger g) :
    Pass.SoundLedger (fun c => g (f c)) :=
  Pass.SoundLedger.comp hf.soundLedger hg

end Damp.IR
