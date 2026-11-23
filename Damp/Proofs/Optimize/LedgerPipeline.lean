/-
`--ledger-opt`: the ledger passes (`ledgerPasses`: `ledgerReuse`, then the
`--O2` passes again, `optimizeFull`, then `ledgerDeadStore`, then
`ledgerHoist`, then `ledgerMerge`) after a level's passes.

* The ledger passes are sound against the modelled ledger
  (`ledgerPasses_soundLedger`) and keep the ledger check
  (`ledgerPasses_keepsLedger`).
* After the default level or `--O2` (sound passes) the combination is
  `Pass.SoundLedger` (`Circuit.optimize_ledger_soundLedger`,
  `Circuit.optimizeFull_ledger_soundLedger`).
* After `--O3`, which is sound only for `Damp.Crypto.prims`, the combination is
  sound against the modelled ledger for those hash functions
  (`Pass.SoundLedgerFor`, `Circuit.optimizeMax_ledger_soundLedgerFor`).

`Pass.SoundLedgerFor p` is `Pass.SoundLedger` at one choice of hash functions,
as `Pass.SoundFor p` is `Pass.Sound` at one.
-/
import Damp.Proofs.Optimize.Pipeline
import Damp.Proofs.Optimize.LedgerCheck
import Damp.Proofs.Optimize.LedgerSound
import Damp.Proofs.Optimize.LedgerReuse
import Damp.Proofs.Optimize.LedgerDeadStore
import Damp.Proofs.Optimize.LedgerReuseCheck
import Damp.Proofs.Optimize.LedgerMerge
import Damp.Proofs.Optimize.LedgerHoist

namespace Damp.IR
open Damp.Zkir (Prims)
open Damp.Exec Damp.Ledger

/-- At the hash functions `p`, the pass does not change what the executor
    does against the modelled ledger, with witnesses that do what the
    runtime's do (`WitnessesOK`), from any well-formed ledger state,
    except for the public transcript and the public inputs. -/
structure Pass.SoundLedgerFor (p : Prims) (f : Pass) : Prop where
  exec : ∀ {ω : Type} (H : Hooks) (w : WitnessOracle ω LedgerState), WitnessesOK w → ∀
    (c : Circuit) (inputs : List Fr) (private_ : ω) (σ : LedgerState), σ.WF →
    (Exec.run p (oracles H w) (f c) inputs private_ σ).map Result.ledgerObservable =
      (Exec.run p (oracles H w) c inputs private_ σ).map Result.ledgerObservable

/-- Sound against the modelled ledger for all hash functions, so for `p`. -/
theorem Pass.SoundLedger.soundLedgerFor {f : Pass} (h : Pass.SoundLedger f) (p : Prims) :
    Pass.SoundLedgerFor p f :=
  ⟨fun H w hw c i pr σ hσ => h.exec H p w hw c i pr σ hσ⟩

/-- A pass sound for `p` is sound against the modelled ledger for `p`. -/
theorem Pass.SoundFor.soundLedgerFor {p : Prims} {f : Pass} (h : Pass.SoundFor p f) :
    Pass.SoundLedgerFor p f := by
  refine ⟨fun {ω} H w _ c inputs private_ σ _ => ?_⟩
  have e := h.exec (oracles H w) c inputs private_ σ
  cases h1 : Exec.run p (oracles H w) (f c) inputs private_ σ <;>
    cases h2 : Exec.run p (oracles H w) c inputs private_ σ <;> rw [h1, h2] at e <;> simp at e ⊢
  exact Result.ledgerObservable_of_observable _ _ e

/-- Passes sound against the modelled ledger for `p` compose. -/
theorem Pass.SoundLedgerFor.comp {p : Prims} {f g : Pass} (hf : Pass.SoundLedgerFor p f)
    (hg : Pass.SoundLedgerFor p g) : Pass.SoundLedgerFor p (fun c => g (f c)) :=
  ⟨fun H w hw c i pr σ hσ => (hg.exec H w hw (f c) i pr σ hσ).trans (hf.exec H w hw c i pr σ hσ)⟩

/-- A pass sound for `p` followed by a pass sound against the modelled ledger
    is sound against the modelled ledger for `p`. -/
theorem Pass.SoundLedgerFor.after_soundFor {p : Prims} {f g : Pass} (hf : Pass.SoundFor p f)
    (hg : Pass.SoundLedger g) : Pass.SoundLedgerFor p (fun c => g (f c)) :=
  hf.soundLedgerFor.comp (hg.soundLedgerFor p)

/-- Every ledger pass is sound against the modelled ledger. -/
theorem ledgerPasses_soundLedger' : ∀ f ∈ ledgerPasses, Pass.SoundLedger f := by
  intro f hf
  simp only [ledgerPasses, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with h | h | h | h | h <;> subst h
  · exact Circuit.ledgerReuse_soundLedger
  · exact Circuit.optimizeFull_sound.soundLedger
  · exact Circuit.ledgerDeadStore_soundLedger
  · exact Circuit.ledgerHoist_soundLedger
  · exact Circuit.ledgerMerge_soundLedger

/-- The ledger passes, in order, are sound against the modelled ledger. -/
theorem ledgerPasses_soundLedger : Pass.SoundLedger (runPasses ledgerPasses) :=
  runPasses_soundLedger _ ledgerPasses_soundLedger'

/-- The ledger passes keep ledger statements well formed. -/
theorem ledgerPasses_keepsLedger : Pass.KeepsLedger (runPasses ledgerPasses) := by
  refine runPasses_keepsLedger _ ?_
  intro f hf
  simp only [ledgerPasses, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with h | h | h | h | h <;> subst h
  · exact Circuit.ledgerReuse_checkLedger
  · exact Circuit.optimizeFull_checkLedger
  · exact Circuit.ledgerDeadStore_checkLedger
  · exact Circuit.ledgerHoist_checkLedger
  · exact Circuit.ledgerMerge_checkLedger

/-- The default level, then the ledger passes, is sound against the modelled ledger. -/
theorem Circuit.optimize_ledger_soundLedger :
    Pass.SoundLedger (fun c => runPasses ledgerPasses c.optimize) :=
  Pass.SoundLedger.after_sound Circuit.optimize_sound ledgerPasses_soundLedger

/-- `--O2`, then the ledger passes, is sound against the modelled ledger. -/
theorem Circuit.optimizeFull_ledger_soundLedger :
    Pass.SoundLedger (fun c => runPasses ledgerPasses c.optimizeFull) :=
  Pass.SoundLedger.after_sound Circuit.optimizeFull_sound ledgerPasses_soundLedger

/-- `--O3`, then the ledger passes, is sound against the modelled ledger when
    the hash functions are `Damp.Crypto.prims`. -/
theorem Circuit.optimizeMax_ledger_soundLedgerFor :
    Pass.SoundLedgerFor Crypto.prims (fun c => runPasses ledgerPasses c.optimizeMax) :=
  Pass.SoundLedgerFor.after_soundFor Circuit.optimizeMax_soundFor ledgerPasses_soundLedger

end Damp.IR
