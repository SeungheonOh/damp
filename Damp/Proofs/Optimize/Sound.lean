/-
Soundness of a pass.

A pass is sound when, for every circuit and every input, it changes neither
what a run produces that anyone can observe (`Pass.SoundRun`) nor what the
executor does, whatever its oracles answer (`Pass.SoundExec`). Both are
equalities, so they compose: a list of sound passes is a sound pass
(`runPasses_sound`). Each pass's own file here proves it sound.
-/
import Damp.Optimize.Pass
import Damp.Proofs.Optimize.SimplifyExecutor

namespace Damp.IR
open Damp.Zkir Damp.Exec

/-- The pass does not change what a run produces that anyone can observe. -/
def Pass.SoundRun (f : Pass) : Prop :=
  ∀ (p : Prims) (c : Circuit) (inputs priv pub : List Fr),
    ((f c).run p inputs priv pub).map Outcome.observable =
      (c.run p inputs priv pub).map Outcome.observable

/-- The pass does not change what the executor does, for any oracles. -/
def Pass.SoundExec (f : Pass) : Prop :=
  ∀ {ω σ : Type} (p : Prims) (O : Oracles ω σ) (c : Circuit) (inputs : List Fr) (private_ : ω) (ledger : σ),
    (Exec.run p O (f c) inputs private_ ledger).map Result.observable =
      (Exec.run p O c inputs private_ ledger).map Result.observable

/-- A sound pass. -/
structure Pass.Sound (f : Pass) : Prop where
  run : f.SoundRun
  exec : f.SoundExec

theorem Pass.Sound.id : Pass.Sound (fun c => c) := ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

/-- Sound passes compose. -/
theorem Pass.Sound.comp {f g : Pass} (hf : Pass.Sound f) (hg : Pass.Sound g) :
    Pass.Sound (fun c => g (f c)) :=
  ⟨fun p c i pr pu => (hg.run p (f c) i pr pu).trans (hf.run p c i pr pu),
   fun p O c i w l => (hg.exec p O (f c) i w l).trans (hf.exec p O c i w l)⟩

/-- A list of sound passes, applied in order, is a sound pass. -/
theorem runPasses_sound : ∀ (ps : List Pass), (∀ f ∈ ps, Pass.Sound f) → Pass.Sound (runPasses ps)
  | [], _ => Pass.Sound.id
  | f :: ps, h => by
      have hf := h f (List.mem_cons_self ..)
      have hps := runPasses_sound ps fun g hg => h g (List.mem_cons_of_mem _ hg)
      exact Pass.Sound.comp (f := f) (g := runPasses ps) hf hps

theorem Circuit.simplify_sound : Pass.Sound Circuit.simplify :=
  ⟨Circuit.simplify_correct, fun p O c i w l => Exec.simplify_correct p O c i w l⟩

end Damp.IR
