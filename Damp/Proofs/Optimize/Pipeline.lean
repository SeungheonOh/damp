/-
Soundness of the pipeline: every pass in `defaultPasses` and `fullPasses` is
sound, so `Circuit.optimize` and `Circuit.optimizeFull` are. `--O3`
(`Circuit.optimizeMaxWith p`) is sound relative to the hash functions `p` it
folds with (`Circuit.optimizeMaxWith_soundFor`), so `Circuit.optimizeMax` is
sound when the circuit is run with `Damp.Crypto.prims`
(`Circuit.optimizeMax_correct`, `Exec.optimizeMax_correct`).
-/
import Damp.Optimize.Pipeline
import Damp.Proofs.Optimize.Sound
import Damp.Proofs.Optimize.Bounds
import Damp.Proofs.Optimize.Algebra
import Damp.Proofs.Optimize.Asserts
import Damp.Proofs.Optimize.Bounds2
import Damp.Proofs.Optimize.Forward
import Damp.Proofs.Optimize.FoldHashes
import Damp.Proofs.Optimize.InlineAll
import Damp.Proofs.Optimize.AssertEq
import Damp.Proofs.Optimize.Commute

namespace Damp.IR
open Damp.Zkir Damp.Exec

/-- Every default pass is sound. -/
theorem defaultPasses_sound : ∀ f ∈ defaultPasses, Pass.Sound f := by
  intro f hf
  simp only [defaultPasses, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with h | h | h | h | h | h <;> subst h
  · exact Circuit.simplify_sound
  · exact Circuit.foldDivmod_sound
  · exact Circuit.bounds2_sound
  · exact Circuit.simplify_sound
  · exact Circuit.algebra_sound
  · exact Circuit.commuteOpt_sound

/-- Every pass is sound. -/
theorem fullPasses_sound : ∀ f ∈ fullPasses, Pass.Sound f := by
  intro f hf
  simp only [fullPasses, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with h | h | h | h | h | h | h | h | h | h | h <;> subst h
  · exact Circuit.simplify_sound
  · exact Circuit.foldDivmod_sound
  · exact Circuit.assertEq_sound
  · exact Circuit.asserts_sound
  · exact Circuit.simplify_sound
  · exact Circuit.bounds2_sound
  · exact Circuit.simplify_sound
  · exact Circuit.algebra_sound
  · exact Circuit.forwardOpt_sound
  · exact Circuit.forwardAllOpt_sound
  · exact Circuit.commuteOpt_sound

theorem Circuit.optimizeFull_sound : Pass.Sound Circuit.optimizeFull := runPasses_sound _ fullPasses_sound

theorem Circuit.optimize_sound : Pass.Sound Circuit.optimize := runPasses_sound _ defaultPasses_sound

/-- Every `--O3` pass is sound for the hash functions `p` it folds with. -/
theorem maxPassesWith_soundFor (p : Prims) : ∀ f ∈ maxPassesWith p, Pass.SoundFor p f := by
  intro f hf
  simp only [maxPassesWith, List.mem_cons] at hf
  rcases hf with h | h | h
  · subst h; exact Circuit.simplify_sound.soundFor p
  · subst h; exact Circuit.foldHashes_soundFor p
  · exact (fullPasses_sound f h).soundFor p

theorem Circuit.optimizeMaxWith_soundFor (p : Prims) : Pass.SoundFor p (Circuit.optimizeMaxWith p) :=
  runPasses_soundFor p _ (maxPassesWith_soundFor p)

/-- `--O3` is sound when the hash functions are Damp's implementations of
    Midnight's (`Damp.Crypto.prims`). -/
theorem Circuit.optimizeMax_soundFor : Pass.SoundFor Crypto.prims Circuit.optimizeMax :=
  Circuit.optimizeMaxWith_soundFor Crypto.prims

/-- `--O3` does not change what a run with `Damp.Crypto.prims` produces that
    anyone can observe. -/
theorem Circuit.optimizeMax_correct (c : Circuit) (inputs priv pub : List Fr) :
    (c.optimizeMax.run Crypto.prims inputs priv pub).map Outcome.observable =
      (c.run Crypto.prims inputs priv pub).map Outcome.observable :=
  Circuit.optimizeMax_soundFor.run c inputs priv pub

/-- Optimizing a circuit does not change what a run of it produces that anyone
    can observe: it fails exactly when the original does, and otherwise has the
    same outputs and the same public inputs of the instructions that ran. -/
theorem Circuit.optimize_correct (p : Prims) (c : Circuit) (inputs priv pub : List Fr) :
    (c.optimize.run p inputs priv pub).map Outcome.observable =
      (c.run p inputs priv pub).map Outcome.observable :=
  Circuit.optimize_sound.run p c inputs priv pub

end Damp.IR

namespace Damp.Exec
open Damp.IR Damp.Zkir

variable {ω σ : Type}

/-- Optimizing a circuit does not change what the executor does with it: run
    on the optimized circuit, it completes exactly when it would on the
    original, and leaves the same outputs, transcripts, public inputs of the
    instructions that ran, private state and ledger state, for every witness
    and ledger oracle. -/
theorem optimize_correct (p : Prims) (O : Oracles ω σ) (c : Circuit)
    (inputs : List Fr) (private_ : ω) (ledger : σ) :
    (run p O c.optimize inputs private_ ledger).map Result.observable
      = (run p O c inputs private_ ledger).map Result.observable :=
  Circuit.optimize_sound.exec p O c inputs private_ ledger

/-- On the optimized circuit the executor asks the witnesses exactly the same
    questions, in the same order, and sends the ledger exactly the same
    instructions, in the same order, as on the original; and the calls
    complete together. -/
theorem optimize_asks_same (p : Prims) (O : Oracles ω σ) (c : Circuit)
    (inputs : List Fr) (private_ : ω) (ledger : σ) :
    (run p O.logged c.optimize inputs (private_, []) (ledger, [])).map (fun r => (r.private_.2, r.ledger.2))
      = (run p O.logged c inputs (private_, []) (ledger, [])).map (fun r => (r.private_.2, r.ledger.2)) := by
  have h := optimize_correct p O.logged c inputs (private_, []) (ledger, [])
  have h' := congrArg (Option.map fun (o : List Fr × List Fr × List Fr × List Fr × _ × _) =>
    (o.2.2.2.2.1.2, o.2.2.2.2.2.2)) h
  simpa [Option.map_map, Function.comp_def, Result.observable] using h'

/-- `--O3` does not change what the executor does with `Damp.Crypto.prims`,
    for every witness and ledger oracle. -/
theorem optimizeMax_correct (O : Oracles ω σ) (c : Circuit)
    (inputs : List Fr) (private_ : ω) (ledger : σ) :
    (run Crypto.prims O c.optimizeMax inputs private_ ledger).map Result.observable
      = (run Crypto.prims O c inputs private_ ledger).map Result.observable :=
  Circuit.optimizeMax_soundFor.exec O c inputs private_ ledger

end Damp.Exec
