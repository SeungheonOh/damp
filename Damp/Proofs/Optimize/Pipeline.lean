/-
Soundness of the pipeline: every pass in `defaultPasses` and `fullPasses` is
sound, so `Circuit.optimize` and `Circuit.optimizeFull` are.
-/
import Damp.Optimize.Pipeline
import Damp.Proofs.Optimize.Sound
import Damp.Proofs.Optimize.Bounds
import Damp.Proofs.Optimize.Algebra
import Damp.Proofs.Optimize.Asserts

namespace Damp.IR
open Damp.Zkir Damp.Exec

/-- Every default pass is sound. -/
theorem defaultPasses_sound : ∀ f ∈ defaultPasses, Pass.Sound f := by
  intro f hf
  simp only [defaultPasses, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with h | h | h | h <;> subst h
  · exact Circuit.simplify_sound
  · exact Circuit.bounds_sound
  · exact Circuit.simplify_sound
  · exact Circuit.algebra_sound

/-- Every pass is sound. -/
theorem fullPasses_sound : ∀ f ∈ fullPasses, Pass.Sound f := by
  intro f hf
  simp only [fullPasses, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with h | h | h | h | h | h <;> subst h
  · exact Circuit.simplify_sound
  · exact Circuit.asserts_sound
  · exact Circuit.simplify_sound
  · exact Circuit.bounds_sound
  · exact Circuit.simplify_sound
  · exact Circuit.algebra_sound

theorem Circuit.optimizeFull_sound : Pass.Sound Circuit.optimizeFull := runPasses_sound _ fullPasses_sound

theorem Circuit.optimize_sound : Pass.Sound Circuit.optimize := runPasses_sound _ defaultPasses_sound

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

end Damp.Exec
