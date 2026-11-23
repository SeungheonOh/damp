/-
The compiler's correctness, end to end.

`Contract.build` ships, for each circuit `c`, the ZKIR

    Emit.circuit c.optimize

Three results are chained here:

* `Circuit.optimize_correct` (`Damp/Proofs/Optimize/Simplify.lean`): optimizing does not
  change what a run produces that anyone can observe;
* `pruned_run` (`Damp/Proofs/Prune.lean`): dropping unused bindings keeps every
  accepted run (and, since only bindings that cannot fail are dropped, loses
  no rejection either: `Emit.pruned_run_eq` in `Damp/Proofs/Shipped.lean`,
  which also restates the pass theorems for the shipped ZKIR);
* `circuitCore_correct` (`Damp/Proofs/Emit.lean`): the emitted ZKIR, run by the
  ZKIR evaluator, gives exactly what the IR semantics gives.

The ZKIR evaluator (`Damp/Zkir/Semantics.lean`) is a port of Midnight's
reference implementation, tested against it by `test/semantics.sh`. Nothing
here says anything about the step from that evaluator to the constraint
system and the proof: that is Midnight's, and upstream's own result.
-/
import Damp.Proofs.Emit
import Damp.Proofs.Optimize.Pipeline
import Damp.Proofs.Prune

set_option linter.unusedSimpArgs false

namespace Damp
open Damp.IR
open Damp.Zkir (Prims Outcome)

/-- The circuit whose ZKIR is shipped for `c`: optimized, unused bindings dropped. -/
def IR.Circuit.shipped (c : Circuit) : Circuit := Emit.pruned c.optimize

/-- What `Emit.circuit` returns is the emission of the circuit without its unused bindings. -/
theorem Emit.circuit_eq_core (c : Circuit) (src : Zkir.IrSource) (h : Emit.circuit c = .ok src) :
    Emit.circuitCore (Emit.pruned c) = .ok src := by
  unfold Emit.circuit at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  · cases hcore : Emit.circuitCore (Emit.pruned c) with
    | error m => simp [hcore, bind, Except.bind] at h
    | ok src' =>
        cases hchk : src'.checkProducer with
        | error m => simp [hcore, hchk, bind, Except.bind, Functor.map, Except.map] at h
        | ok u =>
            simp [hcore, hchk, bind, Except.bind, Functor.map, Except.map, pure, Except.pure] at h
            rw [h]

/-- **The shipped ZKIR means exactly the shipped circuit.** For every input and
    pair of transcripts, Midnight's evaluator on the emitted ZKIR and the IR
    semantics on the shipped circuit give the same result: the same outputs
    and public inputs, or both reject. -/
theorem compile_exact (p : Prims) (c : Circuit) (src : Zkir.IrSource)
    (h : Emit.circuit c.optimize = .ok src) (inputs priv pub : List Fr) :
    src.run p inputs priv pub = c.shipped.run p inputs priv pub :=
  Emit.circuitCore_correct p _ src (Emit.circuit_eq_core _ src h) inputs priv pub

/-- Nothing is lost by a pass sound for the hash functions `p` followed by
    emission: every run with `p` the contract's circuit accepts is accepted by
    the ZKIR emitted for the rewritten circuit, with the same outputs and the
    same public inputs for the on-chain instructions that ran. -/
theorem compile_complete_ofFor {f : Pass} {p : Prims} (hf : Pass.SoundFor p f) (c : Circuit) (src : Zkir.IrSource)
    (h : Emit.circuit (f c) = .ok src) (inputs priv pub : List Fr) (o : Outcome)
    (hrun : c.run p inputs priv pub = some o) :
    ∃ o', src.run p inputs priv pub = some o' ∧ o'.observable = o.observable := by
  have hopt := hf.run c inputs priv pub
  rw [hrun] at hopt
  cases hrun' : (f c).run p inputs priv pub with
  | none => simp [hrun'] at hopt
  | some o' =>
      simp only [hrun', Option.map_some, Option.some.injEq] at hopt
      refine ⟨o', ?_, hopt⟩
      rw [Emit.circuitCore_correct p _ src (Emit.circuit_eq_core _ src h) inputs priv pub]
      exact Emit.pruned_run p (f c) inputs priv pub o' hrun'

/-- Nothing is lost by a sound pass followed by emission, whatever the hash
    functions. -/
theorem compile_complete_of {f : Pass} (hf : Pass.Sound f) (p : Prims) (c : Circuit) (src : Zkir.IrSource)
    (h : Emit.circuit (f c) = .ok src) (inputs priv pub : List Fr) (o : Outcome)
    (hrun : c.run p inputs priv pub = some o) :
    ∃ o', src.run p inputs priv pub = some o' ∧ o'.observable = o.observable :=
  compile_complete_ofFor (hf.soundFor p) c src h inputs priv pub o hrun

/-- **Nothing is lost.** Every run the contract's circuit accepts is accepted
    by the emitted ZKIR, with the same outputs and the same public inputs for
    the on-chain instructions that ran. -/
theorem compile_complete (p : Prims) (c : Circuit) (src : Zkir.IrSource)
    (h : Emit.circuit c.optimize = .ok src) (inputs priv pub : List Fr) (o : Outcome)
    (hrun : c.run p inputs priv pub = some o) :
    ∃ o', src.run p inputs priv pub = some o' ∧ o'.observable = o.observable :=
  compile_complete_of Circuit.optimize_sound p c src h inputs priv pub o hrun

/-- The same with every pass (`--O2`). -/
theorem compile_complete_full (p : Prims) (c : Circuit) (src : Zkir.IrSource)
    (h : Emit.circuit c.optimizeFull = .ok src) (inputs priv pub : List Fr) (o : Outcome)
    (hrun : c.run p inputs priv pub = some o) :
    ∃ o', src.run p inputs priv pub = some o' ∧ o'.observable = o.observable :=
  compile_complete_of Circuit.optimizeFull_sound p c src h inputs priv pub o hrun

/-- The same with `--O3`, for runs with Damp's implementations of Midnight's
    hash functions (`Damp.Crypto.prims`), the ones `--O3` folds constant hashes
    with. -/
theorem compile_complete_max (c : Circuit) (src : Zkir.IrSource)
    (h : Emit.circuit c.optimizeMax = .ok src) (inputs priv pub : List Fr) (o : Outcome)
    (hrun : c.run Crypto.prims inputs priv pub = some o) :
    ∃ o', src.run Crypto.prims inputs priv pub = some o' ∧ o'.observable = o.observable :=
  compile_complete_ofFor Circuit.optimizeMax_soundFor c src h inputs priv pub o hrun

end Damp
