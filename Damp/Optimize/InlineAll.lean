/-
Removing computations whose only consumers are witness-call arguments.

A witness call's arguments are evaluated by the executor, never by the circuit:
the emitter compiles a witness statement to its `private_input`s alone. But
the emitter's pruning of unused bindings (`Emit.pruneDeadBinds`, one backward
liveness pass, already a fixpoint: a dropped binding makes nothing live) counts
the variables a witness argument mentions as used (`Emit.uses`), so a binding
read only by witness arguments, and everything only it reads, is emitted and
constrains nothing that matters.

`Circuit.forwardAllOpt` substitutes every binding it may into every later use
(`Circuit.forwardAll`; the side conditions are those of `Damp/Optimize/Forward.lean`),
then lets `algebra` and `simplify` cash it in, and keeps the result only when the
emitted circuit has strictly fewer instructions (`Pass.choose`). After the
substitution a witness argument names only variables that are not bindings
(inputs, witness results, ledger reads) or that could not be substituted, so a
binding used only through witness arguments is read by nothing the emitter
compiles and is pruned. The emitter shares equal expressions, so substituting a
binding used several times does not by itself duplicate instructions; where
the rewrites after it lose sharing, the size test rejects the result.

Sound for every circuit (`Circuit.forwardAllOpt_sound`): every statement
stays, witness and ledger statements keep their place and their arguments'
values. Used at `--O2` and `--O3` only: compactc keeps these computations, so
removing them changes the verifier key of a circuit that mirrors a Compact
program (`zerocash_core.spend` in the benchmark).
-/
import Damp.Optimize.Forward

namespace Damp.IR

/-- `forwardAll`, then `algebra` and `simplify`, kept only when the emitted
    circuit is strictly smaller. -/
def Circuit.forwardAllOpt : Pass :=
  Pass.choose (fun c => (Circuit.forwardAll c).algebra.simplify) (fun c => c) Circuit.emitsSmaller

end Damp.IR
