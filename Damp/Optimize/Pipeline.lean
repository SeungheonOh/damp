/-
The optimizer: the passes of this directory, in order.

Each pass is a function `Circuit → Circuit`, defined in its own file here and
proved in `Damp/Proofs/Optimize/` to be *sound* (`Pass.Sound` there): for every
input it changes neither what a run of the circuit produces that anyone can
observe, nor what the executor does with it. Soundness composes, so the
pipeline is sound (`Circuit.optimize_correct`, `Exec.optimize_correct`,
`Exec.optimize_asks_same` in `Damp/Proofs/Optimize/Pipeline.lean`).

Two levels:

* `Circuit.optimize`, what the build applies by default. On a circuit written
  to mirror a Compact program it produces what compactc produces, so verifier
  keys can be compared with compactc's.
* `Circuit.optimizeFull` (`--O2`), every pass. It also uses what `assert`s
  establish, which compactc does not, so a circuit may come out smaller than
  compactc's and then has a different verifier key.

`simplify` runs again after a pass that leaves constants behind for it to fold.
-/
import Damp.Optimize.Pass
import Damp.Optimize.Simplify
import Damp.Optimize.Bounds
import Damp.Optimize.Algebra
import Damp.Optimize.Asserts

namespace Damp.IR

/-- The passes applied by default, first to last. -/
def defaultPasses : List Pass :=
  [Circuit.simplify, Circuit.bounds, Circuit.simplify, Circuit.algebra]

/-- Every pass, first to last. -/
def fullPasses : List Pass :=
  [Circuit.simplify, Circuit.asserts, Circuit.simplify, Circuit.bounds, Circuit.simplify, Circuit.algebra]

/-- Optimize a circuit. -/
def Circuit.optimize (c : Circuit) : Circuit := runPasses defaultPasses c

/-- Optimize a circuit with every pass. -/
def Circuit.optimizeFull (c : Circuit) : Circuit := runPasses fullPasses c

end Damp.IR
