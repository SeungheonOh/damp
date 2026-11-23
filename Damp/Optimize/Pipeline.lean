/-
The optimizer: the passes of this directory, in order.

Each pass is a function `Circuit → Circuit`, defined in its own file here and
proved in `Damp/Proofs/Optimize/` to be *sound* (`Pass.Sound` there): for every
input it changes neither what a run of the circuit produces that anyone can
observe, nor what the executor does with it. Soundness composes, so the
pipeline is sound (`Circuit.optimize_correct`, `Exec.optimize_correct`,
`Exec.optimize_asks_same` in `Damp/Proofs/Optimize/Pipeline.lean`).

Three levels:

* `Circuit.optimize`, what the build applies by default. On a circuit written
  to mirror a Compact program it produces what compactc produces, so verifier
  keys can be compared with compactc's.
* `Circuit.optimizeFull` (`--O2`), every sound pass. It also uses what
  `assert`s establish (`asserts`), and substitutes bindings into later
  statements (`forwardOpt`, kept only when the emitted circuit gets smaller),
  which compactc does not, so a circuit may come out smaller than compactc's
  and then has a different verifier key.
* `Circuit.optimizeMax` (`--O3`), `--O2` after computing hashes of constants
  at compile time (`foldHashes`) with `Damp.Crypto.prims`, the Lean
  implementations of Midnight's Poseidon and SHA-256, and then without the
  range checks that a later persistent hash implies (`hashRanges`: the hash
  refuses an input that does not fit the bytes it reads it as). Every other
  level is sound whatever the hash functions are (`Pass.Sound`); this one only
  when they are those implementations (`Pass.SoundFor Crypto.prims`), which
  `test/semantics.sh` checks against Midnight's runtime on samples but which
  are not proved equal to it.

`--ledger-opt` appends `ledgerPasses` to any of these levels. They are sound
in a weaker sense (`Pass.SoundLedger`): only against the modelled ledger, and
the public transcript changes.

`bounds2` is the value-range pass with relational facts (`a < b` from an
assertion lets it drop the range check on `b - a`); it does everything
`bounds` does. `simplify` runs again after a pass that leaves constants behind
for it to fold.
-/
import Damp.Optimize.Pass
import Damp.Optimize.Simplify
import Damp.Optimize.Bounds
import Damp.Optimize.Algebra
import Damp.Optimize.Asserts
import Damp.Optimize.Bounds2
import Damp.Optimize.Forward
import Damp.Optimize.FoldHashes
import Damp.Optimize.InlineAll
import Damp.Optimize.AssertEq
import Damp.Optimize.Commute
import Damp.Optimize.HashRanges
import Damp.Optimize.AssertZero
import Damp.Optimize.MergeChecks
import Damp.Optimize.ShareHashes
import Damp.Optimize.LedgerReuse
import Damp.Optimize.LedgerDeadStore
import Damp.Crypto.Prims

namespace Damp.IR

/-- The passes applied by default, first to last. -/
def defaultPasses : List Pass :=
  [Circuit.simplify, Circuit.foldDivmod, Circuit.bounds2, Circuit.simplify, Circuit.algebra, Circuit.commuteOpt]

/-- Every pass, first to last. -/
def fullPasses : List Pass :=
  [Circuit.simplify, Circuit.foldDivmod, Circuit.assertEq, Circuit.asserts, Circuit.mergeChecks, Circuit.simplify,
   Circuit.bounds2,
   Circuit.simplify, Circuit.algebra, Circuit.forwardOpt, Circuit.forwardAllOpt, Circuit.commuteOpt,
   Circuit.assertZero]

/-- `--O3`: fold hashes of constants with `p`, then every pass. -/
def maxPassesWith (p : Zkir.Prims) : List Pass :=
  Circuit.simplify :: Circuit.foldHashes p :: fullPasses

/-- Optimize a circuit. -/
def Circuit.optimize (c : Circuit) : Circuit := runPasses defaultPasses c

/-- Optimize a circuit with every pass. -/
def Circuit.optimizeFull (c : Circuit) : Circuit := runPasses fullPasses c

/-- Optimize a circuit with every pass, hashes of constants computed with `p`. -/
def Circuit.optimizeMaxWith (p : Zkir.Prims) (c : Circuit) : Circuit := runPasses (maxPassesWith p) c

/-- `--O3`: `maxPassesWith Crypto.prims`, then one hash for the two arms of
    a conditional (`shareSelects`, `shareGuarded`: sound for hash functions
    that refuse exactly the inputs that do not fit their alignment, as
    `Crypto.prims` does), then drop the range checks a later persistent hash
    implies (sound for hash functions that check their inputs' alignment). -/
def maxPasses : List Pass :=
  maxPassesWith Crypto.prims ++ [Circuit.shareSelects, Circuit.shareGuarded, Circuit.hashRanges]

/-- Optimize a circuit with every pass, hashes of constants computed with
    Damp's implementations of Midnight's hash functions (`--O3`). -/
def Circuit.optimizeMax (c : Circuit) : Circuit := runPasses maxPasses c

/-- `--ledger-opt`, run after a level's passes: rewrite the ledger statements
    themselves (`ledgerReuse`: reuse a value just read or written instead of
    reading it again; `ledgerDeadStore`: drop a write that a later write to the
    same cell overwrites). Not `Pass.Sound`: the circuit sends the ledger
    different Impact programs, so its public transcript and verifier key
    differ. Proved `Pass.SoundLedger` (`Damp/Proofs/Optimize/LedgerSound.lean`):
    against the Lean model of Midnight's VM, from a well-formed ledger state,
    the outputs, private transcript, private state and final ledger state are
    those of the original. -/
def ledgerPasses : List Pass := [Circuit.ledgerReuse, Circuit.ledgerDeadStore]

end Damp.IR
