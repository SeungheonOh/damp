/-
Trying a pass and keeping its result only when it is better.

`Pass.choose f g better` runs both `f` and `g` on a circuit and keeps `f`'s
result when `better` prefers it to `g`'s, and `g`'s otherwise. The comparison
can be anything, such as the number of instructions the emitter produces: a
choice between two sound passes is sound whatever it is
(`Pass.Sound.choose` in `Damp/Proofs/Optimize/Choose.lean`). This is how a pass
that only sometimes pays (say, one that enables later rewrites but can also
cost sharing) is made never to make a circuit bigger.
-/
import Damp.Optimize.Pass

namespace Damp.IR

/-- `f c` when `better (f c) (g c)`, otherwise `g c`. -/
def Pass.choose (f g : Pass) (better : Circuit → Circuit → Bool) : Pass := fun c =>
  let a := f c
  let b := g c
  if better a b then a else b

end Damp.IR
