/-
Soundness of `Circuit.forwardAllOpt` (`Damp/Optimize/InlineAll.lean`).
-/
import Damp.Optimize.InlineAll
import Damp.Proofs.Optimize.Forward
import Damp.Proofs.Optimize.Choose

namespace Damp.IR

/-- `forwardAll` followed by `algebra` and `simplify`, kept only when smaller, is sound. -/
theorem Circuit.forwardAllOpt_sound : Pass.Sound Circuit.forwardAllOpt :=
  Pass.Sound.choose
    (Pass.Sound.comp (Pass.Sound.comp Circuit.forwardAll_sound Circuit.algebra_sound) Circuit.simplify_sound)
    Pass.Sound.id _

end Damp.IR
