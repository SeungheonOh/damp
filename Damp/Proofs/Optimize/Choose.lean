/-
Soundness of `Pass.choose` (`Damp/Optimize/Choose.lean`): a choice between
two sound passes is sound, whatever decides it.
-/
import Damp.Optimize.Choose
import Damp.Proofs.Optimize.Sound

namespace Damp.IR

/-- Choosing, by any criterion, between the results of two sound passes is a
    sound pass. -/
theorem Pass.Sound.choose {f g : Pass} (hf : Pass.Sound f) (hg : Pass.Sound g)
    (better : Circuit → Circuit → Bool) : Pass.Sound (Pass.choose f g better) where
  run p c inputs priv pub := by
    simp only [Pass.choose]
    split
    · exact hf.run p c inputs priv pub
    · exact hg.run p c inputs priv pub
  exec p O c inputs private_ ledger := by
    simp only [Pass.choose]
    split
    · exact hf.exec p O c inputs private_ ledger
    · exact hg.exec p O c inputs private_ ledger

end Damp.IR
