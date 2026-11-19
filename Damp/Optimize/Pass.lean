/-
What a pass is: a rewrite of a circuit. The passes are the other files of this
directory; `Damp/Optimize/Pipeline.lean` puts them in order.
-/
import Damp.IR.Basic

namespace Damp.IR

/-- A pass: a rewrite of a circuit. -/
abbrev Pass := Circuit → Circuit

/-- Apply passes in order. -/
def runPasses (ps : List Pass) (c : Circuit) : Circuit := ps.foldl (fun c p => p c) c

end Damp.IR
