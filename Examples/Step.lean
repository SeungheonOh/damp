import Damp

/-! The Lean counterpart of `test/oracle/step.compact`. -/
namespace Examples.Step
open Damp

ledger
  total : Cell Field

witness hint : Uint 9

circuit step (a : Field) (b : Boolean) (n : Uint16) : Field := do
  const h ← if% b then hint else pure 0
  const r := a * a + h.toField - transientHash a
  total.write (disclose r)
  require (n <. 1000) "n too big"
  return disclose r

contract step

end Examples.Step
