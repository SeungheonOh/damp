import Damp

/-! The Lean counterpart of `test/oracle/notes.compact`: a witness that returns
nothing. The circuit places no constraint for it, but the executor still runs
it when its guard holds, because such a witness exists to update the user's
private state. -/
namespace Examples.Notes
open Damp

ledger
  total : Cell Field

witness note (x : Field) : Unit

circuit save (a b : Field) (on : Boolean) : Unit := do
  if% on then note a
  note b
  total.write (disclose a)

contract notes

end Examples.Notes
