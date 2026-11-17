import Damp

/-! The Lean counterpart of `test/oracle/extras.compact`: enumerations, optional
values, a ledger set and commitments. -/
namespace Examples.Extras
open Damp

enum Phase where
  | idle
  | started
  | closed

ledger
  phase : Cell Phase
  seen : Set (Bytes 32)
  best : Cell (Maybe Uint16)
  commitment : Cell Field
  pc : Cell (Bytes 32)

witness nonce : Bytes 32

circuit advance (p : Phase) (id : Bytes 32) (bid : Maybe Uint16) (r : Field) : Phase := do
  require ((← phase.read) !=. Phase.closed) "closed"
  let id := disclose id
  require (!.(← seen.member id)) "seen"
  seen.insert id
  if% disclose (bid.isSome &&. bid.value >. 100) then best.write (disclose bid) else best.write .none
  commitment.write (transientCommit bid.value r)
  pc.write (persistentCommit r (← nonce))
  phase.write (disclose (select (p ==. Phase.idle) Phase.started p))
  if% (← seen.size) >. 3 then seen.remove id
  let empty ← seen.isEmpty
  let ok ← if% empty then (do return (← best.read) ==. Maybe.some 7) else pure .true
  require ok "x"
  phase.read

contract extras

end Examples.Extras
