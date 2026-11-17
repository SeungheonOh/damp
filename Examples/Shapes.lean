import Damp

/-! The Lean counterpart of `test/oracle/shapes.compact`: structures, vectors,
nested conditionals and a ledger map. -/
namespace Examples.Shapes
open Damp

struct Point where
  x : Field
  y : Uint8

ledger
  balances : Map Uint16 Field
  origin : Cell Point
  flag : Cell Boolean

witness pick : Point

circuit move (p : Point) (v : Vector Uint8 3) (on deep : Boolean) : Point := do
  let w := disclose (← pick)
  const s := v[0] + v[1] + v[2]
  if% disclose on then
    if% disclose deep then origin.write (disclose p)
    else flag.write (disclose (p.y <=. v[1]))
  origin.write (disclose ⟨p.x + w.x + s.toField, w.y⟩)
  origin.read

circuit pay (k : Uint16) (amt : Field) (a b : Uint8) : Field := do
  let k := disclose k
  let has ← balances.member k
  const cur ← if% has then balances.lookup k else pure 0
  balances.insert k (disclose (cur + amt))
  flag.write (disclose (a >. b ||. a >=. b &&. a !=. b))
  require (!.(← balances.isEmpty)) "empty"
  if% disclose a ==. 7 then balances.remove k
  return (← balances.size).toField

contract shapes

end Examples.Shapes
