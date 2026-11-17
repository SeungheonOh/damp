import Damp

/-! The Lean counterpart of `test/oracle/bytes.compact`: byte strings and the
persistent hash. -/
namespace Examples.Bytes
open Damp

ledger
  owner : Cell (Bytes 32)
  tag : Cell (Bytes 8)
  wide : Cell (Bytes 64)

witness secret : Bytes 32

circuit claim (who : Bytes 32) (t : Bytes 8) (on : Boolean) : Bytes 32 := do
  let s ← secret
  const h := disclose (persistentHash s)
  require (h ==. (← owner.read) ||. who ==. Bytes.pad 32 "admin") "not owner"
  if% disclose on then tag.write (disclose t)
  owner.write (disclose (persistentHash (who, h)))
  owner.read

circuit store (w : Bytes 64) (f : Field) : Bytes 64 := do
  const d := persistentHash (f, w)
  require (d !=. (← owner.read)) "collision"
  wide.write (disclose w)
  wide.read

contract bytes

end Examples.Bytes
