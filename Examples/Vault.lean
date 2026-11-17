import Damp

/-! The Lean counterpart of `test/oracle/vault.compact`: a constructor, and an
exported circuit that needs no proof because it never touches the ledger. -/
namespace Examples.Vault
open Damp

ledger
  owner : Cell (Bytes 32)
  limit : Cell Uint32
  spent : Counter

witness key : Bytes 32

constructor (o : Bytes 32) (l : Uint32) := do
  owner.write (disclose o)
  limit.write (disclose l)

circuit spend (amount : Uint16) : Unit := do
  const h := disclose (persistentHash (← key))
  require (h ==. (← owner.read)) "not owner"
  spent.increment (disclose amount)
  require ((← spent.read) <=. (← limit.read)) "over limit"

circuit digest (x y : Field) : Field := do
  return transientHash (x, y)

contract vault

end Examples.Vault
