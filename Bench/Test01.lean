import Damp

/-! `bench/compact/test01.compact` (Compact's test-center/compact/test01.compact, a copy of
tiny.compact with some arithmetic in `set`; see the header of the Compact file for two changes). -/
namespace Bench.Test01
open Damp

enum STATE where
  | unset
  | set

ledger
  authority : Cell (Bytes 32)
  value : Cell Field
  state : Cell STATE

witness secretKey : Bytes 32

circuit public_key (sk : Bytes 32) : Bytes 32 :=
  return disclose (persistentHash #v[Bytes.pad 32 "lares:tiny:pk:", sk])

constructor (v : Field) := do
  const sk ← secretKey
  authority.write (← public_key sk)
  value.write (disclose v)
  state.write STATE.set

def inState (s : STATE) : CircuitM Boolean :=
  return (← state.read) ==. s

circuit set (v : Field) (temp : Field) : Unit := do
  require (← inState STATE.unset) "set: attempted to overwrite recorded value"
  const sk ← secretKey
  const apk ← public_key sk
  authority.write apk
  value.write ((disclose v + 1 - 1) * 2)
  if% (← (disclose v).toUint 65535) <. 10 then
    state.write STATE.set
  else
    if% temp + 2 !=. 5 then require Boolean.false "oops 1"

circuit get : Maybe Field := do
  return if (← inState STATE.set) then Maybe.some (← value.read) else Maybe.none

circuit clear : Unit := do
  require (← inState STATE.set) "clear: no value is currently recorded"
  const sk ← secretKey
  const apk ← public_key sk
  require (apk ==. (← authority.read)) "clear: attempted clear without proper authorization"
  authority.write (Bytes.zero 32)
  value.write 0
  state.write STATE.unset

contract test01 exports set get clear public_key

end Bench.Test01
