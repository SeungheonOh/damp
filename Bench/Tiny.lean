import Damp

/-! `bench/compact/tiny.compact` (Compact's examples/tiny.compact). -/
namespace Bench.Tiny
open Damp

enum State where
  | unset
  | set

ledger
  authority : Cell (Bytes 32)
  value : Cell Field
  state : Cell State

witness secretKey : Bytes 32

circuit public_key (sk : Bytes 32) : Bytes 32 :=
  return disclose (persistentHash #v[Bytes.pad 32 "lares:tiny:pk:", sk])

constructor (v : Field) := do
  const sk ← secretKey
  authority.write (← public_key sk)
  value.write (disclose v)
  state.write State.set

def inState (s : State) : CircuitM Boolean :=
  return (← state.read) ==. s

circuit set (v : Field) : Unit := do
  require (← inState State.unset) "set: attempted to overwrite recorded value"
  const sk ← secretKey
  const apk ← public_key sk
  authority.write apk
  value.write (disclose v)
  state.write State.set

circuit get : Maybe Field := do
  return if (← inState State.set) then Maybe.some (← value.read) else Maybe.none

circuit clear : Unit := do
  require (← inState State.set) "clear: no value is currently recorded"
  const sk ← secretKey
  const apk ← public_key sk
  require (apk ==. (← authority.read)) "clear: attempted clear without proper authorization"
  authority.write (Bytes.zero 32)
  value.write 0
  state.write State.unset

contract tiny exports set get clear public_key

end Bench.Tiny
