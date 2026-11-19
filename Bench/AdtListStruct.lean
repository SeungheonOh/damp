import Damp

/-! `bench/compact/adt_list_struct.compact` (Compact's examples/adt/tests/list_struct.compact):
a ledger list of a structure that holds coins. -/
namespace Bench.AdtListStruct
open Damp

struct Complex where
  boolean : Boolean
  bytes : Bytes 32
  field : Field
  uint : Uint64
  vector : Vector Field 2
  coin : ShieldedCoinInfo
  qcoin : QualifiedShieldedCoinInfo

ledger
  c : LedgerList Complex

def construct (bool : Boolean) : Complex :=
  let coinInfo : ShieldedCoinInfo := ⟨Bytes.pad 32 "nonce", Bytes.pad 32 "color", 1⟩
  { boolean := bool
    bytes := Bytes.pad 32 "some"
    field := (42 : Field) * 42 * 42
    uint := 1234567890
    vector := #v[8, (128 : Field) * 128]
    coin := coinInfo
    qcoin := ⟨Bytes.pad 32 "nonce", Bytes.pad 32 "color", 9, 8⟩ }

circuit test : Unit := do
  const complex := construct .true
  const complex2 := construct .false
  require ((← c.isEmpty) ==. .true) "Structure should be empty"
  require ((← c.length) ==. 0) "Size should be 0"
  require ((← c.head).isSome ==. .false) "Head should not exist"
  c.pushFront complex
  require ((← c.length) ==. 1) "Size should be 1"
  require ((← c.head).isSome ==. .true) "Head should exist"
  require ((← c.head).value ==. complex) "Head should have value 0"
  c.pushFront complex2
  require ((← c.length) ==. 2) "Size should be 2"
  require ((← c.head).isSome ==. .true) "Head should exist"
  require ((← c.head).value ==. complex2) "Head should have value 1"
  c.popFront
  require ((← c.length) ==. 1) "Size should be 2"
  require ((← c.head).isSome ==. .true) "Head should exist"
  require ((← c.head).value ==. complex) "Head should have value 0"
  c.resetToDefault

contract adt_list_struct

end Bench.AdtListStruct
