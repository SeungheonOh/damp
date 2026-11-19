import Damp

/-! `bench/compact/adt_map_list.compact` (Compact's examples/adt/tests/map_field_list_field.compact):
a map whose values are ledger lists. -/
namespace Bench.AdtMapList
open Damp

ledger
  c : Map Field (LedgerList Field)

circuit test : Unit := do
  require ((← c.isEmpty) ==. .true) "Structure should be empty"
  require ((← c.size) ==. 0) "Size should be 0"
  c.insertDefault 0
  require ((← c.size) ==. 1) "Size should be 1"
  require ((← (← c.lookup 0).length) ==. 0) "Key 0 should have value 1"
  c.insertDefault 1
  require ((← c.size) ==. 2) "Size should be 2"
  require ((← (← c.lookup 1).length) ==. 0) "Key 1 should have value 0"
  require ((← c.member 1) ==. .true) "Key 1 should be member"
  c.remove 0
  require ((← c.size) ==. 1) "Size should be 1"
  c.resetToDefault
  require ((← c.size) ==. 0) "Size should be 0"
  require ((← c.isEmpty) ==. .true) "Structure should be empty"

contract adt_map_list

end Bench.AdtMapList
