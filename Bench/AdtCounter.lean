import Damp

/-! `bench/compact/adt_counter.compact` (Compact's examples/adt/tests/counter.compact). -/
namespace Bench.AdtCounter
open Damp

ledger
  c : Counter
  c2 : Counter

circuit test_all : Unit := do
  require ((← c.read) ==. 0) "Initial value is 0"
  c.resetToDefault
  require ((← c.read) ==. 0) "Value is 0"
  c.increment 5
  require ((← c.read) ==. 5) "Value is 5"
  c.decrement 4
  require ((← c.read) ==. 1) "Value is 1"
  c.resetToDefault
  require ((← c.read) ==. 0) "Value is 0"

circuit test_big_increment : Unit := do
  require ((← c2.read) ==. 0) "Initial value is 0"
  c2.increment 4096
  c2.decrement 4
  require ((← c2.read) ==. 4092) "Value is as defined"

contract adt_counter

end Bench.AdtCounter
