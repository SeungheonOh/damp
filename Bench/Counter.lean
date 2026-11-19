import Damp

/-! `bench/compact/counter.compact` (Compact's examples/counter.compact). -/
namespace Bench.Counter
open Damp

ledger
  round : Counter

circuit increment : Unit := do
  round.increment 1

contract counter

end Bench.Counter
