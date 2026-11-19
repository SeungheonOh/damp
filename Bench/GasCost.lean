import Damp

/-! `bench/compact/gas_cost.compact` (Compact's test-center/compact/gas-cost.compact). -/
namespace Bench.GasCost
open Damp

ledger
  setA : Set Field
  setB : Set Field

constructor := do
  setA.insert 10

circuit testGasCost : Unit := do
  setA.remove 10
  setB.insert 10

contract gas_cost

end Bench.GasCost
