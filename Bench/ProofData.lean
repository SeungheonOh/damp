import Damp

/-! `bench/compact/proof_data.compact` (Compact's examples/casts/proof_data.compact, unchanged):
`Bytes<5>` and `Vector<5, Uint<8>>` read from the ledger and cast to each other. -/
namespace Bench.ProofData
open Damp

ledger
  param1 : Cell (Bytes 5)
  param2 : Cell (Vector Uint8 5)

circuit test1 : Vector Uint8 5 := do
  return (← param1.read).toVector

circuit test2 : Bytes 5 := do
  return Bytes.ofVector (← param2.read)

contract proof_data

end Bench.ProofData
