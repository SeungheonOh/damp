import Damp

/-! `bench/compact/zkir_generation.compact` (Compact's examples/casts/zkir_generation.compact,
unchanged): `Vector<n, Uint<8>>` and `Bytes<n>` cast to each other around a ledger write and a
counter. -/
namespace Bench.ZkirGeneration
open Damp

ledger
  round : Counter
  val1 : Cell (Bytes 10)

circuit increment : Unit := round.increment 1

circuit test1 (param1 : Vector Uint8 10) : Bytes 10 := do
  val1.write (Bytes.ofVector (disclose param1))
  val1.read

circuit test2 (param1 : Vector Uint8 1) : Unit := do
  round.increment (disclose param1[0]).widen
  const p := Bytes.ofVector param1
  round.increment ((disclose p).toVector[0]).widen

contract zkir_generation

end Bench.ZkirGeneration
