import Damp

/-! `bench/compact/vectors.compact` (ledger-touching circuits of Compact's
examples/vectors/spread_part_one.compact, and a `slice`). A spread is a Lean vector built from
the pieces; a loop over `0..100` is an unrolled Lean loop. -/
namespace Bench.Vectors
open Damp

ledger
  var1 : Cell (Vector Field 2)
  var1a : Cell (Vector Field 3)
  var2 : Map Field (Vector Uint32 10)
  var4 : Map Field Field

circuit test1b (vector1 vector2 : Vector Field 1) : Unit := do
  var1.write (disclose #v[vector1[0], vector2[0]])
  var1a.write (disclose #v[vector1[0], vector2[0], 1])

circuit test2 (vector1 : Vector Uint8 2) (vector2 : Vector Uint16 2) : Unit := do
  const v1 := disclose vector1
  const v2 := disclose vector2
  const a : Vector Uint32 10 :=
    #v[1, 2, 3, 4, 5, v1[0].widen, v1[1].widen, v2[0].widen, v2[1].widen, 0]
  var2.insert 1 a
  const looked ← var2.lookup 1
  for i in looked.toList do
    const _x := i

circuit test4 : Unit := do
  for i in [0:100] do
    var4.insert (Field.ofNat i) (Field.ofNat i)

circuit slice_to_ledger (vector : Vector Field 8) : Unit := do
  var1.write (disclose #v[vector[3], vector[4]])

contract vectors

end Bench.Vectors
