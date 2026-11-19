import Damp

/-! `bench/compact/types.compact` (the ledger-touching circuits of Compact's
examples/types/examples.compact). Type aliases are Lean abbreviations. -/
namespace Bench.Types
open Damp

abbrev f10 := Field
abbrev vector_10_f10 := Vector f10 10

ledger
  t10_map_map : Map f10 (Map f10 f10)
  t10_map : Map f10 vector_10_f10
  t16_sum_of_fields : Map Field Field

circuit test10a (vara : f10) : Boolean := do
  t10_map_map.insertDefault (disclose vara)
  t10_map_map.member (disclose vara)

circuit test10 (vara : f10) (varb : vector_10_f10) : Boolean := do
  t10_map.insert (disclose vara) (disclose varb)
  t10_map.member (disclose vara)

circuit test16 (vara : Vector Field 10) : Field := do
  for a in (disclose vara).toList do
    const sum := a + a + 1
    t16_sum_of_fields.insert a sum
  t16_sum_of_fields.lookup 0

contract types

end Bench.Types
