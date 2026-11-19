import Damp

/-! `bench/compact/pm_20028.compact` (Compact's examples/bugs/pm-20028/examples.compact):
`Uint<248>` values, casts down and up, comparisons across widths. `test10` (a circuit
returning `Uint<0>`, no ledger) and the module-based `test3` are left out. -/
namespace Bench.Pm20028
open Damp

abbrev Uint248 := Uint (2 ^ 248 - 1)
abbrev Uint247 := Uint (2 ^ 247 - 1)
abbrev Uint128' := Uint (2 ^ 128 - 1)

ledger
  var_field1 : Cell Field
  var_uint2 : Cell Uint248
  var_test4a : Cell Uint248
  var_test4b : Cell Uint248
  var_test5 : Cell Uint248
  var_test6 : Cell Uint248
  var_test7a : Cell Uint248
  var_test7b : Cell Uint64
  var_test8a : Cell Uint247
  var_test8b : Cell Uint247
  var_test9a : Cell Uint248
  var_test9b : Cell Uint248

circuit test1 : Uint248 := do
  var_field1.write 1
  return 1

circuit test2 : Field := do
  var_uint2.write 1
  return 1

circuit test4 (a b : Uint248) : Field := do
  var_test4a.write (disclose a)
  var_test4b.write (disclose b)
  return a.toField + b.toField

circuit test5 : Uint248 := do
  const maxWidth : Uint248 := 123456789
  const down128 ← maxWidth.castTo (2 ^ 128 - 1)
  const down64 ← down128.castTo (2 ^ 64 - 1)
  const down32 ← down64.castTo (2 ^ 32 - 1)
  const up128 ← down32.castTo (2 ^ 128 - 1)
  const back248 ← up128.castTo (2 ^ 248 - 1)
  var_test5.write back248
  var_test5.read

circuit test6 : Uint248 := do
  var_test6.write (Value.zero Uint248)
  var_test6.read

circuit test_cast_comparison : Boolean := do
  var_test7a.write 1
  var_test7b.write 1
  require ((← var_test7a.read) ==. (← var_test7b.read)) "Equal !"
  return (← var_test7a.read) ==. (← var_test7b.read)

circuit test8 : Uint248 := do
  var_test8a.write (Value.zero Uint247)
  var_test8b.write 1
  return ((← var_test8a.read) + (← var_test8b.read)).widen

circuit test9 : Uint248 := do
  var_test9a.write (Value.zero Uint248)
  var_test9b.write (Value.zero Uint248)
  (← var_test9a.read).sub (← var_test9b.read)

contract pm_20028

end Bench.Pm20028
