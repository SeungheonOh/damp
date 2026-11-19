import Damp

/-! `bench/compact/pm_19287.compact` (Compact's examples/bugs/pm-19287.compact): loops over
vectors and matrices returned by helper circuits, accumulating into ledger fields. Compact's
`for (const x of v)` is a Lean `for` over the vector's elements. -/
namespace Bench.Pm19287
open Damp

ledger
  circuit_vector_sum : Cell Field
  tuple_element_count : Cell Uint16
  nested_circuit_calls : Cell Field
  dynamic_vector_processing : Map Field Field
  matrix_iteration_result : Cell Field
  recursive_circuit_sum : Cell Field
  concat_sum : Cell Field
  complex_sum : Cell Field
  conditional_result : Cell Field
  slicing_sum : Cell Field
  current_vector : Cell (Vector Field 3)

constructor := do
  circuit_vector_sum.write 0
  tuple_element_count.write 0
  nested_circuit_calls.write 0
  matrix_iteration_result.write 0
  recursive_circuit_sum.write 0
  complex_sum.write 0
  concat_sum.write 0
  conditional_result.write 0
  slicing_sum.write 0
  current_vector.write #v[0, 0, 0]

def generateTestVector (size : Uint8) : Vector Field 5 :=
  select (size.widen (k := 65535) ==. 5) #v[100, 200, 300, 400, 500] #v[10, 20, 30, 40, 50]

def generateTupleData : Field × Uint32 × Boolean × Field := (42, 100, .true, 256)

def createMatrix : Vector (Vector Field 2) 3 := #v[#v[1, 5], #v[2, 6], #v[3, 7]]

def transformVector (input : Vector Field 3) : Vector Field 3 :=
  #v[input[0] * 2, input[1] + 10, input[2] - 5]

def addTo (c : Cell Field) (x : Field) : CircuitM Unit := do
  c.write ((← c.read) + x)

circuit test_circuit_returned_vector : Field := do
  circuit_vector_sum.write 0
  for value in (generateTestVector 5).toList do
    addTo circuit_vector_sum value
  circuit_vector_sum.read

def bump : CircuitM Unit := do
  tuple_element_count.write (← ((← tuple_element_count.read) + (1 : Uint 1)).castTo 65535)

circuit test_circuit_returned_tuple : Uint16 := do
  tuple_element_count.write 0
  let (fieldVal, uintVal, boolVal, fieldVal2) := generateTupleData
  if% (← fieldVal.toUint (2 ^ 64 - 1)) >. 50 then do
    bump
  if% (uintVal.widen (k := 2 ^ 64 - 1)) >. 50 then do
    bump
  if% boolVal &&. ((1 : Uint 1) >. 50) then do
    bump
  if% (← fieldVal2.toUint (2 ^ 64 - 1)) >. 50 then do
    bump
  tuple_element_count.read

circuit test_nested_circuit_matrix : Field := do
  matrix_iteration_result.write 0
  const matrix := createMatrix
  for row in matrix.toList do
    for cell in row.toList do
      addTo matrix_iteration_result cell
  matrix_iteration_result.read

circuit test_circuit_calls_in_loop : Field := do
  nested_circuit_calls.write 0
  const baseValues : Vector Field 3 := #v[1, 2, 3]
  for base in baseValues.toList do
    const transformed := transformVector #v[base, base * 2, base * 3]
    for result in transformed.toList do
      addTo nested_circuit_calls result
  nested_circuit_calls.read

circuit test_dynamic_vector_processing : Field := do
  for multiplier in [(1 : Uint8), 2, 3, 4, 5] do
    const generated := generateTestVector multiplier
    complex_sum.write 0
    for v in generated.toList do
      addTo complex_sum v
    dynamic_vector_processing.insert multiplier.toField (← complex_sum.read)
  dynamic_vector_processing.lookup 3

circuit test_complex_nested_patterns : Field := do
  complex_sum.write 0
  const matrices : Vector (Vector (Vector Field 2) 3) 2 := #v[createMatrix, createMatrix]
  for matrix in matrices.toList do
    for row in matrix.toList do
      const transformedRow := transformVector #v[row[0], row[1], row[0] + row[1]]
      for tv in transformedRow.toList do
        if% (← tv.toUint (2 ^ 64 - 1)) >. 10 then addTo complex_sum tv
  complex_sum.read

circuit test_concatenated_circuit_results : Field := do
  concat_sum.write 0
  const vec1 := generateTestVector 5
  const vec2 := generateTestVector 3
  for value in vec1.toList ++ vec2.toList do
    addTo concat_sum value
  concat_sum.read

circuit test_conditional_circuit_calls : Field := do
  conditional_result.write 0
  for condition in [Boolean.true, .false, .true, .false] do
    const vec := select condition (generateTestVector 5) (generateTestVector 3)
    for v in [vec[0], vec[1], vec[2]] do
      addTo conditional_result v
  conditional_result.read

circuit test_recursive_style_processing : Field := do
  recursive_circuit_sum.write 0
  current_vector.write #v[1, 2, 3]
  for _ in [1, 2, 3] do
    const processed := transformVector (← current_vector.read)
    for v in processed.toList do
      addTo recursive_circuit_sum v
    current_vector.write processed
  recursive_circuit_sum.read

circuit test_vector_slicing_with_circuits : Field := do
  slicing_sum.write 0
  const fullVector := generateTestVector 5
  for element in [fullVector[0], fullVector[2], fullVector[4]] do
    addTo slicing_sum element
  let (tupleField1, _, _, tupleField2) := generateTupleData
  slicing_sum.write ((← slicing_sum.read) + tupleField1 + tupleField2)
  slicing_sum.read

circuit test : Vector Field 10 := do
  const test1 ← test_circuit_returned_vector
  const test2 ← test_circuit_returned_tuple
  const test3 ← test_nested_circuit_matrix
  const test4 ← test_circuit_calls_in_loop
  const test5 ← test_dynamic_vector_processing
  const test6 ← test_complex_nested_patterns
  const _test7 ← test_concatenated_circuit_results
  const test8 ← test_conditional_circuit_calls
  const test9 ← test_recursive_style_processing
  const test10 ← test_vector_slicing_with_circuits
  return #v[test1, test2.toField, test3, test4, test5, test6, (0 : Field), test8, test9, test10]

contract pm_19287

end Bench.Pm19287
