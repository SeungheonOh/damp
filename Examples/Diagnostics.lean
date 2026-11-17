import Damp

/-! Mistakes that are caught where the circuit is written. -/
namespace Examples.Diagnostics
open Damp

ledger
  total : Cell Field
  hits : Counter

/-- error: circuit cannot be compiled: `break` under a circuit condition is not supported -/
#guard_msgs in
circuit stopEarly (v : Vector Field 3) (stop : Boolean) : Field := do
  let mut acc : Field := 0
  for i in [0:3] do
    if stop then break
    acc := acc + v[i]!
  return acc

/--
error: circuit cannot be compiled: both branches of an `if` end with the same ledger operation (48 80 1 1 0 12 1 -2 _). In a `do` block the statements after an `if` are built once per branch: write `if% … then … else …` for a conditional with statements after it, or move the shared operation out of the `if`
-/
#guard_msgs in
circuit twice (x : Field) (on : Boolean) : Field := do
  if disclose on then total.write (disclose x)
  total.read

/--
error: circuit cannot be compiled: the literal 70000 does not fit a Uint whose maximum is 65535
-/
#guard_msgs in
circuit tooBig (x : Field) : Field := do
  hits.increment 70000
  return x

-- The same circuit, written so the read is built once.
circuit once (x : Field) (on : Boolean) : Field := do
  if% disclose on then total.write (disclose x)
  total.read

-- An ordinary Lean condition is unaffected: it is decided while the circuit is built.
circuit static (x : Field) : Field := do
  if 2 + 2 = 4 then total.write (disclose x)
  total.read

witness secret : Field

/--
error: circuit cannot be compiled: a ledger operation stores or looks up a value that depends on argument `x`, the result of witness `secret`. If making it public is intended, wrap it in `disclose`
-/
#guard_msgs in
circuit leak (x : Field) : Field := do
  total.write (x + (← secret))
  total.read

/--
error: circuit cannot be compiled: whether a ledger operation runs depends on argument `on`. If making it public is intended, wrap it in `disclose`
-/
#guard_msgs in
circuit leakByBranch (on : Boolean) : Field := do
  if% on then hits.increment 1
  total.read

/--
error: circuit cannot be compiled: the circuit returns a value that depends on the result of witness `secret`. If making it public is intended, wrap it in `disclose`
-/
#guard_msgs in
circuit leakByReturn (x : Field) : Field := do
  return x * (← secret)

/-- info: once: 9 instructions, 2 inputs, 1 outputs
  0 private inputs, 1 ledger reads, 6 ledger instructions, 0 asserts, 0 hashes -/
#guard_msgs in
#circuit_info once

end Examples.Diagnostics
