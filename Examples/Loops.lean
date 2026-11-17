import Damp

/-! The Lean counterpart of `test/oracle/loops.compact`: plain `if`, `let mut`
and `for`, all of which are ordinary Lean and unroll when the definition is
evaluated. -/
namespace Examples.Loops
open Damp

ledger
  sum : Cell Field
  hits : Counter

circuit tally (v : Vector Field 4) (on : Vector Boolean 4) (limit : Uint8) : Field := do
  let mut acc : Field := 0
  for i in [0:4] do
    if on[i]! then acc := acc + v[i]!
  -- Compute the total here; a plain `let` would be computed at its first use.
  const total := acc
  if% disclose limit <. 10 then hits.increment 1 else sum.write (disclose total)
  -- An ordinary Lean `if`, decided while the circuit is being built.
  if v.size = 4 then sum.write (disclose (total * total))
  sum.read

contract loops

end Examples.Loops
