import Damp

/-! The Lean counterpart of `test/oracle/counter.compact`. -/
namespace Examples.Counter
open Damp

ledger
  count : Counter
  total : Cell Field
  cap : Cell Uint32

witness delta : Uint 20

circuit bump (x : Uint16) (go stop : Boolean) : Uint64 := do
  if% disclose go then do
    count.increment (disclose x)
    if% !.(disclose stop) then total.write (disclose x).toField
    require (x <. 500) "too big"
  count.read

circuit arith (a b : Uint8) (f : Field) : Field := do
  let d := disclose (← delta)
  const s := a + b
  const p := a * b
  const m ← a.sub b
  const ok := a ==. b ||. a <. b &&. d <. 5
  cap.write (disclose (s + p + m)).widen
  require ok "nope"
  total.write (disclose (f - d.toField))
  total.read

contract counter

end Examples.Counter
