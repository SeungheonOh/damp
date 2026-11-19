import Damp

/-! `bench/compact/threading.compact` (Compact's test-center/compact/threading.compact):
two circuits walking a Fibonacci sequence kept by a counter. -/
namespace Bench.Threading
open Damp

ledger
  counter : Counter

constructor := do
  counter.resetToDefault

witness num (n : Field) : Field

circuit fib (c0 : Field) : Field := do
  const c := disclose c0
  if% c ==. 1 &&. (← counter.read) !=. 0 then do
    counter.resetToDefault
    counter.increment 1
  else do
    require (c ==. (← counter.read).toField + 1) "invalid fib num requested"
    counter.increment 1
  const a ← num c
  const b ← num ((← counter.read).toField - 1)
  return disclose (a + b)

circuit fib2 (reset : Boolean) : Field := do
  if% disclose reset then counter.resetToDefault else counter.increment 1
  return disclose (← num (← counter.read).toField)

contract threading

end Bench.Threading
