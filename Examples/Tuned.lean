import Damp

/-! A contract with settings fixed at compile time, to show what the optimizer
removes. It has no Compact counterpart; `test/opt.sh` checks that the optimized
and unoptimized circuits behave the same and reports their sizes. -/
namespace Examples.Tuned
open Damp

/-- Settings chosen when the contract is compiled. Ordinary Lean data. -/
structure Config where
  weights : List Nat
  audit : Bool
  cap : Nat

def config : Config := { weights := [1, 0, 2, 1], audit := false, cap := 5000 }

ledger
  total : Cell Field
  runs : Counter
  log : Cell Field

circuit settle (amounts : Vector Uint16 4) (vip : Boolean) : Field := do
  let amounts := disclose amounts
  let vip := disclose vip
  let mut sum : Field := 0
  for i in [0:4] do
    -- A weight of 1 costs no multiplication; a weight of 0 costs nothing at all.
    sum := sum + (amounts[i]!).toField * Field.ofNat (config.weights[i]!)
  -- Decided at compile time: the check disappears, and so does the audit write.
  require (Boolean.ofBool (config.cap > 0)) "cap must be positive"
  if% Boolean.ofBool config.audit then log.write sum
  -- The same range check twice is made once.
  let a ← amounts[0].toField.toUint 65535
  let b ← amounts[0].toField.toUint 65535
  -- `vip && true` is just `vip`.
  let bonus := vip &&. Boolean.ofBool (config.cap > 0)
  total.write (select bonus (sum + a.toField + b.toField) sum)
  runs.increment 1
  total.read

contract tuned

end Examples.Tuned
