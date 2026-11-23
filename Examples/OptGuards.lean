import Damp

/-! Checks on `Circuit.assertZero` (`assert (a == b)` as `constrain (a - b) zero`)
and `Circuit.mergeChecks` (a check repeated under complementary guards, merged),
both at `--O2` and `--O3`, run by the build. Both are proved sound for every
choice of hash functions (`Circuit.assertZero_sound`,
`Circuit.mergeChecks_sound`); the checks below show each rule firing, each side
condition blocking it, and that runs are unchanged on accepted and refused
inputs. -/
namespace Examples.OptGuards
open Damp Damp.IR

/-- A circuit with inputs `0..n-1`, a body and outputs. -/
private def mk (n : Nat) (body : List Stmt) (outputs : List Expr) : Circuit where
  name := "t"
  args := []
  inputs := (List.range n).map fun v => { name := s!"x{v}", var := v, range := none }
  body := body.toArray
  result := .tuple []
  outputs := outputs

def observe (c : Circuit) (inputs : List Fr) : Option (List Nat) :=
  (c.run Crypto.prims inputs [] []).map fun o => o.outputs.map (·.val)

/-- The checks of a circuit. -/
private def checks (c : Circuit) : List Stmt :=
  c.body.toList.filter fun | .assert .. | .constrain .. => true | _ => false

private def isConstrainZero : Stmt → Bool
  | .constrain _ .zero => true
  | _ => false

/-! ### `assert (a == b)` -/

private def eqConst := mk 1 [.assert (.eq (.var 0) (.const 5)) "five"] [.var 0]
private def eqZero := mk 1 [.assert (.eq (.const 0) (.var 0)) "zero"] [.var 0]
private def eqVars := mk 2 [.assert (.eq (.var 0) (.var 1)) "same"] [.var 0]

#guard (checks (Circuit.assertZero eqConst)).all isConstrainZero
#guard (checks (Circuit.assertZero eqVars)).all isConstrainZero
-- `x == 0` becomes `constrain x zero`, no arithmetic at all.
#guard match (checks (Circuit.assertZero eqZero)) with
  | [.constrain (.var 0) .zero] => true
  | _ => false
#guard observe (Circuit.assertZero eqConst) [5] == some [5]
#guard observe (Circuit.assertZero eqConst) [6] == none
#guard observe eqConst [6] == none
#guard observe (Circuit.assertZero eqVars) [7, 7] == some [7]
#guard observe (Circuit.assertZero eqVars) [7, 8] == none
-- A condition that is not an equality stays an `assert`.
#guard match checks (Circuit.assertZero (mk 1 [.assert (.var 0) "b"] [])) with
  | [.assert ..] => true
  | _ => false

/-! ### Checks under complementary guards -/

-- `if (b) { assert(x != y) } else { assert(y != x) }` with the range check
-- of `x as Uint<16>` in both arms, as the language flattens it: `n` is bound
-- to `select b 0 1`, the negation of `b`.
private def ne (a b : Expr) : Expr := .select (.eq a b) (.const 0) (.const 1)
private def both := mk 3
  [.constrain (.var 2) .bool,
   .bind 3 "n" (.select (.var 2) (.const 0) (.const 1)),
   .assert (.select (.var 2) (ne (.var 0) (.var 1)) (.const 1)) "same",
   .constrain (.select (.var 2) (.var 0) (.const 0)) (.bits 16),
   .assert (.select (.var 3) (ne (.var 1) (.var 0)) (.const 1)) "same",
   .constrain (.select (.var 3) (.var 0) (.const 0)) (.bits 16)]
  [.select (.var 2) (.var 0) (.var 1)]
-- Two checks fewer, and after `simplify` (`b` is known to be 0 or 1) the
-- merged ones are `assert (x != y)` and `constrain x (bits 16)`.
#guard (checks (Circuit.mergeChecks both)).length + 2 == (checks both).length
#guard match checks (Circuit.simplify (Circuit.mergeChecks both)) with
  | [.constrain (.var 2) .bool, .assert _ _, .constrain (.var 0) (.bits 16)] => true
  | _ => false
-- Same runs: accepted, refused by the assert in either arm, refused by the
-- range check in either arm.
#guard observe (Circuit.mergeChecks both) [3, 4, 1] == observe both [3, 4, 1]
#guard observe (Circuit.mergeChecks both) [3, 4, 0] == observe both [3, 4, 0]
#guard observe both [3, 4, 0] == some [4]
#guard observe (Circuit.mergeChecks both) [3, 3, 1] == none
#guard observe (Circuit.mergeChecks both) [3, 3, 0] == none
#guard observe (Circuit.mergeChecks both) [70000, 4, 1] == none
#guard observe (Circuit.mergeChecks both) [70000, 4, 0] == none
#guard observe both [70000, 4, 0] == none

-- A guard that is not 0 or 1 still fails the merged check: `select g c c`
-- keeps the condition's check.
private def noBool := mk 3
  [.bind 3 "n" (.select (.var 2) (.const 0) (.const 1)),
   .assert (.select (.var 2) (.var 0) (.const 1)) "a",
   .assert (.select (.var 3) (.var 0) (.const 1)) "a"]
  []
#guard (checks (Circuit.mergeChecks noBool)).length == 1
#guard observe noBool [1, 0, 2] == none
#guard observe (Circuit.mergeChecks noBool) [1, 0, 2] == none
#guard observe (Circuit.mergeChecks noBool) [1, 0, 1] == some []

-- Side condition: a variable of the second check rebound in between. On
-- `x0 = 70000, b = 0` the original fails at the second check, which reads
-- the old `x0`; merging would read it at the first place too, and the
-- rebinding makes that unsound in general. The pair is left alone.
private def rebound := mk 3
  [.bind 3 "n" (.select (.var 2) (.const 0) (.const 1)),
   .constrain (.select (.var 2) (.var 0) (.const 0)) (.bits 16),
   .bind 0 "x" (.const 1),
   .constrain (.select (.var 3) (.var 0) (.const 0)) (.bits 16)]
  []
#guard (checks (Circuit.mergeChecks rebound)).length == 2

-- Side condition: the guards are not known to be complementary.
private def unrelated := mk 4
  [.assert (.select (.var 2) (.var 0) (.const 1)) "a",
   .assert (.select (.var 3) (.var 0) (.const 1)) "a"]
  []
#guard (checks (Circuit.mergeChecks unrelated)).length == 2

-- A range check that 0 passes merges, whatever it is ...
private def belowTen := mk 3
  [.bind 3 "n" (.select (.var 2) (.const 0) (.const 1)),
   .constrain (.select (.var 2) (.var 0) (.const 0)) (.below 10 4),
   .constrain (.select (.var 3) (.var 0) (.const 0)) (.below 10 4)]
  []
#guard (checks (Circuit.mergeChecks belowTen)).length == 1
#guard observe (Circuit.mergeChecks belowTen) [12, 0, 0] == none
#guard observe belowTen [12, 0, 0] == none
-- ... but not one that 0 fails: when the guard is 0 the original checks 0
-- and fails, the merged check would check `x`.
private def zeroFails := mk 3
  [.bind 3 "n" (.select (.var 2) (.const 0) (.const 1)),
   .constrain (.select (.var 2) (.var 0) (.const 0)) (.below 0 4),
   .constrain (.select (.var 3) (.var 0) (.const 0)) (.below 0 4)]
  []
#guard !Range.holds 0 (.below 0 4)
#guard (checks (Circuit.mergeChecks zeroFails)).length == 2
-- Different ranges are not merged.
private def twoRanges := mk 3
  [.bind 3 "n" (.select (.var 2) (.const 0) (.const 1)),
   .constrain (.select (.var 2) (.var 0) (.const 0)) .bool,
   .constrain (.select (.var 3) (.var 0) (.const 0)) (.bits 8)]
  []
#guard (checks (Circuit.mergeChecks twoRanges)).length == 2

-- A long body: the pass visits each statement once and looks ahead from
-- checks only; 32 unrelated guarded checks stay.
private def chain : Circuit := mk 2
  ((List.range 32).map fun i => .assert (.select (.var 0) (.eq (.var 1) (.const (Int.ofNat i))) (.const 1)) "c")
  []
#guard (checks (Circuit.mergeChecks chain)).length == 32

/-! ### A contract (`assert_misc.myswitch`'s shape) -/

ledger
  round : Counter

circuit myswitch (x y : Field) (b : Boolean) : Field := do
  const r ← if% disclose b then do
      require (x !=. y) "same"
      round.increment (← (disclose x).toUint 65535)
      return x
    else do
      require (y !=. x) "same"
      round.increment (← (disclose x).toUint 65535)
      return y
  return r

contract optGuards

/-- Number of ZKIR instructions of the emitted circuit (0 if it cannot be emitted). -/
def size (c : Circuit) : Nat :=
  match Emit.circuit c with
  | .ok src => src.instructions.size
  | .error _ => 0

-- `--O2` merges the two `assert`s and the two range checks of `x`.
#guard size myswitch.circuit.optimizeFull + 3 ≤ size myswitch.circuit.optimize

end Examples.OptGuards
