import Damp
import Damp.Optimize.Bounds

/-! Checks on the value-range pass (`Damp/Optimize/Bounds.lean`), proved sound in
`Damp/Proofs/Optimize/Bounds.lean` (`Circuit.bounds_sound`). Each rule fires
where the derived bounds decide it, and each side condition blocks it where the
rewrite would change which runs succeed; the comments give the run that the
naive rewrite would get wrong. -/
namespace Examples.OptBounds
open Damp Damp.IR

def prims : Zkir.Prims where
  transientHash xs := xs.foldl (· + ·) 0
  persistentHash _ xs := some (List.replicate 32 (xs.length % 256))
  transientCommit xs r := xs.foldl (· + ·) r

/-- A circuit with inputs `0..n-1` (no input checks), a body and outputs. -/
private def mk (n : Nat) (body : List Stmt) (outputs : List Expr := []) : Circuit where
  name := "t"
  args := []
  inputs := (List.range n).map fun v => { name := s!"x{v}", var := v, range := none }
  body := body.toArray
  result := .tuple []
  outputs := outputs

def observe (c : Circuit) (inputs priv pub : List Fr) : Option (List Nat × List (List Nat)) :=
  (c.run prims inputs priv pub).map fun o =>
    (o.outputs.map (·.val), (o.groups.filter (·.active)).map fun g => g.vals.map (·.val))

/-- The pass does not change this run. -/
def agrees (c : Circuit) (inputs : List Fr) (priv : List Fr := []) : Bool :=
  observe c inputs priv [] == observe c.bounds inputs priv []

/-- The run fails, before and after the pass. -/
def rejects (c : Circuit) (inputs : List Fr) (priv : List Fr := []) : Bool :=
  (observe c inputs priv []).isNone && agrees c inputs priv

/-- The number of statements left after the pass. -/
def size (c : Circuit) : Nat := c.bounds.body.size

private def x : Expr := .var 0
private def y : Expr := .var 1
private def z : Expr := .var 2

/-! ### Rule 1: range checks implied by the bounds -/

-- `x + y` of two bytes is below 2^9.
private def sum9 := mk 2 [.constrain x (.bits 8), .constrain y (.bits 8), .constrain (.add x y) (.bits 9)]
#guard size sum9 == 2
#guard agrees sum9 [255, 255] && rejects sum9 [256, 0]
-- ... but not below 2^8: kept, and it fails for 200 + 100.
private def sum8 := mk 2 [.constrain x (.bits 8), .constrain y (.bits 8), .constrain (.add x y) (.bits 8)]
#guard size sum8 == 3
#guard rejects sum8 [200, 100] && agrees sum8 [100, 100]
-- Without bounds on the operands nothing is known: x = 600 fails the check.
private def sumFree := mk 2 [.constrain (.add x y) (.bits 9)]
#guard size sumFree == 1
#guard rejects sumFree [600, 0]
-- A product that could wrap around the field has no bound: 2^200 · 2^200 wraps.
private def mulWrap := mk 1 [.constrain x (.bits 200), .constrain (.mul x x) (.bits 254)]
#guard size mulWrap == 2
-- A product that cannot wrap: a byte times a byte is below 2^16.
private def mul16 := mk 2 [.constrain x (.bits 8), .constrain y (.bits 8), .constrain (.mul x y) (.bits 16)]
#guard size mul16 == 2
#guard agrees mul16 [255, 255]
-- `below b w` needs `b` to fit `w`: `below 300 8` never passes, so it stays.
private def belowWide := mk 1 [.constrain x (.bits 8), .constrain x (.below 300 8)]
#guard size belowWide == 2
#guard rejects belowWide [3]
private def belowOk := mk 1 [.constrain x (.bits 8), .constrain x (.below 300 10)]
#guard size belowOk == 1
-- A width of 255 bits or more never passes: kept.
private def bits255 := mk 1 [.constrain x (.bits 8), .constrain x (.bits 255)]
#guard size bits255 == 2
#guard rejects bits255 [3]
-- The value must certainly exist: a comparison whose operand does not fit its
-- width fails, though its value would be a boolean. Dropping the check would
-- accept x0 = 300.
private def ltFail := mk 2 [.constrain y (.bits 8), .constrain (.lt 8 x y) .bool]
#guard size ltFail == 2
#guard rejects ltFail [300, 1]
#guard (observe (mk 2 [.constrain y (.bits 8)]) [300, 1] [] []).isSome
-- With both operands bounded the comparison cannot fail, and the check goes.
private def ltOk := mk 2 [.constrain x (.bits 8), .constrain y (.bits 8), .constrain (.lt 8 x y) .bool]
#guard size ltOk == 2
#guard agrees ltOk [3, 9] && agrees ltOk [9, 3] && rejects ltOk [300, 3]
-- A conditional on a value not known to be 0 or 1 fails: z = 2 is rejected.
private def selFree := mk 3 [.constrain x (.bits 8), .constrain y (.bits 8),
  .constrain (.select z x y) (.bits 8)]
#guard size selFree == 3
#guard rejects selFree [1, 2, 2]
private def selBool := mk 3 [.constrain x (.bits 8), .constrain y (.bits 8), .constrain z .bool,
  .constrain (.select z x y) (.bits 8)]
#guard size selBool == 3
#guard agrees selBool [1, 2, 1] && rejects selBool [1, 2, 2]

/-! ### Rule 2: `divmod` of a value that fits -/

private def dm := mk 1 [.constrain x (.bits 8), .bind 1 "r" (.divmod false 8 x), .bind 2 "q" (.divmod true 8 x)]
  [.var 1, .var 2]
#guard (Bounds.tighten [(0, 255)] (.divmod false 8 x)) == x
#guard (Bounds.tighten [(0, 255)] (.divmod true 8 x)) == .const 0
#guard agrees dm [200]
-- A width above 248 fails at run time; nothing is rewritten.
#guard (Bounds.tighten [(0, 255)] (.divmod false 300 x)) == .divmod false 300 x
private def dmWide := mk 1 [.constrain x (.bits 8), .bind 1 "r" (.divmod false 300 x)] [.var 1]
#guard rejects dmWide [5]
-- A value that does not fit stays.
#guard (Bounds.tighten [(0, 256)] (.divmod false 8 x)) == .divmod false 8 x
-- The quotient of a value that might fail stays (the remainder is the value itself):
-- dropping `lt 8 y x` would accept y = 300.
#guard (Bounds.tighten [(0, 255)] (.divmod true 8 (.lt 8 y x))) == .divmod true 8 (.lt 8 y x)
#guard (Bounds.tighten [(0, 255)] (.divmod false 8 (.lt 8 y x))) == .lt 8 y x
private def dmFail := mk 2 [.constrain x (.bits 8), .bind 2 "q" (.divmod true 8 (.lt 8 y x))] [.var 2]
#guard rejects dmFail [3, 300]

/-! ### Rule 3: comparisons the bounds decide -/

#guard Bounds.tighten [(0, 9)] (.lt 8 x (.const 10)) == .const 1
#guard Bounds.tighten [(1, 100)] (.lt 8 (.const 200) y) == .const 0
-- Undecided by the bounds: kept.
#guard Bounds.tighten [(0, 10)] (.lt 8 x (.const 10)) == .lt 8 x (.const 10)
-- The constant must fit the width: `lt 8 x 300` fails for every x, and stays.
#guard Bounds.tighten [(0, 9)] (.lt 8 x (.const 300)) == .lt 8 x (.const 300)
-- An operand without a bound may not fit: x = 300 fails.
#guard Bounds.tighten [] (.lt 8 (.const 200) x) == .lt 8 (.const 200) x
private def ltc := mk 1 [.constrain x (.below 10 4), .bind 1 "c" (.lt 8 x (.const 10))] [.var 1]
#guard (ltc.bounds.body.toList.getD 1 default |> fun | .bind _ _ (.const 1) => true | _ => false)
#guard agrees ltc [9] && rejects ltc [10]

/-! ### Bounds from assertions, and rebinding -/

-- After `assert (x < 10)`, a check `x < 10` (as `below 10 4`) is implied.
private def asrt := mk 1 [.constrain x (.bits 8), .assert (.lt 8 x (.const 10)) "",
  .constrain x (.below 10 4)]
#guard size asrt == 2
#guard agrees asrt [9] && rejects asrt [10]
-- After `assert (not (100 < x))`, x ≤ 100.
private def asrtLe := mk 1 [.constrain x (.bits 8),
  .assert (.select (.lt 8 (.const 100) x) (.const 0) (.const 1)) "", .constrain x (.below 101 8)]
#guard size asrtLe == 2
#guard agrees asrtLe [100] && rejects asrtLe [101]
-- A variable bound again loses its bound: x0 := x1 after the assertion, and
-- dropping the check would accept x1 = 50.
private def rebind := mk 2 [.constrain x (.bits 8), .assert (.lt 8 x (.const 10)) "",
  .bind 0 "x" y, .constrain x (.below 10 4)]
#guard size rebind == 4
#guard rejects rebind [3, 50] && agrees rebind [3, 5]

/-! ### Witness results -/

-- Results are checked as they arrive, also when the call is not made (then
-- they are 0); a later wider check is implied.
private def wit := mk 1 [.constrain x .bool,
  .witness x "w" [] [(1, some (.bits 8))] (.prim (.uint 255)), .constrain (.add y y) (.bits 9)]
#guard size wit == 2
#guard agrees wit [1] [200] && agrees wit [0] [] && rejects wit [1] [300]
-- A variable named twice keeps only its last value: nothing is learned.
private def witDup := mk 0 [.witness (.const 1) "w" [] [(0, some (.bits 8)), (0, none)] (.prim .field),
  .constrain x (.bits 8)]
#guard size witDup == 2
#guard rejects witDup [] [1, 300]

/-! ### Surface syntax -/

namespace Surface

/-- Compact's `assert(x < 10); x as Uint<0..10>`: the cast's range check is
    implied by the assertion. -/
circuit digit (x : Uint8) : Uint 9 := do
  require (x <. 10) "not a digit"
  x.castTo 9

/-- The sum of two bytes, as a field element, into `Uint<0..1001>`: the
    check is implied by the bounds of the bytes; and a comparison of the sum
    with 600 is always true. -/
circuit pair (a b : Uint8) : Uint 1000 × Boolean := do
  let s ← (a.toField + b.toField).toUint 1000
  return (s, s <. 600)

/-- The low 31 bytes of a byte: the byte itself. -/
circuit low (a : Uint8) : Bytes 32 := do
  return upgradeFromTransient a.toField

end Surface

/-- ZKIR instruction count after the default optimizer, and after the
    pipeline `simplify; bounds; simplify`. -/
def counts (c : Circuit) : Option (Nat × Nat) :=
  match Emit.circuit c.simplify, Emit.circuit (Circuit.bounds c.simplify).simplify with
  | .ok a, .ok b => some (a.instructions.size, b.instructions.size)
  | _, _ => none

#guard match counts Surface.digit.circuit with | some (a, b) => b < a | none => false
#guard match counts Surface.pair.circuit with | some (a, b) => b < a | none => false
#guard match counts Surface.low.circuit with | some (a, b) => b < a | none => false

-- The runs agree.
#guard agrees Surface.digit.circuit [7] && rejects Surface.digit.circuit [10]
#guard agrees Surface.pair.circuit [255, 255] && rejects Surface.pair.circuit [256, 0]
#guard agrees Surface.low.circuit [200]

end Examples.OptBounds
