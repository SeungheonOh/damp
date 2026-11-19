import Damp
import Damp.Optimize.Bounds2

/-! Checks on the value-range pass with relational facts (`Circuit.bounds2`,
`Damp/Optimize/Bounds2.lean`), proved sound in
`Damp/Proofs/Optimize/Bounds2.lean` (`Circuit.bounds2_sound`). The new rules
fire after a checked subtraction, and each side condition blocks them where
the rewrite would change which runs succeed; the comments give the run that
the naive rewrite would get wrong. -/
namespace Examples.OptBounds2
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
def agrees (c : Circuit) (inputs : List Fr) : Bool :=
  observe c inputs [] [] == observe c.bounds2 inputs [] []

def rejects (c : Circuit) (inputs : List Fr) : Bool := (observe c inputs [] []).isNone

/-- Number of statements after the pass. -/
private def size (c : Circuit) : Nat := c.bounds2.body.size

private def a : Expr := .var 0
private def b : Expr := .var 1
private def g : Expr := .var 2
/-- `¬ a < b`, as `Uint.sub` asserts it. -/
private def notLt : Expr := .select (.lt 16 a b) (.const 0) (.const 1)

/-! ### Unguarded: `a.sub b` -/

-- `a, b < 2^16`, `assert ¬ a < b`, `d := a - b`: `d < 2^16`, so a check of
-- `d` to 16 bits is dropped (`bounds` keeps it).
private def sub := mk 2
  [.constrain a (.bits 16), .constrain b (.bits 16), .assert notLt "neg",
   .bind 3 "d" (.add a (.neg b)), .constrain (.var 3) (.bits 16)] [.var 3]
#guard size sub == 4
#guard sub.bounds.body.size == 5
#guard agrees sub [7, 3] && agrees sub [3, 3] && rejects sub [3, 7]
-- The check itself, of `a + -b`, is dropped too.
private def subDirect := mk 2
  [.constrain a (.bits 16), .constrain b (.bits 16), .assert notLt "neg",
   .constrain (.add a (.neg b)) (.bits 16)]
#guard size subDirect == 3
#guard agrees subDirect [7, 3]

-- Without the assertion nothing is known: for `a = 3`, `b = 7`, `a - b` wraps
-- around and fails the check, so it must stay.
private def noAssert := mk 2
  [.constrain a (.bits 16), .constrain b (.bits 16),
   .bind 3 "d" (.add a (.neg b)), .constrain (.var 3) (.bits 16)]
#guard size noAssert == 4
#guard rejects noAssert [3, 7]
#guard (observe (mk 2 [.constrain a (.bits 16), .constrain b (.bits 16),
   .bind 3 "d" (.add a (.neg b))]) [3, 7] [] []).isSome

-- The fact is forgotten when one of its variables is bound again: after
-- `a := 0`, `a - b` is `-b`, which fails the check for `b = 3`.
private def rebound := mk 2
  [.constrain a (.bits 16), .constrain b (.bits 16), .assert notLt "neg", .bind 0 "a" (.const 0),
   .bind 3 "d" (.add a (.neg b)), .constrain (.var 3) (.bits 16)]
#guard size rebound == 6
#guard rejects rebound [5, 3]
#guard agrees rebound [5, 0]

-- A fact about `(a, b)` says nothing about `(b, a)`: for `a = 7`, `b = 3`,
-- `b - a` fails the check.
private def swapped := mk 2
  [.constrain a (.bits 16), .constrain b (.bits 16), .assert notLt "neg",
   .bind 3 "d" (.add b (.neg a)), .constrain (.var 3) (.bits 16)]
#guard size swapped == 5
#guard rejects swapped [7, 3]

/-! ### Guarded: `a.sub b` under `if g` -/

-- `assert (select g ¬(a < b) 1)` and `d := select g (a - b) 0`: if `g` is 1,
-- `d = a - b ≤ a`; otherwise `d = 0`.
private def guarded := mk 3
  [.constrain a (.bits 16), .constrain b (.bits 16), .constrain g .bool,
   .assert (.select g notLt (.const 1)) "neg",
   .bind 3 "d" (.select g (.add a (.neg b)) (.const 0)), .constrain (.var 3) (.bits 16)] [.var 3]
#guard size guarded == 5
#guard agrees guarded [7, 3, 1] && agrees guarded [3, 7, 0] && rejects guarded [3, 7, 1]

-- Under a different guard the fact says nothing: with `g = 0` the assertion
-- holds for `a = 3`, `b = 7`, but under the guard `h = 1` the value `a - b`
-- wraps around and fails.
private def otherGuard := mk 4
  [.constrain a (.bits 16), .constrain b (.bits 16), .constrain g .bool, .constrain (.var 3) .bool,
   .assert (.select g notLt (.const 1)) "neg",
   .bind 4 "d" (.select (.var 3) (.add a (.neg b)) (.const 0)), .constrain (.var 4) (.bits 16)]
#guard size otherGuard == 7
#guard rejects otherGuard [3, 7, 0, 1]

/-! ### Surface syntax -/

namespace Surface

ledger
  change : Cell Uint16

/-- Compact's `const c = paid - price; change = (c as Field) as Uint<16>`:
    the cast's range check is implied by the subtraction's check. -/
circuit pay (price paid : Uint16) : Uint16 := do
  const c ← paid.sub price
  const back ← c.toField.toUint 65535
  change.write (disclose back)
  change.read

/-- The same under a condition. -/
circuit maybePay (price paid : Uint16) (go : Boolean) : Uint16 := do
  if% disclose go then do
    const c ← paid.sub price
    const back ← c.toField.toUint 65535
    change.write (disclose back)
  change.read

end Surface

/-- ZKIR instruction count after the pipeline with `bounds`, and after it with
    `bounds2` in place of `bounds`. -/
def counts (c : Circuit) : Option (Nat × Nat) :=
  match Emit.circuit (runPasses [Circuit.simplify, Circuit.bounds, Circuit.simplify, Circuit.algebra] c),
      Emit.circuit (runPasses [Circuit.simplify, Circuit.bounds2, Circuit.simplify, Circuit.algebra] c) with
  | .ok x, .ok y => some (x.instructions.size, y.instructions.size)
  | _, _ => none

#guard counts Surface.pay.circuit == some (16, 15)
#guard counts Surface.maybePay.circuit == some (20, 19)

-- The runs agree (the ledger read returns 4).
private def agreesPub (c : Circuit) (inputs : List Fr) : Bool :=
  observe c inputs [] [4] == observe c.bounds2 inputs [] [4]
#guard agreesPub Surface.pay.circuit [3, 7] && (observe Surface.pay.circuit [3, 7] [] [4]).isSome
#guard agreesPub Surface.pay.circuit [7, 3] && (observe Surface.pay.circuit [7, 3] [] [4]).isNone
#guard agreesPub Surface.maybePay.circuit [7, 3, 0] && (observe Surface.maybePay.circuit [7, 3, 0] [] [4]).isSome
#guard agreesPub Surface.maybePay.circuit [7, 3, 1]
#guard agreesPub Surface.maybePay.circuit [3, 7, 1]

end Examples.OptBounds2
