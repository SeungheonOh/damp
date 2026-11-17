import Damp

/-!
Where the promises of the typed interface (`Damp/Contract.lean`) need a
hypothesis, or fail outright: one concrete counterexample each, checked by the
reference semantics. The positive statements are proved in
`Damp/InterfaceCorrect.lean`.
-/
namespace Examples.Interface
open Damp Damp.IR

/-- Hashes play no part here. -/
def prims : Zkir.Prims where
  transientHash _ := 0
  persistentHash _ _ := none
  transientCommit _ r := r

/-- Outputs of a run, or `none` if it fails. -/
def outputs (c : Circuit) (inputs priv pub : List Fr) : Option (List Nat) :=
  (c.run prims inputs priv pub).map fun o => o.outputs.map (·.val)

/-- Value of an expression in the all-zero environment. -/
def ev (e : Expr) : Option Nat := (e.eval prims fun _ => 0).map (·.val)

/-! ### Checked operations in a branch that is not taken (bug, fixed)

Compact zeroes a checked result in a branch that is not taken and guards its
check (`compactc` 0.36.1 emits `cond_select guard value 0` and a guarded
`assert`). Damp used to emit an unguarded range check for `toUint`/`castTo`
and return the raw difference from `sub`, so a branch that does not run could
make the whole circuit unprovable. Every run below marked "not taken" returned
`none` before the fix in `Damp/Contract.lean` (`guarded`). -/

/-- A checked conversion inside a branch that is not taken. -/
def deadCast : Circuit := mkCircuit "deadCast" ["x", "b"] fun (x : Field) (b : Boolean) =>
  (cond b (do let u ← x.toUint 255; pure u.toField) (pure 0) : CircuitM Field)

-- Taken with an in-range value: fine. Taken with 1000: rejected, as it must be.
#guard outputs deadCast [7, 1] [] [] = some [7]
#guard outputs deadCast [1000, 1] [] [] = none
-- Not taken: the conversion must not matter.
#guard outputs deadCast [1000, 0] [] [] = some [0]

/-- A subtraction inside a branch that is not taken, whose result is then compared. -/
def deadSub : Circuit := mkCircuit "deadSub" ["x", "y", "b"] fun (x y : Uint 255) (b : Boolean) =>
  (cond b (do let d ← x.sub y; pure (d.lt (Uint.lit 3))) (pure Boolean.false) : CircuitM Boolean)

#guard outputs deadSub [5, 3, 1] [] [] = some [1]
#guard outputs deadSub [3, 5, 1] [] [] = none
-- Not taken, with `y > x`: the subtraction must not matter.
#guard outputs deadSub [3, 5, 0] [] [] = some [0]

/-- The same for a narrowing cast. -/
def deadNarrow : Circuit := mkCircuit "deadNarrow" ["x", "b"] fun (x : Uint 65535) (b : Boolean) =>
  (cond b (do let u ← x.castTo 255; pure (u.lt (Uint.lit 3))) (pure Boolean.false) : CircuitM Boolean)

#guard outputs deadNarrow [2, 1] [] [] = some [1]
#guard outputs deadNarrow [1000, 1] [] [] = none
#guard outputs deadNarrow [1000, 0] [] [] = some [0]

/-! ### (a) Ledger reads are not range-checked

A `Uint 255` read from a ledger cell is whatever the public transcript answers:
the circuit does not check it. It is only as good as what was written there. -/

def readCell : Circuit := mkCircuit "readCell" [] (do
  let x ← (⟨0⟩ : Cell (Uint 255)).read
  pure x.toField : CircuitM Field)

-- A "`Uint 255`" holding 1000.
#guard outputs readCell [] [] [1000] = some [1000]

/-- Comparing such a value at the width of its type makes the circuit unprovable. -/
def readCellLt : Circuit := mkCircuit "readCellLt" [] (do
  let x ← (⟨0⟩ : Cell (Uint 255)).read
  pure (x.lt (Uint.lit 3)) : CircuitM Boolean)

#guard outputs readCellLt [] [] [2] = some [1]
#guard outputs readCellLt [] [] [1000] = none

/-! ### (b) Comparison widths

`Uint.lt` compares at `max (bitLen m) (bitLen k)` bits; ZKIR accepts widths
below 255 only, so the promise needs both bounds below `2 ^ 254`
(`Uint.lt_is`). Every bound up to Compact's `Uint.maxBound = 2 ^ 248 - 1`
qualifies, and since the cap of (d) no other bound can be made except with
`Field.unsafeToUint`; there the comparison has no value (`Uint.lt_too_wide`). -/

#guard ev ((Uint.lit Uint.maxBound).lt (Uint.lit 0)).expr = some 0
#guard ev (((Field.ofNat 0).unsafeToUint (2 ^ 254)).lt (Uint.lit 0)).expr = none

/-! ### (c) `Field.unsafeToUint` is unchecked by design

It is the one way to make a `Uint` that skips both the range check and the
248-bit cap; the caller is responsible (`Field.unsafeToUint_is`). -/

#guard ev ((Field.ofNat 1000).unsafeToUint 255).expr = some 1000
#guard ev (((Field.ofNat 1000).unsafeToUint 255).lt (Uint.lit 3)).expr = none

/-! ### (d) The 248-bit cap on every `Uint` (finding, fixed)

Before the fix only `+` and `*` applied Compact's limit, so `Uint.lit`,
`Uint.ofNat`, numerals and `widen` could produce a bound at or above the field
modulus, where a `Uint` no longer determines its number:
`(Uint.lit Fr.modulus).eq (Uint.lit 0)` evaluated to true. Now every way of
making a `Uint` except `Field.unsafeToUint` is capped: past the limit the value
is an `invalid` expression, and circuit arguments, witness results, `castTo`
and `toUint` with such a bound also record an error, so the circuit is
rejected even where the value is never used. -/

/-- The emitter's verdict: the error, or `none` when the circuit compiles. -/
def rejected (c : Circuit) : Option String :=
  match Emit.circuit c with
  | .error e => some e
  | .ok _ => none

def tooLarge (bound : Nat) : Option String := some (Uint.tooLarge bound)

-- What used to evaluate to true is now rejected.
#guard ev ((Uint.lit Fr.modulus).eq (Uint.lit 0)).expr = none
def litModulus : Circuit := mkCircuit "litModulus" [] (do
  pure ((Uint.lit Fr.modulus).eq (Uint.lit 0)) : CircuitM Boolean)
#guard rejected litModulus = tooLarge Fr.modulus
#guard outputs litModulus [] [] [] = none

-- At the limit everything works; one past it, nothing does.
#guard ev (Uint.lit Uint.maxBound).expr = some Uint.maxBound
#guard ev (Uint.lit (Uint.maxBound + 1)).expr = none
#guard ev (Uint.ofNat 5 (m := Uint.maxBound + 1) (by decide)).expr = none
#guard ev (OfNat.ofNat 5 : Uint (Uint.maxBound + 1)).expr = none
#guard ev ((Uint.lit 5).widen (k := Uint.maxBound) (by decide)).expr = some 5
#guard ev ((Uint.lit 5).widen (k := Uint.maxBound + 1) (by decide)).expr = none

-- Builders: an error at the declaration, used or not.
def castWide : Circuit := mkCircuit "castWide" ["x"] fun (x : Uint 255) =>
  (do let _ ← x.castTo (Uint.maxBound + 1); pure x.toField : CircuitM Field)
#guard rejected castWide = tooLarge (Uint.maxBound + 1)

def toUintWide : Circuit := mkCircuit "toUintWide" ["x"] fun (x : Field) =>
  (do let _ ← x.toUint (2 ^ 250); pure x : CircuitM Field)
#guard rejected toUintWide = tooLarge (2 ^ 250)

def witnessWide : Circuit := mkCircuit "witnessWide" [] (do
  let _ ← askWitness "w" (Uint (2 ^ 250)); pure (0 : Field) : CircuitM Field)
#guard rejected witnessWide = tooLarge (2 ^ 250)

def argWide : Circuit := mkCircuit "argWide" ["x", "y"] fun (_ : Uint (2 ^ 250)) (y : Field) =>
  (pure y : CircuitM Field)
#guard rejected argWide = tooLarge (2 ^ 250)

-- A ledger read of such a type has no value, so a circuit using it is rejected.
def readWide : Circuit := mkCircuit "readWide" [] (do
  let x ← (⟨0⟩ : Cell (Uint (2 ^ 250))).read
  pure x.toField : CircuitM Field)
#guard rejected readWide = tooLarge (2 ^ 250)

-- Within the limit nothing changes: the checked conversion still compiles.
def toUintOk : Circuit := mkCircuit "toUintOk" ["x"] fun (x : Field) =>
  (do let u ← x.toUint 255; pure u.toField : CircuitM Field)
#guard rejected toUintOk = none

/-! ### `+` and `*` past Compact's limit have no value (rejected by the emitter) -/

#guard ev (Uint.lit (2 ^ 248 - 1) + Uint.lit 0).expr = some (2 ^ 248 - 1)
#guard ev (Uint.lit (2 ^ 248 - 1) + Uint.lit 1).expr = none
#guard ev (Uint.lit (2 ^ 200) * Uint.lit (2 ^ 48)).expr = none

/-! ### `require` evaluates its condition even where the guard is false

The guarded assert is `select guard c 1`, and `select` evaluates both sides. A
condition with no value (here a comparison of an unchecked, out-of-range
value) fails the circuit even in a branch that is not taken. With values that
satisfy their types every condition has a value, so this needs (a) or (c). -/

def deadRequire : Circuit := mkCircuit "deadRequire" ["b"] fun (b : Boolean) =>
  (when_ b (require (((Field.ofNat 1000).unsafeToUint 255).lt (Uint.lit 3))) : CircuitM Unit)

#guard outputs deadRequire [0] [] [] = none

end Examples.Interface
