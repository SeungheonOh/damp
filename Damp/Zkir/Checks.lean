/-
The obligations Midnight's ZKIR specification places on whoever produces a
circuit (§8.2 of the ZKIR v3 spec). Upstream's result that the evaluator and
the constraint system agree is stated for circuits that meet them; the
constraint system itself does not enforce them. They are decidable, and every
circuit Damp emits is checked against all three:

* O1, single assignment: `IrSource.checkSingleAssignment` in `Damp/Zkir/Basic.lean`;
* O2, value typing: every operand has the type its instruction expects;
* O3, bit bounds: the widths given to range checks and comparisons are legal.
-/
import Damp.Zkir.Basic

namespace Damp.Zkir

/-- The types a register can have in the circuits Damp emits. -/
inductive RegTy where
  | native
  | bytes
  deriving DecidableEq, Repr

/-- O3: `bits < 255` for range checks and comparisons, `bits ≤ 248` for the
    split and rebuild instructions. An illegal width leaves the constraint
    system satisfiable where the evaluator fails, so it must be ruled out here. -/
def IrSource.checkBitBounds (s : IrSource) : Except String Unit := do
  for i in s.instructions do
    match i with
    | .constrainBits _ n => unless n < 255 do throw s!"constrain_bits with illegal width {n}"
    | .lessThan _ _ _ n => unless n < 255 do throw s!"less_than with illegal width {n}"
    | .divModPowerOfTwo _ _ n => unless n ≤ 248 do throw s!"div_mod_power_of_two with illegal width {n}"
    | .reconstituteField _ _ _ n => unless n ≤ 248 do throw s!"reconstitute_field with illegal width {n}"
    | _ => pure ()

private def tyOf (tys : List (Ident × RegTy)) : Operand → Except String RegTy
  | .imm _ => pure .native
  | .var id =>
      match tys.lookup id with
      | some t => pure t
      | none => throw s!"register {id} read before it is bound"

private def need (tys : List (Ident × RegTy)) (what : String) (t : RegTy) (o : Operand) :
    Except String Unit := do
  unless (← tyOf tys o) = t do throw s!"{what}: operand of the wrong type"

/-- O2: every operand is bound with the type its instruction expects. Covers
    the instructions Damp emits; any other instruction is refused. -/
def IrSource.checkTyped (s : IrSource) : Except String Unit := do
  let mut tys : List (Ident × RegTy) := []
  for (id, t) in s.inputs do
    unless t == .native do throw s!"input {id} is not a native field element"
    tys := (id, .native) :: tys
  for i in s.instructions do
    let nat (what : String) (os : List Operand) : Except String Unit :=
      os.forM (need tys what .native)
    match i with
    | .assert c => nat "assert" [c]
    | .condSelect out bit a b => do nat "cond_select" [bit, a, b]; tys := (out, .native) :: tys
    | .constrainBits v _ => nat "constrain_bits" [v]
    | .constrainEq a b => nat "constrain_eq" [a, b]
    | .constrainToBoolean v => nat "constrain_to_boolean" [v]
    | .copy out v => do tys := (out, ← tyOf tys v) :: tys
    | .testEq out a b => do nat "test_eq" [a, b]; tys := (out, .native) :: tys
    | .add out a b => do nat "add" [a, b]; tys := (out, .native) :: tys
    | .mul out a b => do nat "mul" [a, b]; tys := (out, .native) :: tys
    | .neg out a => do nat "neg" [a]; tys := (out, .native) :: tys
    | .not out a => do nat "not" [a]; tys := (out, .native) :: tys
    | .lessThan out a b _ => do nat "less_than" [a, b]; tys := (out, .native) :: tys
    | .transientHash out is => do nat "transient_hash" is; tys := (out, .native) :: tys
    | .divModPowerOfTwo outs v _ => do
        nat "div_mod_power_of_two" [v]
        tys := outs.map (·, RegTy.native) ++ tys
    | .persistentHash out _ is => do nat "persistent_hash" is; tys := (out, .bytes) :: tys
    | .bytesIntoNatives outs b => do
        need tys "bytes_into_natives" .bytes b
        tys := outs.map (·, RegTy.native) ++ tys
    | .privateInput t out g => do
        unless t == .native do throw "private_input of a non-native type"
        nat "private_input" g.toList
        tys := (out, .native) :: tys
    | .publicInput t out g => do
        unless t == .native do throw "public_input of a non-native type"
        nat "public_input" g.toList
        tys := (out, .native) :: tys
    | .impact g is => nat "impact" (g :: is)
    | .output vs => nat "output" vs
    | _ => throw "an instruction Damp does not emit"

/-- All three producer obligations. -/
def IrSource.checkProducer (s : IrSource) : Except String Unit := do
  s.checkSingleAssignment
  s.checkTyped
  s.checkBitBounds

end Damp.Zkir
