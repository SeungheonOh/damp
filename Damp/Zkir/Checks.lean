/-
The obligations Midnight's ZKIR specification places on whoever produces a
circuit (§8.2 of the ZKIR v3 spec). Upstream's result that the evaluator and
the constraint system agree is stated for circuits that meet them; the
constraint system itself does not enforce them. They are decidable, and every
circuit Damp emits is checked against all three:

* O1, single assignment: `IrSource.checkSingleAssignment` in `Damp/Zkir/Basic.lean`;
* O2, value typing: every operand has the type its instruction expects;
* O3, bit bounds: the widths given to range checks and comparisons are legal.

A fourth check is about the file rather than the spec: every immediate is one
Midnight's loader accepts (`IrSource.checkImmediates`), so the file written
reads back as the circuit the theorems are about (`IrSource.ofJson_toJson` in
`Damp/Proofs/ZkirJson.lean`).
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

/-- An operand the loader accepts: a register, or an immediate whose absolute
    value is below the field modulus (the loader reads an immediate as at most
    32 little-endian bytes and refuses a value that is not a field element). -/
def Operand.okB : Operand → Bool
  | .var _ => true
  | .imm v => decide (v.natAbs < Fr.modulus)

/-- Every immediate of the circuit is one the loader accepts, decided. -/
def IrSource.okB (s : IrSource) : Bool := s.instructions.all fun i => i.uses.all Operand.okB

/-- Every immediate is one the loader accepts. The evaluator reads an
    immediate `c` as `Fr.ofInt c`, but the loader refuses `|c| ≥ p`, so such a
    circuit could not be loaded at all. -/
def IrSource.checkImmediates (s : IrSource) : Except String Unit :=
  if s.okB then pure ()
  else
    let bad := (s.instructions.toList.flatMap Instr.uses).find? (! ·.okB)
    let shown := match bad with
      | some (.imm v) => toString v
      | _ => "?"
    throw s!"the constant {shown} is not below the field modulus in absolute value;       a Field literal must be reduced modulo the field size"

/-- The three producer obligations, and immediates the loader accepts. -/
def IrSource.checkProducer (s : IrSource) : Except String Unit := do
  s.checkSingleAssignment
  s.checkTyped
  s.checkBitBounds
  s.checkImmediates

theorem IrSource.okB_of_checkImmediates {s : IrSource} (h : s.checkImmediates = .ok ()) : s.okB = true := by
  unfold IrSource.checkImmediates at h
  split at h
  · assumption
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- What `checkProducer` accepts has every immediate in range. -/
theorem IrSource.okB_of_checkProducer {s : IrSource} (h : s.checkProducer = .ok ()) : s.okB = true := by
  apply IrSource.okB_of_checkImmediates
  unfold IrSource.checkProducer at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · cases h' : s.checkImmediates with
        | error e => rw [h'] at h; cases h
        | ok u => cases u; rfl

end Damp.Zkir
