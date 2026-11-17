/-
Reading ZKIR v3 JSON back into `Zkir.IrSource`: the inverse of
`IrSource.toJson` (Damp/Zkir.lean), and a reader for the `.zkir` files compactc
writes, which have the same shape.

Operand syntax follows the Rust loader (midnight-zkir 3.2.1, `zkir/src/ir.rs`,
`impl Deserialize for Operand`): a string starting with `%` is a register; an
optional `-` followed by `0x`/`0X` and an even number of hex digits is an
immediate, read as **little-endian** bytes (at most 32 of them), which must be
below the field modulus, and negated in the field when the `-` is present. Anything else is
rejected. Registers are `Zkir.Ident`s, printed `%hint.id`; a name not of that
form is rejected, since `Ident` cannot represent it.

Total: no `partial`, no `sorry`.
-/
import Lean.Data.Json
import Damp.Zkir

namespace Damp.Zkir
open Lean (Json)

abbrev Parse := Except String

/-! ## Scalars -/

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Bytes from hex digits, two per byte, in order. -/
def hexBytes : List Char → Option (List Nat)
  | [] => some []
  | [_] => none
  | a :: b :: rest => do
      let hi ← hexDigit a
      let lo ← hexDigit b
      let more ← hexBytes rest
      pure ((16 * hi + lo) :: more)

/-- Little-endian bytes as a number. -/
def leValue (bs : List Nat) : Nat := bs.foldr (fun b acc => acc * 256 + b) 0

/-- `%hint.id`. -/
def parseIdent (s : String) : Parse Ident := do
  let cs := s.toList
  match cs with
  | '%' :: rest =>
      let digits := (rest.reverse.takeWhile Char.isDigit).reverse
      let pre := rest.take (rest.length - digits.length)
      if digits.isEmpty || pre.getLast? != some '.' then
        throw s!"register name {s} is not of the form %hint.id"
      pure { hint := String.ofList pre.dropLast, id := String.toNat! (String.ofList digits) }
  | _ => throw s!"register name {s} does not start with %"

/-- An immediate's body after `0x`: little-endian hex, below the modulus. -/
def parseImmBody (s : String) (body : List Char) : Parse Nat := do
  if body.isEmpty then throw s!"immediate {s} has no digits"
  let some bs := hexBytes body | throw s!"immediate {s} is not an even number of hex digits"
  -- `Fr::from_le_bytes` takes at most 32 bytes, even when the extra ones are zero.
  if bs.length > 32 then throw s!"immediate {s} has more than 32 bytes"
  let v := leValue bs
  if v ≥ Fr.modulus then throw s!"immediate {s} is out of range for a field element"
  pure v

def parseOperandStr (s : String) : Parse Operand := do
  let cs := s.toList
  let (neg, rest) := match cs with
    | '-' :: r => (true, r)
    | r => (false, r)
  match rest with
  | '0' :: x :: body =>
      if x = 'x' ∨ x = 'X' then
        let v ← parseImmBody s body
        pure (.imm (if neg then -(v : Int) else v))
      else throw s!"invalid operand {s}"
  | _ =>
      if neg then throw s!"invalid operand {s}"
      else .var <$> parseIdent s

/-! ## JSON access -/

def getField (j : Json) (k : String) : Parse Json :=
  match j.getObjVal? k with
  | .ok v => pure v
  | .error _ => throw s!"missing field {k} in {j.compress}"

def getStr (j : Json) (k : String) : Parse String := do
  match (← getField j k) with
  | .str s => pure s
  | v => throw s!"field {k}: expected a string, got {v.compress}"

def getNat (j : Json) (k : String) : Parse Nat := do
  match (← getField j k).getNat? with
  | .ok n => pure n
  | .error _ => throw s!"field {k}: expected a natural number"

def getArr (j : Json) (k : String) : Parse (Array Json) := do
  match (← getField j k) with
  | .arr a => pure a
  | v => throw s!"field {k}: expected an array, got {v.compress}"

def asStr : Json → Parse String
  | .str s => pure s
  | v => throw s!"expected a string, got {v.compress}"

def operand (j : Json) (k : String) : Parse Operand := do parseOperandStr (← getStr j k)
def ident (j : Json) (k : String) : Parse Ident := do parseIdent (← getStr j k)
def operands (j : Json) (k : String) : Parse (List Operand) := do
  ((← getArr j k).toList.mapM fun x => do parseOperandStr (← asStr x))
def idents (j : Json) (k : String) : Parse (List Ident) := do
  ((← getArr j k).toList.mapM fun x => do parseIdent (← asStr x))

def parseType (s : String) : Parse IrType :=
  match s with
  | "Scalar<BLS12-381>" => pure .native
  | "Bytes<32>" => pure .bytes32
  | "Point<Jubjub>" => pure .jubjubPoint
  | "Scalar<Jubjub>" => pure .jubjubScalar
  | _ => throw s!"unsupported type {s}"

def parseAtom (j : Json) : Parse AlignAtom := do
  unless (← getStr j "tag") == "atom" do throw s!"unsupported alignment segment {j.compress}"
  let v ← getField j "value"
  match (← getStr v "tag") with
  | "bytes" => .bytes <$> getNat v "length"
  | "field" => pure .field
  | "compress" => pure .compress
  | t => throw s!"unknown alignment atom {t}"

/-- An absent or `null` guard is no guard. -/
def guard (j : Json) : Parse (Option Operand) :=
  match j.getObjVal? "guard" with
  | .ok .null | .error _ => pure none
  | .ok (.str s) => some <$> parseOperandStr s
  | .ok v => throw s!"guard: expected a string or null, got {v.compress}"

/-! ## Instructions -/

def parseInstr (j : Json) : Parse Instr := do
  let op ← getStr j "op"
  match op with
  | "encode" => return .encode (← operand j "input") (← idents j "outputs")
  | "assert" => return .assert (← operand j "cond")
  | "cond_select" => return .condSelect (← ident j "output") (← operand j "bit") (← operand j "a") (← operand j "b")
  | "constrain_bits" => return .constrainBits (← operand j "val") (← getNat j "bits")
  | "constrain_eq" => return .constrainEq (← operand j "a") (← operand j "b")
  | "constrain_to_boolean" => return .constrainToBoolean (← operand j "val")
  | "copy" => return .copy (← ident j "output") (← operand j "val")
  | "impact" => return .impact (← operand j "guard") (← operands j "inputs")
  | "ec_mul" => return .ecMul (← ident j "output") (← operand j "a") (← operand j "scalar")
  | "ec_mul_generator" => return .ecMulGenerator (← ident j "output") (← operand j "scalar")
  | "hash_to_curve" => return .hashToCurve (← ident j "output") (← operands j "inputs")
  | "into_coordinates" =>
      match (← idents j "outputs") with
      | [x, y] => return .intoCoordinates (x, y) (← operand j "point")
      | _ => throw "into_coordinates: expected two outputs"
  | "from_coordinates" =>
      match (← operands j "inputs") with
      | [x, y] => return .fromCoordinates (← ident j "output") (x, y)
      | _ => throw "from_coordinates: expected two inputs"
  | "div_mod_power_of_two" => return .divModPowerOfTwo (← idents j "outputs") (← operand j "val") (← getNat j "bits")
  | "reconstitute_field" =>
      return .reconstituteField (← ident j "output") (← operand j "divisor") (← operand j "modulus") (← getNat j "bits")
  | "transient_hash" => return .transientHash (← ident j "output") (← operands j "inputs")
  | "persistent_hash" =>
      return .persistentHash (← ident j "output") (← (← getArr j "alignment").toList.mapM parseAtom) (← operands j "inputs")
  | "test_eq" => return .testEq (← ident j "output") (← operand j "a") (← operand j "b")
  | "add" => return .add (← ident j "output") (← operand j "a") (← operand j "b")
  | "mul" => return .mul (← ident j "output") (← operand j "a") (← operand j "b")
  | "neg" => return .neg (← ident j "output") (← operand j "a")
  | "inv" => return .inv (← ident j "output") (← operand j "a")
  | "not" => return .not (← ident j "output") (← operand j "a")
  | "less_than" => return .lessThan (← ident j "output") (← operand j "a") (← operand j "b") (← getNat j "bits")
  | "jubjub_scalar_from_native" => return .jubjubScalarFromNative (← ident j "output") (← operand j "native")
  | "public_input" => return .publicInput (← parseType (← getStr j "type")) (← ident j "output") (← guard j)
  | "private_input" => return .privateInput (← parseType (← getStr j "type")) (← ident j "output") (← guard j)
  | "output" => return .output (← operands j "vals")
  | "bytes_into_natives" => return .bytesIntoNatives (← idents j "outputs") (← operand j "bytes")
  | "bytes_from_natives" => return .bytesFromNatives (← ident j "output") (← operands j "inputs") (← getNat j "len")
  | _ => throw s!"unsupported instruction {op}"

/-! ## Circuits -/

def IrSource.ofJson (j : Json) : Parse IrSource := do
  let major ← getNat (← getField j "version") "major"
  unless major == 3 do throw s!"unsupported ZKIR major version {major}"
  let cc ← match (← getField j "do_communications_commitment") with
    | .bool b => pure b
    | v => throw s!"do_communications_commitment: expected a boolean, got {v.compress}"
  let inputs ← (← getArr j "inputs").toList.mapM fun i => do
    return ((← ident i "name"), (← parseType (← getStr i "type")))
  let outputs ← (← getArr j "outputs").toList.mapM fun t => do parseType (← asStr t)
  let instructions ← (← getArr j "instructions").mapM parseInstr
  pure { inputs, outputs, commCommitment := cc, instructions }

/-- Parse the text of a `.zkir` file. -/
def IrSource.parse (text : String) : Parse IrSource := do
  IrSource.ofJson (← Json.parse text)

end Damp.Zkir
