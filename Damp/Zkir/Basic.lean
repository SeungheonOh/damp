/-
ZKIR v3 as Lean data, with the JSON form Midnight's `zkir` tool reads.

Field names follow `midnight-zkir/zkir/src/ir.rs` (3.2.1). Key generation and
proving stay in the Rust tool; this file only describes and prints circuits.
-/
import Lean.Data.Json
import Damp.Field

namespace Damp.Zkir
open Lean (Json)

/-- A register. Printed as `%hint.id`; the emitter numbers registers in order,
    so `id` alone identifies one within a circuit. -/
structure Ident where
  hint : String
  id : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

def Ident.toString (i : Ident) : String := s!"%{i.hint}.{i.id}"

instance : ToString Ident := ⟨Ident.toString⟩
instance : Coe Ident Json := ⟨fun i => .str i.toString⟩

/-- A named register, or a field immediate. A negative immediate denotes field negation. -/
inductive Operand where
  | var (name : Ident)
  | imm (v : Int)
  deriving Repr, BEq, DecidableEq, Inhabited

inductive IrType where
  | native
  | bytes32
  | jubjubPoint
  | jubjubScalar
  deriving Repr, BEq, Inhabited

/-- One atom of a field-aligned-binary alignment. -/
inductive AlignAtom where
  | bytes (n : Nat)
  | field
  | compress
  deriving Repr, DecidableEq, Inhabited

abbrev Alignment := List AlignAtom

inductive Instr where
  | encode (input : Operand) (outputs : List Ident)
  | assert (cond : Operand)
  | condSelect (output : Ident) (bit a b : Operand)
  | constrainBits (val : Operand) (bits : Nat)
  | constrainEq (a b : Operand)
  | constrainToBoolean (val : Operand)
  | copy (output : Ident) (val : Operand)
  | impact (guard : Operand) (inputs : List Operand)
  | ecMul (output : Ident) (a scalar : Operand)
  | ecMulGenerator (output : Ident) (scalar : Operand)
  | hashToCurve (output : Ident) (inputs : List Operand)
  | intoCoordinates (outputs : Ident × Ident) (point : Operand)
  | fromCoordinates (output : Ident) (inputs : Operand × Operand)
  | divModPowerOfTwo (outputs : List Ident) (val : Operand) (bits : Nat)
  | reconstituteField (output : Ident) (divisor modulus : Operand) (bits : Nat)
  | transientHash (output : Ident) (inputs : List Operand)
  | persistentHash (output : Ident) (alignment : Alignment) (inputs : List Operand)
  | testEq (output : Ident) (a b : Operand)
  | add (output : Ident) (a b : Operand)
  | mul (output : Ident) (a b : Operand)
  | neg (output : Ident) (a : Operand)
  | inv (output : Ident) (a : Operand)
  | not (output : Ident) (a : Operand)
  | lessThan (output : Ident) (a b : Operand) (bits : Nat)
  | jubjubScalarFromNative (output : Ident) (native : Operand)
  | publicInput (ty : IrType) (output : Ident) (guard : Option Operand)
  | privateInput (ty : IrType) (output : Ident) (guard : Option Operand)
  | output (vals : List Operand)
  | bytesIntoNatives (outputs : List Ident) (bytes : Operand)
  | bytesFromNatives (output : Ident) (inputs : List Operand) (len : Nat)
  deriving Repr, Inhabited

structure IrSource where
  inputs : List (Ident × IrType)
  outputs : List IrType
  commCommitment : Bool := true
  instructions : Array Instr
  deriving Repr, Inhabited

/-! ## Reading the structure -/

/-- Registers an instruction defines, in order. -/
def Instr.defs : Instr → List Ident
  | .encode _ os | .divModPowerOfTwo os _ _ | .bytesIntoNatives os _ => os
  | .intoCoordinates (x, y) _ => [x, y]
  | .condSelect o .. | .copy o _ | .ecMul o .. | .ecMulGenerator o _ | .hashToCurve o _
  | .fromCoordinates o _ | .reconstituteField o .. | .transientHash o _
  | .persistentHash o .. | .testEq o .. | .add o .. | .mul o .. | .neg o _ | .inv o _
  | .not o _ | .lessThan o .. | .jubjubScalarFromNative o _ | .publicInput _ o _
  | .privateInput _ o _ | .bytesFromNatives o .. => [o]
  | .assert _ | .constrainBits .. | .constrainEq .. | .constrainToBoolean _ | .impact ..
  | .output _ => []

/-- Operands an instruction reads. -/
def Instr.uses : Instr → List Operand
  | .encode i _ => [i]
  | .assert c => [c]
  | .condSelect _ bit a b => [bit, a, b]
  | .constrainBits v _ | .constrainToBoolean v | .copy _ v | .divModPowerOfTwo _ v _ => [v]
  | .constrainEq a b | .testEq _ a b | .add _ a b | .mul _ a b | .lessThan _ a b _ => [a, b]
  | .impact g is => g :: is
  | .ecMul _ a s => [a, s]
  | .ecMulGenerator _ s => [s]
  | .hashToCurve _ is | .transientHash _ is | .persistentHash _ _ is | .output is
  | .bytesFromNatives _ is _ => is
  | .intoCoordinates _ p => [p]
  | .fromCoordinates _ (x, y) => [x, y]
  | .reconstituteField _ d m _ => [d, m]
  | .neg _ a | .inv _ a | .not _ a | .jubjubScalarFromNative _ a | .bytesIntoNatives _ a => [a]
  | .publicInput _ _ g | .privateInput _ _ g => g.toList

/--
Producer obligation O1 of the ZKIR spec (single assignment), plus scoping:
input names are distinct, no instruction rebinds a name, and every register is
bound before it is read. The upstream soundness result assumes this of the
compiler, so every emitted circuit is checked.
-/
def IrSource.checkSingleAssignment (s : IrSource) : Except String Unit := do
  let mut bound : List Ident := []
  for (n, _) in s.inputs do
    if bound.contains n then throw s!"duplicate input {n}"
    bound := n :: bound
  for i in s.instructions do
    for u in i.uses do
      if let .var n := u then
        unless bound.contains n do throw s!"register {n} read before it is bound"
    for d in i.defs do
      if bound.contains d then throw s!"register {d} bound twice"
      bound := d :: bound

/-! ## JSON -/

/-- Bytes of `n`, least significant first; at least one byte. -/
def leBytes (n : Nat) : List Nat :=
  if h : n < 256 then [n] else (n % 256) :: leBytes (n / 256)
termination_by n
decreasing_by omega

def hexByte (b : Nat) : String :=
  let h := Nat.toDigits 16 b
  String.ofList (if h.length < 2 then '0' :: h else h)

/-- Minimal little-endian hex, as the Rust loader expects: 1000 ↦ "e803". -/
def leHex (n : Nat) : String := String.join ((leBytes n).map hexByte)

def Operand.toJson : Operand → Json
  | .var n => .str n.toString
  | .imm v => .str ((if v < 0 then "-0x" else "0x") ++ leHex v.natAbs)

def IrType.toJson : IrType → Json
  | .native => "Scalar<BLS12-381>"
  | .bytes32 => "Bytes<32>"
  | .jubjubPoint => "Point<Jubjub>"
  | .jubjubScalar => "Scalar<Jubjub>"

def AlignAtom.toJson (a : AlignAtom) : Json :=
  let v := match a with
    | .bytes n => Json.mkObj [("tag", "bytes"), ("length", n)]
    | .field => Json.mkObj [("tag", "field")]
    | .compress => Json.mkObj [("tag", "compress")]
  Json.mkObj [("tag", "atom"), ("value", v)]

private def ops (l : List Operand) : Json := .arr (l.map Operand.toJson).toArray
private def ids (l : List Ident) : Json := .arr (l.map fun i => Json.str i.toString).toArray
private def guardJson : Option Operand → Json
  | none => .null
  | some g => g.toJson
private def obj (op : String) (fields : List (String × Json)) : Json :=
  Json.mkObj (("op", Json.str op) :: fields)

def Instr.toJson : Instr → Json
  | .encode i os => obj "encode" [("input", i.toJson), ("outputs", ids os)]
  | .assert c => obj "assert" [("cond", c.toJson)]
  | .condSelect o bit a b =>
      obj "cond_select" [("output", o), ("bit", bit.toJson), ("a", a.toJson), ("b", b.toJson)]
  | .constrainBits v b => obj "constrain_bits" [("val", v.toJson), ("bits", b)]
  | .constrainEq a b => obj "constrain_eq" [("a", a.toJson), ("b", b.toJson)]
  | .constrainToBoolean v => obj "constrain_to_boolean" [("val", v.toJson)]
  | .copy o v => obj "copy" [("output", o), ("val", v.toJson)]
  | .impact g is => obj "impact" [("guard", g.toJson), ("inputs", ops is)]
  | .ecMul o a s => obj "ec_mul" [("output", o), ("a", a.toJson), ("scalar", s.toJson)]
  | .ecMulGenerator o s => obj "ec_mul_generator" [("output", o), ("scalar", s.toJson)]
  | .hashToCurve o is => obj "hash_to_curve" [("output", o), ("inputs", ops is)]
  | .intoCoordinates (x, y) p => obj "into_coordinates" [("outputs", ids [x, y]), ("point", p.toJson)]
  | .fromCoordinates o (x, y) => obj "from_coordinates" [("output", o), ("inputs", ops [x, y])]
  | .divModPowerOfTwo os v b =>
      obj "div_mod_power_of_two" [("outputs", ids os), ("val", v.toJson), ("bits", b)]
  | .reconstituteField o d m b =>
      obj "reconstitute_field" [("output", o), ("divisor", d.toJson), ("modulus", m.toJson), ("bits", b)]
  | .transientHash o is => obj "transient_hash" [("output", o), ("inputs", ops is)]
  | .persistentHash o al is =>
      obj "persistent_hash"
        [("output", o), ("alignment", .arr (al.map AlignAtom.toJson).toArray), ("inputs", ops is)]
  | .testEq o a b => obj "test_eq" [("output", o), ("a", a.toJson), ("b", b.toJson)]
  | .add o a b => obj "add" [("output", o), ("a", a.toJson), ("b", b.toJson)]
  | .mul o a b => obj "mul" [("output", o), ("a", a.toJson), ("b", b.toJson)]
  | .neg o a => obj "neg" [("output", o), ("a", a.toJson)]
  | .inv o a => obj "inv" [("output", o), ("a", a.toJson)]
  | .not o a => obj "not" [("output", o), ("a", a.toJson)]
  | .lessThan o a b bits =>
      obj "less_than" [("output", o), ("a", a.toJson), ("b", b.toJson), ("bits", bits)]
  | .jubjubScalarFromNative o n => obj "jubjub_scalar_from_native" [("output", o), ("native", n.toJson)]
  | .publicInput t o g => obj "public_input" [("type", t.toJson), ("output", o), ("guard", guardJson g)]
  | .privateInput t o g => obj "private_input" [("type", t.toJson), ("output", o), ("guard", guardJson g)]
  | .output vs => obj "output" [("vals", ops vs)]
  | .bytesIntoNatives os b => obj "bytes_into_natives" [("outputs", ids os), ("bytes", b.toJson)]
  | .bytesFromNatives o is len =>
      obj "bytes_from_natives" [("output", o), ("inputs", ops is), ("len", len)]

def IrSource.toJson (s : IrSource) : Json :=
  Json.mkObj [
    ("version", Json.mkObj [("major", 3), ("minor", 1)]),
    ("do_communications_commitment", s.commCommitment),
    ("inputs", .arr (s.inputs.map fun (n, t) => Json.mkObj [("name", (n : Json)), ("type", t.toJson)]).toArray),
    ("outputs", .arr (s.outputs.map IrType.toJson).toArray),
    ("instructions", .arr (s.instructions.map Instr.toJson))]

end Damp.Zkir
