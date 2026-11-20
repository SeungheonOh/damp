import Damp

/-! Compact's casts (`x as T`), written with Damp's conversion functions.

Each circuit is the Damp port of the circuit of the same name in this Compact
program, compiled with compactc 0.36.1 (`--skip-zk`); `bench/zdiff.py --multiset` on
the two outputs shows only the differences listed below:

```
import CompactStandardLibrary;
enum E { a, b, c }
export ledger f: Field;
export ledger b32: Bytes<32>;
export ledger b4: Bytes<4>;
export ledger b31: Bytes<31>;
export ledger v4: Vector<4, Uint<8>>;
export ledger e: E;
export ledger u8: Uint<8>;
export ledger u16: Uint<16>;
export ledger bo: Boolean;
export ledger b40: Bytes<40>;
export ledger v33: Vector<33, Uint<8>>;
export ledger b33: Bytes<33>;
export circuit b4_to_field(x: Bytes<4>): [] { f = disclose(x) as Field; }
export circuit b31_to_field(x: Bytes<31>): [] { f = disclose(x) as Field; }
export circuit field_to_b32(x: Field): [] { b32 = disclose(x) as Bytes<32>; }
export circuit field_to_b4(x: Field): [] { b4 = disclose(x) as Bytes<4>; }
export circuit field_to_b31(x: Field): [] { b31 = disclose(x) as Bytes<31>; }
export circuit field_to_b40(x: Field): [] { b40 = disclose(x) as Bytes<40>; }
export circuit b4_to_vec(x: Bytes<4>): [] { v4 = disclose(x) as Vector<4, Uint<8>>; }
export circuit vec_to_b4(x: Vector<4, Uint<8>>): [] { b4 = disclose(x) as Bytes<4>; }
export circuit b33_to_vec(x: Bytes<33>): [] { v33 = disclose(x) as Vector<33, Uint<8>>; }
export circuit vec33_to_b33(x: Vector<33, Uint<8>>): [] { b33 = disclose(x) as Bytes<33>; }
export circuit enum_to_field(x: E): [] { f = disclose(x) as Field; }
export circuit enum_to_u8(x: E): [] { u8 = disclose(x) as Uint<8>; }
export circuit field_to_enum(x: Field): [] { e = disclose(x) as E; }
export circuit u8_to_enum(x: Uint<8>): [] { e = disclose(x) as E; }
export circuit u16_to_b4(x: Uint<16>): [] { b4 = disclose(x) as Bytes<4>; }
export circuit b4_to_u16(x: Bytes<4>): [] { u16 = disclose(x) as Uint<16>; }
export circuit bool_to_u8(x: Boolean): [] { u8 = disclose(x) as Uint<8>; }
export circuit u8_to_bool(x: Uint<8>): [] { bo = disclose(x) as Boolean; }
export circuit field_to_bool(x: Field): [] { bo = disclose(x) as Boolean; }
export circuit bool_to_field(x: Boolean): [] { f = disclose(x) as Field; }
```

The `#guard`s list the instructions of each emitted circuit after the input
range checks. They are compactc's instructions (for `Bytes<33> as Vector` Damp takes the
low limb apart first, compactc the high one), except that compactc
first `copy`s a value it range-checks (`Field as Bytes<4>`, `Bytes<4> as
Uint<16>`, `Field as E`, the last byte of `Bytes as Vector`), and rebuilds a limb
from bytes with one `reconstitute_field` per byte where Damp uses a `mul` and an
`add`. `Bytes<32> as Field` (a `reconstitute_field` that checks for overflow) is
reported as unsupported. -/
namespace Examples.Casts
open Damp

enum E where
  | a
  | b
  | c

ledger
  f : Cell Field
  b32 : Cell (Bytes 32)
  b4 : Cell (Bytes 4)
  b31 : Cell (Bytes 31)
  v4 : Cell (Vector Uint8 4)
  e : Cell E
  u8 : Cell Uint8
  u16 : Cell Uint16
  bo : Cell Boolean
  b40 : Cell (Bytes 40)
  v33 : Cell (Vector Uint8 33)
  b33 : Cell (Bytes 33)

circuit b4_to_field (x : Bytes 4) : Unit := f.write (disclose x).toField
circuit b31_to_field (x : Bytes 31) : Unit := f.write (disclose x).toField
circuit field_to_b32 (x : Field) : Unit := do b32.write (← (disclose x).toBytes 32)
circuit field_to_b4 (x : Field) : Unit := do b4.write (← (disclose x).toBytes 4)
circuit field_to_b31 (x : Field) : Unit := do b31.write (← (disclose x).toBytes 31)
circuit field_to_b40 (x : Field) : Unit := do b40.write (← (disclose x).toBytes 40)
circuit b4_to_vec (x : Bytes 4) : Unit := v4.write (disclose x).toVector
circuit vec_to_b4 (x : Vector Uint8 4) : Unit := b4.write (Bytes.ofVector (disclose x))
circuit b33_to_vec (x : Bytes 33) : Unit := v33.write (disclose x).toVector
circuit vec33_to_b33 (x : Vector Uint8 33) : Unit := b33.write (Bytes.ofVector (disclose x))
circuit enum_to_field (x : E) : Unit := f.write (Enum.toField (disclose x))
circuit enum_to_u8 (x : E) : Unit := u8.write (Enum.toUint (disclose x)).widen
circuit field_to_enum (x : Field) : Unit := do e.write (← (disclose x).toEnum E)
circuit u8_to_enum (x : Uint8) : Unit := do e.write (← (disclose x).toEnum E)
circuit u16_to_b4 (x : Uint16) : Unit := do b4.write (← (disclose x).toBytes 4)
circuit b4_to_u16 (x : Bytes 4) : Unit := do u16.write (← (disclose x).toUint 65535)
circuit bool_to_u8 (x : Boolean) : Unit := u8.write (disclose x).toUint.widen
circuit u8_to_bool (x : Uint8) : Unit := bo.write (disclose x).toBoolean
circuit field_to_bool (x : Field) : Unit := bo.write (disclose x).toBoolean
circuit bool_to_field (x : Boolean) : Unit := f.write (disclose x).toField

/-- Not supported: Damp's IR cannot express compactc's overflow check. -/
def b32_to_field (x : Bytes 32) : CircuitM Unit := f.write (disclose x).toField

contract casts

/-- The operation of each emitted instruction, with the operands that tell
    the casts apart, after the circuit's input range checks. -/
def body (c : IR.Circuit) : List String :=
  match Emit.circuit c with
  | .error e => ["error: " ++ e]
  | .ok src =>
    let ins := src.instructions.toList.map fun i =>
      match i.toJson.getObjValAs? String "op" with
      | .ok op =>
        let num (k : String) := match i.toJson.getObjVal? k with
          | .ok v => " " ++ k ++ "=" ++ v.compress
          | .error _ => ""
        op ++ (if op == "impact" then "" else num "bits")
      | .error _ => "?"
    let width : Option IR.Range → Nat
      | some (.below ..) => 2
      | some _ => 1
      | none => 0
    let checks := (c.inputs.map fun i => width i.range).sum
    (ins.drop checks).filter (· != "impact")

#guard body b4_to_field.circuit == []
#guard body b31_to_field.circuit == []
#guard body field_to_b32.circuit == ["div_mod_power_of_two bits=248"]
#guard body field_to_b40.circuit == ["div_mod_power_of_two bits=248"]
#guard body field_to_b4.circuit == ["constrain_bits bits=32"]
#guard body field_to_b31.circuit == ["constrain_bits bits=248"]
#guard body b4_to_vec.circuit == List.replicate 3 "div_mod_power_of_two bits=8"
#guard body vec_to_b4.circuit == List.flatten (List.replicate 3 ["mul", "add"])
#guard body b33_to_vec.circuit == List.replicate 31 "div_mod_power_of_two bits=8"
#guard body vec33_to_b33.circuit == List.flatten (List.replicate 31 ["mul", "add"])
#guard body enum_to_field.circuit == []
#guard body enum_to_u8.circuit == []
#guard body field_to_enum.circuit == ["less_than bits=2", "assert"]
#guard body u8_to_enum.circuit == ["less_than bits=2", "assert"]
#guard body u16_to_b4.circuit == ["constrain_bits bits=32"]
#guard body b4_to_u16.circuit == ["constrain_bits bits=16"]
#guard body bool_to_u8.circuit == []
#guard body u8_to_bool.circuit == ["test_eq", "cond_select"]
#guard body field_to_bool.circuit == ["test_eq", "cond_select"]
#guard body bool_to_field.circuit == []

-- `Bytes<32> as Field` is reported when the circuit is checked.
#guard (circuitProblem (mkCircuit "b32_to_field" ["x"] b32_to_field)).isSome

end Examples.Casts
