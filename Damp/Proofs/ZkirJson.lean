/-
The ZKIR file means the `IrSource`: reading back what the printer writes.

The emitter's theorems are about a Lean value `src : Zkir.IrSource`. What is
shipped is the text `src.toJson.pretty ++ "\n"` (`Contract.write`,
`Damp/Compile/Export.lean`), which Midnight's Rust loader reads. Damp's own
reader, `Zkir.IrSource.ofJson` (`Damp/Zkir/Json.lean`), follows the Rust
loader's rules. This file proves, at the level of the JSON tree:

    IrSource.ofJson src.toJson = .ok src

for every `src` whose immediates are field elements in the loader's sense
(`IrSource.OK`: each immediate `v` has `|v| < Fr.modulus`). Without that
condition the statement is false (see `bigConst` at the end of this file);
`Emit.circuit` checks it (`IrSource.checkImmediates`, part of
`checkProducer`), so it holds of everything the emitter returns
(`IrSource.ofJson_toJson_of_emitted`).

The text layer is `Damp/Proofs/ZkirText.lean` (`IrSource.ofText`), for Damp's
reference JSON parser; Lean core's `Json.pretty` and `Json.parse` are `partial`
and are tested against it (`test/jsontext.sh`).
-/
import Damp.Zkir.Json
import Damp.Compile.Build
import Std.Data.String.ToNat
import Std.Data.TreeMap.Raw.Lemmas

namespace Damp.Zkir
open Lean (Json)

namespace JsonRT

/-! ## Hex immediates -/

theorem hexDigit_digitChar : ∀ d, d < 16 → hexDigit (Nat.digitChar d) = some d := by
  decide

theorem hexByte_toList (b : Nat) (hb : b < 256) :
    (hexByte b).toList = [Nat.digitChar (b / 16), Nat.digitChar (b % 16)] := by
  unfold hexByte
  simp only [String.toList_ofList]
  by_cases h : b < 16
  · rw [Nat.toDigits_of_lt_base h]
    have h1 : b / 16 = 0 := Nat.div_eq_of_lt h
    have h2 : b % 16 = b := Nat.mod_eq_of_lt h
    simp [h1, h2, Nat.digitChar]
  · rw [Nat.toDigits_of_base_le (by omega) (by omega),
      Nat.toDigits_of_lt_base (n := b / 16) (by omega)]
    simp

theorem leBytes_lt : ∀ n, ∀ b ∈ leBytes n, b < 256 := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro b hb
    rw [leBytes] at hb
    split at hb
    · simp at hb; omega
    · simp at hb
      rcases hb with rfl | hb
      · exact Nat.mod_lt _ (by omega)
      · exact ih (n / 256) (by omega) b hb

theorem leValue_leBytes : ∀ n, leValue (leBytes n) = n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [leBytes]
    split
    · simp [leValue]
    · have := ih (n / 256) (by omega)
      simp only [leValue, List.foldr_cons] at this ⊢
      rw [this]; omega

theorem leBytes_length : ∀ k n, 0 < k → n < 256 ^ k → (leBytes n).length ≤ k := by
  intro k
  induction k with
  | zero => intro n h; omega
  | succ k ih =>
    intro n _ hn
    rw [leBytes]
    split
    · simp only [List.length_cons, List.length_nil]; omega
    · simp only [List.length_cons]
      have : 0 < k := by
        cases k with
        | zero => simp at hn; omega
        | succ k => omega
      have h2 : n / 256 < 256 ^ k := by
        rw [Nat.pow_succ] at hn
        exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hn)
      have := ih (n / 256) this h2
      omega

theorem hexBytes_flatMap : ∀ l : List Nat, (∀ b ∈ l, b < 256) →
    hexBytes (l.flatMap fun b => (hexByte b).toList) = some l
  | [], _ => rfl
  | b :: l, h => by
      have hb := h b (by simp)
      simp only [List.flatMap_cons, hexByte_toList b hb, List.cons_append, List.nil_append]
      simp only [hexBytes, hexDigit_digitChar _ (Nat.div_lt_of_lt_mul (by omega : b < 16 * 16)),
        hexDigit_digitChar _ (Nat.mod_lt _ (by omega : 16 > 0)),
        hexBytes_flatMap l (fun x hx => h x (by simp [hx]))]
      simp only [bind, Option.bind, pure, Option.some.injEq, List.cons.injEq, and_true]
      omega

theorem leHex_toList (n : Nat) : (leHex n).toList = (leBytes n).flatMap fun b => (hexByte b).toList := by
  simp [leHex, String.toList_join, List.flatMap_map]

theorem leBytes_ne_nil (n : Nat) : leBytes n ≠ [] := by
  rw [leBytes]; split <;> simp

theorem modulus_lt : Fr.modulus < 256 ^ 32 := by decide

theorem parseImmBody_leHex (s : String) (n : Nat) (hn : n < Fr.modulus) :
    parseImmBody s (leHex n).toList = .ok n := by
  have hne : ((leBytes n).flatMap fun b => (hexByte b).toList).isEmpty = false := by
    obtain ⟨b, l, hbl⟩ : ∃ b l, leBytes n = b :: l := by
      cases h : leBytes n with
      | nil => exact absurd h (leBytes_ne_nil n)
      | cons b l => exact ⟨b, l, rfl⟩
    rw [hbl]
    simp [hexByte_toList b (leBytes_lt n b (by simp [hbl]))]
  have hlen : ¬ (leBytes n).length > 32 := by
    have := leBytes_length 32 n (by omega) (Nat.lt_trans hn modulus_lt)
    omega
  have hv : ¬ n ≥ Fr.modulus := by omega
  simp only [parseImmBody, leHex_toList, hne, hexBytes_flatMap _ (leBytes_lt n), hlen,
    leValue_leBytes, hv]
  rfl

/-! ## Registers and operands -/

theorem Ident.toString_toList (i : Ident) :
    i.toString.toList = '%' :: (i.hint.toList ++ '.' :: Nat.toDigits 10 i.id) := by
  have h1 : (ToString.toString "%").toList = ['%'] := by decide
  have h2 : (ToString.toString ".").toList = ['.'] := by decide
  simp [Ident.toString, String.toList_append, Nat.toString_eq_repr, Nat.toList_repr, h1, h2]
  rfl

theorem toNat!_of_toNat? {s : String} {n : Nat} (h : s.toNat? = some n) : s.toNat! = n := by
  simp only [String.toNat?, String.Slice.toNat?] at h
  simp only [String.toNat!, String.Slice.toNat!]
  split at h
  · rename_i hn; simp only [hn, ite_true]; cases h; rfl
  · cases h

theorem parseIdent_toString (i : Ident) : parseIdent i.toString = .ok i := by
  have hd : ∀ c ∈ (Nat.toDigits 10 i.id).reverse, c.isDigit = true := by
    intro c hc
    exact Nat.isDigit_of_mem_toDigits (by omega) (by omega) (List.mem_reverse.mp hc)
  have htw : (i.hint.toList ++ '.' :: Nat.toDigits 10 i.id).reverse.takeWhile Char.isDigit =
      (Nat.toDigits 10 i.id).reverse := by
    rw [List.reverse_append, List.reverse_cons, List.append_assoc, List.takeWhile_append_of_pos hd]
    simp
  have hne : (Nat.toDigits 10 i.id).isEmpty = false := by
    cases h : Nat.toDigits 10 i.id with
    | nil => exact absurd h Nat.toDigits_ne_nil
    | cons => rfl
  have hpre : (i.hint.toList ++ '.' :: Nat.toDigits 10 i.id).take
      ((i.hint.toList ++ '.' :: Nat.toDigits 10 i.id).length - (Nat.toDigits 10 i.id).length) =
      i.hint.toList ++ ['.'] := by
    have : i.hint.toList ++ '.' :: Nat.toDigits 10 i.id = (i.hint.toList ++ ['.']) ++ Nat.toDigits 10 i.id := by
      simp
    rw [this, List.take_left' (by simp; omega)]
  have hnat : (String.ofList (Nat.toDigits 10 i.id)).toNat! = i.id := by
    apply toNat!_of_toNat?
    rw [← Nat.repr_eq_ofList_toDigits]
    exact Nat.toNat?_repr i.id
  simp only [parseIdent, Ident.toString_toList, htw, List.reverse_reverse, hne, hpre,
    List.getLast?_append, List.getLast?_singleton, List.dropLast_concat, String.ofList_toList, hnat]
  rfl

/-- What `Operand.toJson` prints, as a string. -/
def _root_.Damp.Zkir.Operand.str : Operand → String
  | .var n => n.toString
  | .imm v => (if v < 0 then "-0x" else "0x") ++ leHex v.natAbs

theorem Operand.toJson_eq (o : Operand) : o.toJson = .str o.str := by
  cases o <;> rfl

/-- An operand the loader accepts: an immediate must be a field element in
    absolute value (the loader reads at most 32 bytes, below the modulus). -/
def _root_.Damp.Zkir.Operand.OK : Operand → Prop
  | .var _ => True
  | .imm v => v.natAbs < Fr.modulus

theorem parseOperandStr_str (o : Operand) (h : o.OK) : parseOperandStr o.str = .ok o := by
  cases o with
  | var n =>
      unfold parseOperandStr
      simp only [Operand.str, Ident.toString_toList]
      simp [parseIdent_toString, Functor.map, Except.map]
  | imm v =>
      simp only [Operand.OK] at h
      unfold parseOperandStr
      by_cases hv : v < 0
      · simp only [Operand.str, hv, ite_true, String.toList_append]
        simp [parseImmBody_leHex _ _ h, bind, Except.bind, pure, Except.pure]
        try omega
      · simp only [Operand.str, hv, ite_false, String.toList_append]
        simp [parseImmBody_leHex _ _ h, bind, Except.bind, pure, Except.pure]
        try omega

/-! ## Objects -/

theorem lookup_mem' : ∀ {l : List (String × Json)} {k : String} {v : Json}, l.lookup k = some v → (k, v) ∈ l
  | [], _, _, h => by simp [List.lookup] at h
  | (a, b) :: l, k, v, h => by
      simp only [List.lookup] at h
      split at h
      · rename_i hk; simp at hk; subst hk; cases h; simp
      · exact List.mem_cons_of_mem _ (lookup_mem' h)

theorem lookup_none' : ∀ {l : List (String × Json)} {k : String}, l.lookup k = none →
    (l.map Prod.fst).contains k = false
  | [], _, _ => rfl
  | (a, b) :: l, k, h => by
      simp only [List.lookup] at h
      split at h
      · cases h
      · rename_i hk
        simp only [List.map_cons, List.contains_cons, Bool.or_eq_false_iff]
        refine ⟨?_, lookup_none' h⟩
        simp at hk ⊢; exact hk

/-- A field of an object built by `Json.mkObj` from distinct keys is what the
    list gives for it. -/
theorem getObjVal?_mkObj (l : List (String × Json)) (k : String) (hd : (l.map Prod.fst).Nodup) :
    (Json.mkObj l).getObjVal? k =
      match l.lookup k with
      | some v => .ok v
      | none => .error s!"property not found: {k}" := by
  simp only [Json.mkObj, Json.getObjVal?]
  have hpw : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
    have := List.pairwise_map.mp hd
    exact this.imp (fun h e => h (Std.LawfulEqCmp.eq_of_compare e))
  cases hl : l.lookup k with
  | some v =>
      rw [Std.TreeMap.Raw.get?_eq_getElem?,
        Std.TreeMap.Raw.getElem?_ofList_of_mem (Std.ReflCmp.compare_self) hpw (lookup_mem' hl)]
      rfl
  | none =>
      rw [Std.TreeMap.Raw.get?_eq_getElem?,
        Std.TreeMap.Raw.getElem?_ofList_of_contains_eq_false (lookup_none' hl)]
      rfl

/-! ## Scalars inside JSON -/

theorem getNat?_nat (n : Nat) : Json.getNat? (n : Json) = .ok n := rfl

/-- What `IrType.toJson` prints, as a string. -/
def _root_.Damp.Zkir.IrType.str : IrType → String
  | .native => "Scalar<BLS12-381>"
  | .bytes32 => "Bytes<32>"
  | .jubjubPoint => "Point<Jubjub>"
  | .jubjubScalar => "Scalar<Jubjub>"

theorem IrType.toJson_eq (t : IrType) : t.toJson = .str t.str := by cases t <;> rfl

theorem parseType_str (t : IrType) : parseType t.str = .ok t := by cases t <;> rfl

theorem parseAtom_toJson (a : AlignAtom) : parseAtom a.toJson = .ok a := by
  cases a <;>
    simp [AlignAtom.toJson, parseAtom, getStr, getField, getObjVal?_mkObj, List.lookup, getNat,
      getNat?_nat, bind, Except.bind, pure, Except.pure, Functor.map, Except.map]

theorem mapM_parseAtom : ∀ l : List AlignAtom,
    (l.map AlignAtom.toJson).mapM parseAtom = .ok l
  | [] => rfl
  | a :: l => by
      simp [List.mapM_cons, parseAtom_toJson, mapM_parseAtom l, bind, Except.bind, pure, Except.pure]

theorem mapM_parseOperand : ∀ l : List Operand, (∀ o ∈ l, o.OK) →
    ((l.map Operand.toJson).mapM fun x => do parseOperandStr (← asStr x)) = .ok l
  | [], _ => rfl
  | a :: l, h => by
      have ha := parseOperandStr_str a (h a (by simp))
      have hl := mapM_parseOperand l (fun o ho => h o (by simp [ho]))
      rw [List.map_cons, List.mapM_cons, hl]
      simp [Operand.toJson_eq, asStr, ha, bind, Except.bind, pure, Except.pure]

theorem mapM_parseIdent : ∀ l : List Ident,
    ((l.map fun i => Json.str i.toString).mapM fun x => do parseIdent (← asStr x)) = .ok l
  | [] => rfl
  | a :: l => by
      rw [List.map_cons, List.mapM_cons, mapM_parseIdent l]
      simp [asStr, parseIdent_toString, bind, Except.bind, pure, Except.pure]

/-! ## Instructions

`Instr.toJson` is written with private helpers; `Instr.json` is the same
function with public ones, so that its cases can be unfolded here. -/

def jobj (op : String) (fields : List (String × Json)) : Json :=
  Json.mkObj (("op", Json.str op) :: fields)
def jops (l : List Operand) : Json := .arr (l.map Operand.toJson).toArray
def jids (l : List Ident) : Json := .arr (l.map fun i => Json.str i.toString).toArray
def jguard : Option Operand → Json
  | none => .null
  | some g => g.toJson

def _root_.Damp.Zkir.Instr.json : Instr → Json
  | .encode i os => jobj "encode" [("input", i.toJson), ("outputs", jids os)]
  | .assert c => jobj "assert" [("cond", c.toJson)]
  | .condSelect o bit a b =>
      jobj "cond_select" [("output", o), ("bit", bit.toJson), ("a", a.toJson), ("b", b.toJson)]
  | .constrainBits v b => jobj "constrain_bits" [("val", v.toJson), ("bits", b)]
  | .constrainEq a b => jobj "constrain_eq" [("a", a.toJson), ("b", b.toJson)]
  | .constrainToBoolean v => jobj "constrain_to_boolean" [("val", v.toJson)]
  | .copy o v => jobj "copy" [("output", o), ("val", v.toJson)]
  | .impact g is => jobj "impact" [("guard", g.toJson), ("inputs", jops is)]
  | .ecMul o a s => jobj "ec_mul" [("output", o), ("a", a.toJson), ("scalar", s.toJson)]
  | .ecMulGenerator o s => jobj "ec_mul_generator" [("output", o), ("scalar", s.toJson)]
  | .hashToCurve o is => jobj "hash_to_curve" [("output", o), ("inputs", jops is)]
  | .intoCoordinates (x, y) p => jobj "into_coordinates" [("outputs", jids [x, y]), ("point", p.toJson)]
  | .fromCoordinates o (x, y) => jobj "from_coordinates" [("output", o), ("inputs", jops [x, y])]
  | .divModPowerOfTwo os v b =>
      jobj "div_mod_power_of_two" [("outputs", jids os), ("val", v.toJson), ("bits", b)]
  | .reconstituteField o d m b =>
      jobj "reconstitute_field" [("output", o), ("divisor", d.toJson), ("modulus", m.toJson), ("bits", b)]
  | .transientHash o is => jobj "transient_hash" [("output", o), ("inputs", jops is)]
  | .persistentHash o al is =>
      jobj "persistent_hash"
        [("output", o), ("alignment", .arr (al.map AlignAtom.toJson).toArray), ("inputs", jops is)]
  | .testEq o a b => jobj "test_eq" [("output", o), ("a", a.toJson), ("b", b.toJson)]
  | .add o a b => jobj "add" [("output", o), ("a", a.toJson), ("b", b.toJson)]
  | .mul o a b => jobj "mul" [("output", o), ("a", a.toJson), ("b", b.toJson)]
  | .neg o a => jobj "neg" [("output", o), ("a", a.toJson)]
  | .inv o a => jobj "inv" [("output", o), ("a", a.toJson)]
  | .not o a => jobj "not" [("output", o), ("a", a.toJson)]
  | .lessThan o a b bits =>
      jobj "less_than" [("output", o), ("a", a.toJson), ("b", b.toJson), ("bits", bits)]
  | .jubjubScalarFromNative o n => jobj "jubjub_scalar_from_native" [("output", o), ("native", n.toJson)]
  | .publicInput t o g => jobj "public_input" [("type", t.toJson), ("output", o), ("guard", jguard g)]
  | .privateInput t o g => jobj "private_input" [("type", t.toJson), ("output", o), ("guard", jguard g)]
  | .output vs => jobj "output" [("vals", jops vs)]
  | .bytesIntoNatives os b => jobj "bytes_into_natives" [("outputs", jids os), ("bytes", b.toJson)]
  | .bytesFromNatives o is len =>
      jobj "bytes_from_natives" [("output", o), ("inputs", jops is), ("len", len)]

theorem Instr.toJson_eq_json (i : Instr) : i.toJson = i.json := by
  cases i <;> rfl

/-- Every immediate an instruction reads is one the loader accepts. -/
def _root_.Damp.Zkir.Instr.OK (i : Instr) : Prop := ∀ o ∈ i.uses, o.OK

theorem guard_jguard (l : List (String × Json)) (hd : (l.map Prod.fst).Nodup) (g : Option Operand)
    (hg : ∀ o ∈ g.toList, o.OK) (hl : l.lookup "guard" = some (jguard g)) :
    guard (Json.mkObj l) = .ok g := by
  simp only [guard, getObjVal?_mkObj l _ hd, hl]
  cases g with
  | none => rfl
  | some o =>
      simp only [jguard, Operand.toJson_eq]
      simp [parseOperandStr_str o (hg o (by simp)), Functor.map, Except.map]

theorem ok_bind' {ε α β : Type} (a : α) (f : α → Except ε β) :
    ((Except.ok a : Except ε α) >>= f) = f a := rfl
theorem pure_ok' {ε α : Type} (a : α) : (pure a : Except ε α) = .ok a := rfl
theorem ok_map' {ε α β : Type} (a : α) (f : α → β) : (f <$> (Except.ok a : Except ε α)) = .ok (f a) := rfl

/-- The rewrites that read a printed instruction back. -/
local macro "instr_simp" : tactic =>
  `(tactic| simp (disch := simp_all) only [Instr.json, jobj, jops, jids, parseInstr, getStr, getField,
      getObjVal?_mkObj, List.lookup, operand, operands, ident, idents, getArr, getNat, getNat?_nat, guard,
      jguard, IrType.toJson_eq, parseType_str, Operand.toJson_eq, parseOperandStr_str, mapM_parseOperand,
      mapM_parseIdent, parseIdent_toString, mapM_parseAtom, List.toList_toArray, ok_bind', pure_ok', ok_map',
      beq_self_eq_true, String.reduceBEq])

set_option maxHeartbeats 4000000 in
/-- **An instruction reads back as itself.** -/
theorem parseInstr_toJson (i : Instr) (h : i.OK) : parseInstr i.toJson = .ok i := by
  rw [Instr.toJson_eq_json]
  unfold Instr.OK at h
  cases i
  all_goals simp only [Instr.uses, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      Option.toList] at h
  case publicInput t o g => cases g <;> (try simp only [List.not_mem_nil, List.mem_cons, or_false, forall_eq] at h) <;>
      instr_simp
  case privateInput t o g => cases g <;> (try simp only [List.not_mem_nil, List.mem_cons, or_false, forall_eq] at h) <;>
      instr_simp
  all_goals instr_simp

/-! ## Circuits -/

/-- Every immediate of the circuit is one the loader accepts. -/
def _root_.Damp.Zkir.IrSource.OK (s : IrSource) : Prop := ∀ i ∈ s.instructions.toList, i.OK

theorem mapM_parseInstr : ∀ l : List Instr, (∀ i ∈ l, i.OK) → (l.map Instr.toJson).mapM parseInstr = .ok l
  | [], _ => rfl
  | i :: l, h => by
      rw [List.map_cons, List.mapM_cons, parseInstr_toJson i (h i (by simp)),
        mapM_parseInstr l (fun j hj => h j (by simp [hj]))]
      rfl

theorem mapM_parseInput : ∀ l : List (Ident × IrType),
    List.mapM (fun i => do
        let a ← ident i "name"
        let b ← getStr i "type"
        let c ← parseType b
        Except.ok (a, c))
      (l.map fun x => Json.mkObj [("name", Json.str x.fst.toString), ("type", x.snd.toJson)]) = .ok l
  | [] => rfl
  | (n, t) :: l => by
      rw [List.map_cons, List.mapM_cons, mapM_parseInput l]
      simp (disch := simp) only [ident, getStr, getField, getObjVal?_mkObj, List.lookup, IrType.toJson_eq,
        parseType_str, parseIdent_toString, ok_bind', pure_ok', beq_self_eq_true, String.reduceBEq]

theorem mapM_parseOutput : ∀ l : List IrType,
    ((l.map IrType.toJson).mapM fun t => do parseType (← asStr t)) = .ok l
  | [] => rfl
  | t :: l => by
      rw [List.map_cons, List.mapM_cons, mapM_parseOutput l, IrType.toJson_eq]
      simp only [asStr, ok_bind', parseType_str, pure_ok']

end JsonRT
open JsonRT

/-- **A circuit reads back as itself** (at the level of the JSON tree): Damp's
    reader, which follows Midnight's loader, returns exactly `src` from
    `src.toJson`, provided every immediate is a field element the loader
    accepts. -/
theorem IrSource.ofJson_toJson (src : IrSource) (h : src.OK) : IrSource.ofJson src.toJson = .ok src := by
  have hins : (src.instructions.map Instr.toJson).mapM parseInstr = .ok src.instructions := by
    rw [Array.mapM_eq_mapM_toList, Array.toList_map, mapM_parseInstr _ h]
    rfl
  have h3 : Json.getNat? (3 : Json) = .ok 3 := rfl
  simp (disch := simp) only [IrSource.ofJson, IrSource.toJson, getField, getObjVal?_mkObj, List.lookup, getNat,
    getArr, h3, mapM_parseOutput, hins, ok_bind', pure_ok',
    beq_self_eq_true, String.reduceBEq, ↓reduceIte]
  rw [mapM_parseInput]
  rfl

/-! ## A decidable form of the condition -/

-- `Operand.okB` and `IrSource.okB` are defined in `Damp/Zkir/Checks.lean`,
-- where `IrSource.checkProducer` uses them.

theorem IrSource.ok_of_okB (s : IrSource) (h : s.okB = true) : s.OK := by
  intro i hi o ho
  simp only [IrSource.okB, Array.all_eq_true_iff_forall_mem, List.all_eq_true] at h
  have := h i (Array.mem_toList_iff.mp hi) o ho
  cases o with
  | var _ => trivial
  | imm v => simpa [Operand.okB, Operand.OK] using this

theorem IrSource.ofJson_toJson_of_okB (src : IrSource) (h : src.okB = true) :
    IrSource.ofJson src.toJson = .ok src :=
  IrSource.ofJson_toJson src (IrSource.ok_of_okB src h)

/-- What the emitter returns reads back as itself: `Emit.circuit` runs
    `checkProducer`, which includes the immediates check. -/
theorem IrSource.ofJson_toJson_of_emitted {c : IR.Circuit} {src : IrSource} (h : Emit.circuit c = .ok src) :
    IrSource.ofJson src.toJson = .ok src := by
  apply IrSource.ofJson_toJson_of_okB
  apply IrSource.okB_of_checkProducer
  unfold Emit.circuit at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  · cases hcore : Emit.circuitCore (Emit.pruned c) with
    | error m => simp [hcore, bind, Except.bind] at h
    | ok src' =>
        cases hchk : src'.checkProducer with
        | error m => simp [hcore, hchk, bind, Except.bind] at h
        | ok u =>
            simp [hcore, hchk, bind, Except.bind, pure, Except.pure] at h
            subst h; cases u; exact hchk

/-! ## The condition is needed, and the emitter checks it

An IR constant is emitted as an immediate unchanged (`Emit.expr`). A constant
`c` with `|c| ≥ Fr.modulus` would give ZKIR that the theorems describe (an
immediate is read as `Fr.ofInt c`) but whose file Midnight's loader, and
Damp's reader, refuse. The surface language never produces one (a `Field`
literal is reduced modulo the field size, `Damp/Lang/Contract.lean`), and
`checkProducer`, run by `Emit.circuit`, refuses a circuit that has one, so
such a circuit written directly in the IR is reported where it is declared
(`circuitProblem`). -/

/-- `assert (x == p)`, with `p` the field modulus. -/
def bigConst : IR.Circuit :=
  { name := "big", args := [], inputs := [⟨"x", 0, none⟩],
    body := #[.assert (.eq (.var 0) (.const (Fr.modulus : Int))) "m"],
    result := .tuple [], outputs := [] }

-- The immediate is out of range, so the reader refuses the printed file ...
#guard (IrSource.ofJson
  ({ inputs := [(⟨"x", 0⟩, .native)], outputs := [],
     instructions := #[.testEq ⟨"m", 1⟩ (.var ⟨"x", 0⟩) (.imm Fr.modulus), .assert (.var ⟨"m", 1⟩)] } :
    IrSource).toJson).isOk
  == false
-- ... and the emitter refuses the circuit, naming the constant, at every level.
#guard match Emit.circuit bigConst with
  | .ok _ => false
  | .error e => (e.splitOn (toString Fr.modulus)).length > 1
#guard (Emit.circuit bigConst.optimize).isOk == false
#guard (circuitProblem bigConst).isSome

-- In the surface language the literal `p + 1` is the field element `1`.
#guard (OfNat.ofNat (Fr.modulus + 1) : Damp.Field).expr == .const 1
#guard (Damp.Field.ofNat (2 * Fr.modulus + 5)).expr == .const 5
#guard (Damp.Field.ofString "abc").expr == .const 6513249

end Damp.Zkir
