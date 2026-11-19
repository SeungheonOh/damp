/-
Byte strings over 31 bytes: the executor's two conversions are inverse on
every value Damp's typed interface produces.

A `Bytes n` with `n > 31` is `L = byteLimbs n` field elements in a circuit
(limbs of 248 bits, most significant first; the first holds the
`n − 31·(L−1)` leftover bytes) and one atom of `n` bytes in a ledger cell. The
executor joins the limbs when it writes (`alignedOfFields`, modelled by
`AV.ofFields`/`atomOfFields`: shift by 248 bits and `or`, keep `n` bytes) and
splits them when it reads (`fieldsOfAligned`, `fieldsOfAtom`).

Joining is lossy only for limbs out of range (a first limb of more than
`8·(n − 31·(L−1))` bits, or another of more than 248): the extra bits are cut
off, where a single-limb atom that does not fit is rejected by the runtime.
Every `Bytes n` a circuit gets from its typed interface has its limbs in range:
arguments and witness results are range-checked (`Ty.ranges`), hashes and
constants are built in range, ledger reads come back split by `fieldsOfAtom`.
Out-of-range limbs need a `Bytes` built from raw expressions.

`fieldsOf_ofFields_ranges` is the round trip for every alignment Damp derives
from a type, given the type's range checks hold of the field elements;
`Cell.write_read_ranges` and `Map.insert_lookup_ranges` are `Cell.write_read`
and `Map.insert_lookup` without the single-limb restriction. The only
primitive types excluded (`Ty.LimbsAgree`) are `Bytes 0` (no field element,
but an atom the executor reads one element for) and `Uint`s past Compact's
limit (which have no value at all).
-/
import Damp.Proofs.Ledger.Map
import Damp.Proofs.Interface.Bytes

namespace Damp.Ledger
open Damp.IR Damp.Impact

set_option linter.unusedSimpArgs false

/-- The executor's conversion of this type's alignment atom takes as many field
    elements as the type occupies in a circuit. True of every primitive type
    except `Bytes 0` and a `Uint`/enum past Compact's limit (`Ty.limbsAgree_*`). -/
def Ty.LimbsAgree (t : Ty) : Prop := atomWidth t.align = t.width

theorem Ty.limbsAgree_field : Ty.LimbsAgree .field := rfl
theorem Ty.limbsAgree_bool : Ty.LimbsAgree .bool := rfl

theorem Ty.limbsAgree_bytes {n : Nat} (h : 0 < n) : Ty.LimbsAgree (.bytes n) := by
  simp only [Ty.LimbsAgree, Ty.align, Ty.width, Ty.ranges, atomWidth, List.length_map, List.length_range,
    byteLimbs]
  omega

theorem bitLen_le_of_lt {m k : Nat} (h : m < 2 ^ k) : bitLen m ≤ k := by
  unfold bitLen
  split
  · omega
  · have := Nat.log2_lt (n := m) (by omega) |>.2 h
    omega

theorem Ty.ranges_uint_length (m : Nat) : (Ty.ranges (.uint m)).length = 1 := by
  simp only [Ty.ranges]; split <;> (try split) <;> (try split) <;> rfl

theorem Ty.ranges_enum_length (m : Nat) : (Ty.ranges (.enum m)).length = 1 := by
  simp only [Ty.ranges]; split <;> (try split) <;> (try split) <;> rfl

theorem Ty.limbsAgree_uint {m : Nat} (h : m ≤ Uint.maxBound) : Ty.LimbsAgree (.uint m) := by
  have hb : bitLen m ≤ 248 := bitLen_le_of_lt (by unfold Uint.maxBound at h; omega)
  simp only [Ty.LimbsAgree, Ty.align, Ty.width, Ty.ranges_uint_length, atomWidth]
  omega

theorem Ty.limbsAgree_enum {m : Nat} (h : m ≤ Uint.maxBound) : Ty.LimbsAgree (.enum m) := by
  have hb : bitLen m ≤ 248 := bitLen_le_of_lt (by unfold Uint.maxBound at h; omega)
  simp only [Ty.LimbsAgree, Ty.align, Ty.width, Ty.ranges_enum_length, atomWidth]
  omega

/-! ## Joining limbs is spelling a number in base `2 ^ 248` -/

/-- Shift-and-or is shift-and-add when each limb is below `2 ^ 248`. -/
theorem foldl_shift_or : ∀ (ys : List Fr) (acc : Nat), (∀ y ∈ ys, y.val < limbBase) →
    ys.foldl (fun x l => (x <<< 248) ||| l.val) acc = ys.foldl (fun a x => a * limbBase + x.val) acc
  | [], _, _ => rfl
  | y :: ys, acc, h => by
    simp only [List.foldl_cons]
    rw [← Nat.shiftLeft_add_eq_or_of_lt (h y (by simp)), Nat.shiftLeft_eq]
    exact foldl_shift_or ys _ fun z hz => h z (by simp [hz])

theorem toNat_eq_foldl_or (ys : List Fr) (h : ∀ y ∈ ys, y.val < limbBase) :
    ys.foldl (fun x l => (x <<< 248) ||| l.val) 0 = Bytes.toNat ys := by
  rw [foldl_shift_or ys 0 h]; rfl

/-- The limbs of a number below `2 ^ (248·L)` spell it back. -/
theorem limbVals_toNat {ys : List Fr} (h : ∀ y ∈ ys, y.val < limbBase) :
    Bytes.limbVals ys.length (Bytes.toNat ys) = ys := by
  have hlt : Bytes.toNat ys < 2 ^ (248 * ys.length) := by
    rw [toNat_eq_digits, Nat.pow_mul]
    have := foldl_digits_lt limbBase (ys.map Fr.val) (by
      intro d hd; obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hd; exact h y hy)
    simpa using this
  apply Bytes.toNat_inj (by simp [Bytes.limbVals])
  · intro y hy
    simp only [Bytes.limbVals, List.mem_map] at hy
    obtain ⟨j, _, rfl⟩ := hy
    rw [Fr.val_ofNat_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))]
    exact Nat.mod_lt _ (by decide)
  · exact h
  · rw [Bytes.toNat_limbVals, Nat.mod_eq_of_lt hlt]

/-! ## One atom -/

/-- Field elements passing a `Bytes n` value's range checks, joined by the
    executor and split again, come back unchanged; nothing is cut off. -/
theorem bytes_roundtrip {n : Nat} {ys : List Fr} (hn : 31 < n) (hl : ys.length = byteLimbs n)
    (hr : rangesHold (Ty.ranges (.bytes n)) ys = true) :
    atomOfFields (.bytes n) ys = Bytes.toNat ys ∧ Bytes.toNat ys < 2 ^ (8 * n) ∧
      fieldsOfAtom (.bytes n) (Bytes.toNat ys) = some ys := by
  have hr' : rangesHold (Value.ranges (Bytes n)) ys = true := by
    simpa [Value.ranges, Value.shape, Shape.ranges, Shape.tys] using hr
  have hbase := Bytes.limbs_lt_base hl hr'
  have hlt : Bytes.toNat ys < 2 ^ (8 * n) := by
    have := Bytes.toNat_lt hl hr'
    rwa [Nat.pow_mul, show (2 : Nat) ^ 8 = 256 from rfl]
  refine ⟨?_, hlt, ?_⟩
  · simp only [atomOfFields, show n > 31 from hn, ↓reduceIte]
    rw [toNat_eq_foldl_or ys hbase, Nat.mod_eq_of_lt hlt]
  · simp only [fieldsOfAtom, show n > 31 from hn, ↓reduceIte, Nat.mod_eq_of_lt hlt, Option.some.injEq]
    have := limbVals_toNat hbase
    rw [hl] at this
    conv => rhs; rw [← this]
    rfl

/-- One atom of a type whose limbs agree: written and read back, the field
    elements are unchanged, given the type's range checks. -/
theorem atom_roundtrip {t : Ty} (ht : Ty.LimbsAgree t) {ys : List Fr} (hl : ys.length = t.width)
    (hr : rangesHold t.ranges ys = true) :
    fieldsOfAtom t.align (atomOfFields t.align ys) = some ys := by
  by_cases h1 : atomWidth t.align = 1
  · have hy : ys.length = 1 := by rw [hl, ← ht, h1]
    match ys, hy with
    | [y], _ =>
      have hs : ∀ n, t.align = .bytes n → n ≤ 31 := by
        intro n hn; rw [hn] at h1; simp only [atomWidth] at h1; omega
      rw [atomOfFields_singleLimb hs, fieldsOfAtom_singleLimb hs]
  · cases t with
    | field => exact absurd rfl h1
    | bool => exact absurd rfl h1
    | uint m => simp only [Ty.LimbsAgree, Ty.width, Ty.ranges_uint_length] at ht; exact absurd ht h1
    | enum m => simp only [Ty.LimbsAgree, Ty.width, Ty.ranges_enum_length] at ht; exact absurd ht h1
    | bytes n =>
      have hn : 31 < n := by simp only [Ty.align, atomWidth] at h1; omega
      have hl' : ys.length = byteLimbs n := by
        rw [hl]; simp [Ty.width, Ty.ranges]
      obtain ⟨e, -, h⟩ := bytes_roundtrip hn hl' hr
      simp only [Ty.align]; rw [e]; exact h

/-! ## Whole values -/

theorem rangesHold_append {r₁ r₂ : List (Option Range)} {x₁ x₂ : List Fr} (h : r₁.length = x₁.length) :
    rangesHold (r₁ ++ r₂) (x₁ ++ x₂) = (rangesHold r₁ x₁ && rangesHold r₂ x₂) := by
  simp [rangesHold, List.zip_append h]

/-- **The round trip for every alignment Damp derives from types.** Field
    elements passing the types' range checks, converted by the executor to an
    aligned value (`AV.ofFields`) and read back under the same alignment
    (`fieldsOf`), are unchanged, whatever the byte lengths. -/
theorem fieldsOf_ofFields_ranges : ∀ (tys : List Ty) (vs : List Fr) (v : AV),
    (∀ t ∈ tys, Ty.LimbsAgree t) → vs.length = (tys.flatMap Ty.ranges).length →
    rangesHold (tys.flatMap Ty.ranges) vs = true →
    AV.ofFields (tys.map Ty.align) vs = some v → fieldsOf (tys.map Ty.align) v.atoms = some vs
  | [], vs, v, _, hl, _, h => by
      have : vs = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
      subst this
      simp [AV.ofFields] at h; subst h; rfl
  | t :: ts, vs, v, ha, hl, hr, h => by
      have ht : Ty.LimbsAgree t := ha t (by simp)
      have hw : t.ranges.length = atomWidth t.align := ht.symm
      have hsplit : vs = vs.take (atomWidth t.align) ++ vs.drop (atomWidth t.align) := (List.take_append_drop _ _).symm
      simp only [List.flatMap_cons, List.length_append] at hl hr
      have htl : (vs.take (atomWidth t.align)).length = t.ranges.length := by
        simp only [List.length_take]; omega
      rw [hsplit, rangesHold_append htl.symm, Bool.and_eq_true] at hr
      simp only [List.map_cons, AV.ofFields] at h
      split at h
      · simp at h
      split at h
      · simp at h
      cases hrest : AV.ofFields (ts.map Ty.align) (vs.drop (atomWidth t.align)) with
      | none => simp [hrest] at h
      | some r =>
        simp only [hrest, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        have h1 := atom_roundtrip ht (ys := vs.take (atomWidth t.align)) (by rw [htl]; rfl) hr.1
        have h2 := fieldsOf_ofFields_ranges ts _ r (fun x hx => ha x (by simp [hx]))
          (by simp only [List.length_drop]; omega) hr.2 hrest
        simp only [List.map_cons, fieldsOf, h1, h2, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
        rw [← hsplit]

/-- `fieldsOf_ofFields_ranges` for a value type `α`. -/
theorem fieldsOf_ofFields_value {α : Type} [Value α] (hα : ∀ t ∈ Value.tys α, Ty.LimbsAgree t)
    {vs : List Fr} {v : AV} (hl : vs.length = Value.width α) (hr : rangesHold (Value.ranges α) vs = true)
    (h : AV.ofFields (alignOf α) vs = some v) : fieldsOf (alignOf α) v.atoms = some vs :=
  fieldsOf_ofFields_ranges (Value.tys α) vs v hα hl hr h

/-! ## The read-back theorems, for every byte length -/

section
variable {α : Type} [Value α] (H : Hooks) (c : Cell α) (p : Zkir.Prims) (env : Env)
  (σ : LedgerState) (fields : List SV)

/-- **`Cell.write_read`, for every alignment Damp produces.** After `write x`,
    `read` returns exactly the field elements written, for any value type whose
    primitive types agree on their limbs (every type but `Bytes 0` and
    oversized `Uint`s), provided the elements pass the type's range checks (as
    every argument, witness result, hash, constant and ledger read does). In
    particular a `Cell (Bytes 32)` holding 32 bytes `0xff` reads back its two
    limbs `0xff`, `2^248 - 1`. -/
theorem Cell.write_read_ranges (x : α) (vs : List Fr) (v : AV)
    (hst : σ.state = .array fields) (hi : c.index < fields.length) (hb : c.index < 256) (hwf : σ.WF)
    (hx : Expr.evalList p env (Value.toExprs x) = some vs) (hv : AV.ofFields (alignOf α) vs = some v)
    (hα : ∀ t ∈ Value.tys α, Ty.LimbsAgree t) (hlen : vs.length = Value.width α)
    (hr : rangesHold (Value.ranges α) vs = true) (env' : Env) :
    ∃ req₁ req₂ σ₁, (emitted (c.write x)).bind (Exec.request p env) = some req₁ ∧
      ledgerOracle H req₁ σ = some ([], σ₁) ∧
      (emitted c.read).bind (Exec.request p env') = some req₂ ∧
      ledgerOracle H req₂ σ₁ = some (vs, σ₁) := by
  obtain ⟨req₁, h1, h2⟩ := Cell.write_spec H c p env σ fields x vs v hst hi hb hwf hx hv
  have hst' : (σ.setField c.index (.cell v)).state = .array (fields.set c.index (.cell v)) := by
    simp [LedgerState.setField, hst]
  have hwf' : (σ.setField c.index (.cell v)).WF := by
    simpa [LedgerState.WF, LedgerState.setField, hst] using hwf
  obtain ⟨req₂, h3, h4⟩ := Cell.read_spec H c p env' (σ.setField c.index (.cell v)) (fields.set c.index (.cell v))
    v vs hst' (by simp [hi]) hb hwf' (fieldsOf_ofFields_value hα hlen hr hv)
  exact ⟨req₁, req₂, _, h1, h2, h3, h4⟩

end

/-- **`Map.insert_lookup`, for every alignment Damp produces**: insert, then
    look up the same key, and the value inserted comes back, whatever its byte
    lengths, given its type's range checks. -/
theorem Map.insert_lookup_ranges {κ ν : Type} [Value κ] [Value ν] (H : Hooks) (p : Zkir.Prims) (env : Env)
    (σ : LedgerState) (fields : List SV) (m : List (AV × SV)) (k : κ) (ks : List Fr) (kv : AV)
    (mp : Map κ ν) (v : ν) (vs : List Fr) (vv : AV)
    (hpath : mp.path = [fieldKey mp.index]) (hst : σ.state = .array fields)
    (hf : fields[mp.index]? = some (.map m)) (hb : mp.index < 256) (hwf : σ.WF)
    (hk : Expr.evalList p env (Value.toExprs k) = some ks) (hkv : AV.ofFields (alignOf κ) ks = some kv)
    (hv : Expr.evalList p env (Value.toExprs v) = some vs) (hvv : AV.ofFields (alignOf ν) vs = some vv)
    (hν : ∀ t ∈ Value.tys ν, Ty.LimbsAgree t) (hlen : vs.length = Value.width ν)
    (hr : rangesHold (Value.ranges ν) vs = true) :
    ∃ req₁ req₂ σ₁, (emitted (mp.insert k v)).bind (Exec.request p env) = some req₁ ∧
      ledgerOracle H req₁ σ = some ([], σ₁) ∧
      (emitted (mp.lookup k)).bind (Exec.request p env) = some req₂ ∧
      ledgerOracle H req₂ σ₁ = some (vs, σ₁) := by
  obtain ⟨req₁, h1, h2⟩ := Map.insert_spec H p env σ fields m k ks kv mp v vs vv hpath hst hf hb hwf hk hkv hv hvv
  have hi := lt_of_getElem? hf
  let m' := assocSet kv (.cell vv) m
  have hst' : (σ.setField mp.index (.map m')).state = .array (fields.set mp.index (.map m')) := by
    simp [LedgerState.setField, hst]
  have hwf' : (σ.setField mp.index (.map m')).WF := by
    simpa [LedgerState.WF, LedgerState.setField, hst] using hwf
  obtain ⟨req₂, h3, h4⟩ := Map.lookup_spec H p env (σ.setField mp.index (.map m')) (fields.set mp.index (.map m'))
    m' k ks kv mp vv vs hpath hst' (by simp [hi]) hb hwf' hk hkv (assocGet_assocSet_self kv _ m)
    (fieldsOf_ofFields_value hν hlen hr hvv)
  exact ⟨req₁, req₂, _, h1, h2, h3, h4⟩

/-- The concrete case of the reported defect: 32 bytes with every bit set are
    the limbs `[0xff, 2^248 - 1]`; they pass `Bytes 32`'s range checks, the
    executor stores the atom `2^256 - 1`, and reads back the same two limbs. -/
theorem bytes32_ones :
    let ys : List Fr := [Fr.ofNat 255, Fr.ofNat (2 ^ 248 - 1)]
    rangesHold (Value.ranges (Bytes 32)) ys = true ∧
      AV.ofFields [.bytes 32] ys = some ⟨[.bytes 32], [2 ^ 256 - 1]⟩ ∧
      fieldsOf [.bytes 32] [2 ^ 256 - 1] = some ys := by
  have h255 : (Fr.ofNat 255).val = 255 := Fr.val_ofNat_of_lt (by decide)
  have hbig : (Fr.ofNat (2 ^ 248 - 1)).val = 2 ^ 248 - 1 := Fr.val_ofNat_of_lt (by decide)
  refine ⟨?_, ?_, ?_⟩
  · decide
  · simp [AV.ofFields, atomWidth, atomOfFields, atomFits, h255, hbig]
  · simp only [fieldsOf, fieldsOfAtom]
    simp [Fr.ofNat]
    constructor <;> rfl

end Damp.Ledger
