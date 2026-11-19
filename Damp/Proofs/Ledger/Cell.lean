/-
`Cell` (`Damp/Lang/Ledger.lean`) against the VM model.

Every theorem is about the instructions the real definition emits
(`emitted (c.write x)` etc.), evaluated as the executor sends them
(`Exec.request`), run through the ledger oracle the model induces
(`ledgerOracle`). The ledger state is any well-formed one whose contract state
is an array of fields (`σ.state = .array fields`) with field `c.index`
present; a field index is a one-byte key, so `c.index < 256`.
-/
import Damp.Proofs.Ledger.Basic

namespace Damp.Ledger
open Damp.IR Damp.Impact

set_option linter.unusedSimpArgs false

/-! ## Reading back what was written -/

/-- Every atom of the alignment is one field element in a circuit: no byte
    strings longer than 31 bytes (those are split into limbs). True of `Field`,
    `Boolean`, `Uint`, enums, `Bytes n` for `n ≤ 31`, and structures of them. -/
def SingleLimb (a : List Zkir.AlignAtom) : Prop := ∀ x ∈ a, ∀ n, x = .bytes n → n ≤ 31

theorem atomWidth_singleLimb {x : Zkir.AlignAtom} (h : ∀ n, x = .bytes n → n ≤ 31) : atomWidth x = 1 := by
  cases x with
  | bytes n => have := h n rfl; simp only [atomWidth]; omega
  | field => rfl
  | compress => rfl

theorem atomOfFields_singleLimb {x : Zkir.AlignAtom} (h : ∀ n, x = .bytes n → n ≤ 31) (y : Fr) :
    atomOfFields x [y] = y.val := by
  cases x with
  | bytes n => have := h n rfl; simp [atomOfFields]; omega
  | field => rfl
  | compress => rfl

theorem fieldsOfAtom_singleLimb {x : Zkir.AlignAtom} (h : ∀ n, x = .bytes n → n ≤ 31) (y : Fr) :
    fieldsOfAtom x y.val = some [y] := by
  cases x with
  | bytes n =>
      have := h n rfl
      have hn : ¬ n > 31 := by omega
      simp [fieldsOfAtom, hn, y.isLt]
  | field => simp [fieldsOfAtom, y.isLt]
  | compress => simp [fieldsOfAtom, y.isLt]

/-- The executor's two conversions are inverse on single-limb alignments: the
    field elements a `popeq` reads back from a value written from field
    elements `vs` are `vs`. -/
theorem fieldsOf_ofFields : ∀ (a : List Zkir.AlignAtom) (vs : List Fr) (v : AV),
    AV.ofFields a vs = some v → SingleLimb a → vs.length = a.length → fieldsOf a v.atoms = some vs
  | [], vs, v, h, _, hl => by
      have : vs = [] := List.eq_nil_of_length_eq_zero hl
      subst this
      simp [AV.ofFields] at h; subst h; rfl
  | x :: as, vs, v, h, hs, hl => by
      match vs, hl with
      | y :: ys, hl =>
        have hx : ∀ n, x = .bytes n → n ≤ 31 := hs x (by simp)
        have has : SingleLimb as := fun z hz => hs z (by simp [hz])
        have hw := atomWidth_singleLimb hx
        simp only [AV.ofFields, hw, List.length_cons, List.take_succ_cons, List.take_zero,
          List.drop_succ_cons, List.drop_zero, atomOfFields_singleLimb hx] at h
        split at h
        · omega
        split at h
        · simp at h
        cases hr : AV.ofFields as ys with
        | none => simp [hr] at h
        | some r =>
          simp [hr] at h
          subst h
          simp [fieldsOf, fieldsOfAtom_singleLimb hx, fieldsOf_ofFields as ys r hr has (by simpa using hl)]

/-! ## The operations -/

section
variable {α : Type} [Value α] (H : Hooks) (c : Cell α) (p : Zkir.Prims) (env : Env)
  (σ : LedgerState) (fields : List SV)

/-- `Cell.write`: field `c.index` becomes the cell holding `x` (its field
    elements `vs` as the VM stores them, `v`); nothing else changes and nothing
    is read. It never fails on such a state. -/
theorem Cell.write_spec (x : α) (vs : List Fr) (v : AV)
    (hst : σ.state = .array fields) (hi : c.index < fields.length) (hb : c.index < 256) (hwf : σ.WF)
    (hx : Expr.evalList p env (Value.toExprs x) = some vs) (hv : AV.ofFields (alignOf α) vs = some v) :
    ∃ req, (emitted (c.write x)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some ([], σ.setField c.index (.cell v)) := by
  have he : emitted (c.write x) = some [.push false (fieldKey c.index),
      .push true ⟨alignOf α, Value.toExprs x⟩, .ins false 1] := rfl
  rw [he]
  rw [evalList_eq_mapM] at hx
  refine ⟨[.push false ⟨[.bytes 1], [Fr.ofInt c.index]⟩, .push true ⟨alignOf α, vs⟩, .ins false 1], ?_, ?_⟩
  · simp [Exec.request, Op.mapM, Aligned.mapM, hx, Exec.blank, fieldKey, Expr.eval]
  · have hk := ofAligned_byteKey hb
    simp only [AV.ofAligned] at hk
    rw [LedgerState.WF] at hwf
    simp [hb, hi, hwf, ledgerOracle, Op.toR, AV.ofAligned, hv, hk, query, LedgerState.vm, VmState.init, runR,
      ROp.exec, ROp.stackReq, hst, VmState.push, VmState.pop, insLoop, Cache.get, Cache.keyFor, insCache,
      AV.toU8, SV.asCell, maxStackHeight, readBack, popeqAligns, LedgerState.setField, CTree.get,
      Cache.contains, CKey.push]

/-- `Cell.read`: the field elements of the cell in field `c.index`, read
    under the type's alignment; the ledger is unchanged. -/
theorem Cell.read_spec (w : AV) (ys : List Fr)
    (hst : σ.state = .array fields) (hf : fields[c.index]? = some (.cell w)) (hb : c.index < 256)
    (hwf : σ.WF) (hys : fieldsOf (alignOf α) w.atoms = some ys) :
    ∃ req, (emitted c.read).bind (Exec.request p env) = some req ∧ ledgerOracle H req σ = some (ys, σ) := by
  have he : c.read = ledgerRead α (fun es =>
      [.dup 0, .idx false false [fieldKey c.index], .popeq false (alignOf α) es]) := rfl
  rw [he, emitted_ledgerRead]
  refine ⟨[.dup 0, .idx false false [⟨[.bytes 1], [Fr.ofInt c.index]⟩], .popeq false (alignOf α) []], ?_, ?_⟩
  · simp [Exec.request, Op.mapM, Aligned.mapM, Exec.blank, fieldKey, Expr.eval, mapM_eval_readVars]
  · have hk := ofAligned_byteKey hb
    simp only [AV.ofAligned] at hk
    rw [LedgerState.WF] at hwf
    have hi : c.index < fields.length := by
      rcases Nat.lt_or_ge c.index fields.length with h | h
      · exact h
      · simp [List.getElem?_eq_none h] at hf
    simp [hb, hi, hf, hwf, hys, ledgerOracle, Op.toR, AV.ofAligned, hk, query, LedgerState.vm, VmState.init,
      runR, ROp.exec, ROp.stackReq, hst, VmState.push, VmState.pop, VmState.popCell, idxWalk, idxOne,
      Cache.visit, CTree.visit, assocGet, assocSet, AV.toU8, SV.asCell, maxStackHeight, readBack,
      popeqAligns, CKey.push]
    cases σ; simp_all [readBack_cons, readBack_nil]

/-- `Cell.write` changes only field `c.index`: every other field, the call
    context and the effects are as they were. -/
theorem Cell.write_frame (x : α) (vs : List Fr) (v : AV) (j : Nat) (hj : j ≠ c.index)
    (hst : σ.state = .array fields) (hi : c.index < fields.length) (hb : c.index < 256) (hwf : σ.WF)
    (hx : Expr.evalList p env (Value.toExprs x) = some vs) (hv : AV.ofFields (alignOf α) vs = some v) :
    ∃ req σ', (emitted (c.write x)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some ([], σ') ∧
      σ'.field j = σ.field j ∧ σ'.field c.index = some (.cell v) ∧
      σ'.context = σ.context ∧ σ'.effects = σ.effects := by
  obtain ⟨req, h1, h2⟩ := Cell.write_spec H c p env σ fields x vs v hst hi hb hwf hx hv
  refine ⟨req, _, h1, h2, ?_, ?_, ?_, ?_⟩ <;>
    simp [LedgerState.setField, LedgerState.field, hst, List.getElem?_set, hj.symm, hi]

/-- Write, then read: the read returns exactly the field elements written
    (for a type whose alignment is single-limb, see `SingleLimb`), and the
    second statement leaves the ledger as the first left it. For every byte
    length, given the type's range checks, see `Cell.write_read_ranges`
    (`Limbs.lean`). -/
theorem Cell.write_read (x : α) (vs : List Fr) (v : AV)
    (hst : σ.state = .array fields) (hi : c.index < fields.length) (hb : c.index < 256) (hwf : σ.WF)
    (hx : Expr.evalList p env (Value.toExprs x) = some vs) (hv : AV.ofFields (alignOf α) vs = some v)
    (hsl : SingleLimb (alignOf α)) (hlen : vs.length = (alignOf α).length) (env' : Env) :
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
    v vs hst' (by simp [hi]) hb hwf' (fieldsOf_ofFields _ vs v hv hsl hlen)
  exact ⟨req₁, req₂, _, h1, h2, h3, h4⟩

/-- `Cell.resetToDefault` is `write` of the type's zero value, so it stores
    the cell of `Value.zero α`. -/
theorem Cell.resetToDefault_spec (vs : List Fr) (v : AV)
    (hst : σ.state = .array fields) (hi : c.index < fields.length) (hb : c.index < 256) (hwf : σ.WF)
    (hx : Expr.evalList p env (Value.toExprs (Value.zero α)) = some vs)
    (hv : AV.ofFields (alignOf α) vs = some v) :
    ∃ req, (emitted c.resetToDefault).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some ([], σ.setField c.index (.cell v)) :=
  Cell.write_spec H c p env σ fields (Value.zero α) vs v hst hi hb hwf hx hv

end

end Damp.Ledger
