/-
The effects' decoding is idempotent, so every ledger state a successful query
leaves is well formed (`LedgerState.WF`).

`QueryContext::query` decodes the effects the program leaves into typed Rust
values and re-encodes them (`decodeEffects`, `Damp/Ledger/Query.lean`). The
decoded entries are fixed points of the decoding (each key and value is
re-encoded in its type's own form, which decodes to itself), duplicate keys
are gone, and the entries kept stay in order; so decoding again changes
nothing (`decodeEffects_idem`). Hence `query_wf`, `ledgerOracle_wf`: a state
the modelled ledger leaves is well formed, whatever it started from.
-/
import Damp.Proofs.Ledger.Basic

namespace Damp.Ledger

theorem effectKey_idem {slot : Nat} {k k' : AV} (h : effectKey slot k = some k') :
    effectKey slot k' = some k' := by
  unfold effectKey at h ⊢
  by_cases h1 : slot ≤ 2 ∨ slot = 4 ∨ slot = 5
  · simp only [h1, ite_true] at h ⊢
    cases hk : k.toHash with
    | none => simp [hk] at h
    | some x =>
      simp [hk] at h
      subst h
      unfold AV.toHash at hk
      split at hk
      · rename_i y _
        by_cases hy : y < 2 ^ 256
        · simp [hy] at hk; subst hk; simp [AV.ofHash, AV.toHash, hy]
        · simp [hy] at hk
      · simp at hk
  · simp only [h1, ite_false] at h ⊢
    by_cases h3 : slot = 3
    · simp only [h3, ite_true] at h ⊢
      split at h
      · cases h; simp [*]
      · simp at h
    · simp only [h3, ite_false] at h ⊢
      by_cases h67 : slot = 6 ∨ slot = 7
      · simp only [h67, ite_true] at h ⊢
        split at h
        · cases h; simp [*]
        · simp at h
      · simp only [h67, ite_false] at h ⊢
        by_cases h8 : slot = 8
        · simp only [h8, ite_true] at h ⊢
          split at h
          · cases h; simp [*]
          · simp at h
        · simp [h8] at h

theorem effectValue_idem {slot : Nat} {v v' : SV} (h : effectValue slot v = some v') :
    effectValue slot v' = some v' := by
  unfold effectValue at h ⊢
  by_cases h3 : slot ≤ 3
  · simp only [h3, ite_true] at h ⊢
    cases v with
    | null => simp at h; subst h; rfl
    | cell c =>
      simp at h
      obtain ⟨_, rfl⟩ := h
      rfl
    | _ => simp at h
  · simp only [h3, ite_false] at h ⊢
    by_cases h45 : slot = 4 ∨ slot = 5
    · simp only [h45, ite_true] at h ⊢
      cases v with
      | null => simp at h; subst h; simp [AV.toU64, AV.ofU64]
      | cell c =>
        cases hc : c.toU64 with
        | none => simp [hc] at h
        | some x =>
          simp [hc] at h; subst h
          unfold AV.toU64 at hc
          split at hc
          · rename_i y _
            by_cases hy : y < 2 ^ 64
            · simp [hy] at hc; subst hc; simp [AV.toU64, hy, AV.ofU64]
            · simp [hy] at hc
          · simp at hc
      | _ => simp at h
    · simp only [h45, ite_false] at h ⊢
      cases v with
      | null => simp at h; subst h; simp [AV.toU128]
      | cell c =>
        cases hc : c.toU128 with
        | none => simp [hc] at h
        | some x =>
          simp [hc] at h; subst h
          unfold AV.toU128 at hc
          split at hc
          · rename_i y _
            by_cases hy : y < 2 ^ 128
            · simp [hy] at hc; subst hc; simp [AV.toU128, hy]
            · simp [hy] at hc
          · simp at hc
      | _ => simp at h

theorem effectEntry_idem {slot : Nat} {k k' : AV} {v v' : SV} (h : effectEntry slot k v = some (k', v')) :
    effectEntry slot k' v' = some (k', v') := by
  unfold effectEntry at h ⊢
  cases hv : effectValue slot v with
  | none => simp [hv] at h
  | some a =>
    cases hk : effectKey slot k with
    | none => simp [hv, hk] at h
    | some b =>
      simp [hv, hk] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [effectValue_idem hv, effectKey_idem hk]

theorem effectMap_idem (slot : Nat) : ∀ {m m' : List (AV × SV)}, effectMap slot m = some m' →
    effectMap slot m' = some m'
  | [], m', h => by simp [effectMap] at h; subst h; rfl
  | (k, v) :: rest, m', h => by
      simp only [effectMap] at h
      cases hr : effectMap slot rest with
      | none => simp [hr] at h
      | some r =>
        have ihr := effectMap_idem slot hr
        cases he : effectEntry slot k v with
        | none => simp [hr, he] at h
        | some e =>
          obtain ⟨k', v'⟩ := e
          simp only [hr, he, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
          by_cases hg : (assocGet k' r).isSome
          · simp [hg] at h; subst h; exact ihr
          · simp [hg] at h; subst h
            simp only [effectMap, ihr, effectEntry_idem he, Option.bind_eq_bind, Option.bind_some, hg]
            rfl

/-- One step of the effects' decoding, on slot `i`. -/
private def slotF (p : SV × Nat) : Option SV :=
  match p.1 with
  | .map m => (effectMap p.2 m).map SV.map
  | _ => none

private theorem slotF_idem {e e' : SV} {i : Nat} (h : slotF (e, i) = some e') : slotF (e', i) = some e' := by
  cases e with
  | map m =>
    simp only [slotF, Option.map_eq_some_iff] at h
    obtain ⟨m', hm, rfl⟩ := h
    simp [slotF, effectMap_idem i hm]
  | _ => simp [slotF] at h

private theorem mapM_zipIdx_idem : ∀ (l : List SV) (n : Nat) {l' : List SV},
    (l.zipIdx n).mapM slotF = some l' → (l'.zipIdx n).mapM slotF = some l'
  | [], n, l', h => by simp at h; subst h; rfl
  | e :: es, n, l', h => by
      simp only [List.zipIdx_cons, List.mapM_cons] at h
      cases he : slotF (e, n) with
      | none => simp [he] at h
      | some e' =>
        cases hes : (es.zipIdx (n + 1)).mapM slotF with
        | none => simp [he, hes] at h
        | some es' =>
          simp [he, hes] at h; subst h
          simp [List.zipIdx_cons, List.mapM_cons, slotF_idem he, mapM_zipIdx_idem es (n + 1) hes]

private theorem mapM_length {l : List (SV × Nat)} {l' : List SV} (h : l.mapM slotF = some l') :
    l'.length = l.length := by
  induction l generalizing l' with
  | nil => simp at h; subst h; rfl
  | cons x xs ih =>
    simp only [List.mapM_cons] at h
    cases hx : slotF x with
    | none => simp [hx] at h
    | some y =>
      cases hxs : xs.mapM slotF with
      | none => simp [hx, hxs] at h
      | some ys => simp [hx, hxs] at h; subst h; simp [ih hxs]

theorem decodeEffects_eq (e : SV) : decodeEffects e =
    match e with
    | .array es => if es.length = 9 then ((es.zipIdx).mapM slotF).map SV.array else none
    | _ => none := by
  cases e <;> simp only [decodeEffects]
  split
  · rename_i es _
    change Option.bind (List.mapM slotF es.zipIdx) (fun es' => some (SV.array es')) = _
    cases (List.mapM slotF es.zipIdx) <;> rfl
  · rfl

/-- Decoding the effects is idempotent. -/
theorem decodeEffects_idem {e e' : SV} (h : decodeEffects e = some e') : decodeEffects e' = some e' := by
  rw [decodeEffects_eq] at h ⊢
  cases e with
  | array es =>
    simp only at h
    split at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨es', hm, rfl⟩ := h
      have hl : es'.length = 9 := by rw [mapM_length hm]; simp_all
      simp [hl, mapM_zipIdx_idem es 0 hm]
    · simp at h
  | _ => simp at h

/-- A successful query leaves a well-formed ledger state. -/
theorem query_wf {H : Hooks} {rops : List ROp} {q q' : LedgerState} {reads : List AV}
    (h : query H rops q = some (reads, q')) : q'.WF := by
  unfold query at h
  cases hr : runR H rops q.vm with
  | none => simp [hr] at h
  | some s =>
    simp only [hr, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · split at h
      · cases hd : decodeEffects _ with
        | none => rw [hd] at h; simp at h
        | some eff =>
          rw [hd] at h
          simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          exact decodeEffects_idem hd
      · simp at h
    · simp at h

/-- The modelled ledger leaves a well-formed state. -/
theorem ledgerOracle_wf {H : Hooks} {ops : List (Impact.Op Fr)} {q q' : LedgerState} {xs : List Fr}
    (h : ledgerOracle H ops q = some (xs, q')) : q'.WF := by
  unfold ledgerOracle at h
  cases hr : ops.mapM Op.toR with
  | none => simp [hr] at h
  | some rops =>
    cases hq : query H rops q with
    | none => simp [hr, hq] at h
    | some r =>
      obtain ⟨reads, q₁⟩ := r
      cases hb : readBack (popeqAligns ops) reads with
      | none => simp [hr, hq, hb] at h
      | some v =>
        simp [hr, hq, hb] at h
        obtain ⟨_, rfl⟩ := h
        exact query_wf hq

end Damp.Ledger
