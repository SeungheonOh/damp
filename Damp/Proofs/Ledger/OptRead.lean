/-
More of the VM model for the ledger-level optimizer:

* `ledgerOracle_read2`: a read through two uncached `idx` instructions
  (`dup 0; idx p₁; idx p₂; popeq`, the shape of `Map.lookup` and of a field
  inside a structure) is the plain read along `p₁ ++ p₂`
  (`ledgerOracle_read`), so it answers `readSpec 0 (p₁ ++ p₂)` and leaves the
  state as it was.
* `ledgerOracle_mapInsert_read`: after a successful map insert
  `idx [k₁] (pushing the path); push k₂; push v; ins 1; ins 1 (cached)` (the
  program of `Map.insert` on a top-level map, and of a write into a nested
  cell), a read along `[k₁, k₂]` answers what `v` holds, under the read's
  alignment.
-/
import Damp.Proofs.Ledger.OptFrame

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Damp.Ledger
open Damp.IR Damp.Impact

/-! ## Two `idx` instructions are one -/

theorem idxWalk_append (c : Bool) : ∀ (K1 K2 : List Entry) (s : VmState) (curr : Entry),
    idxWalk c false (K1 ++ K2) s curr = (idxWalk c false K1 s curr).bind fun s1 =>
      (s1.pop).bind fun r => idxWalk c false K2 r.2 r.1
  | [], K2, s, curr => by simp [idxWalk, VmState.push, VmState.pop]
  | k :: K1, K2, s, curr => by
      simp only [List.cons_append, idxWalk, Option.bind_eq_bind, Bool.false_eq_true, ite_false]
      cases k.val.asCell with
      | none => rfl
      | some kv =>
        simp only [Option.bind_some]
        cases idxOne s.cache curr kv c with
        | none => rfl
        | some r => simp only [Option.bind_some]; exact idxWalk_append c K1 K2 _ _

theorem idxWalk_push (c : Bool) : ∀ (K : List Entry) (s : VmState) (curr : Entry) (s' : VmState),
    idxWalk c false K s curr = some s' → ∃ e, s'.stack = e :: s.stack
  | [], s, curr, s', h => by simp [idxWalk, VmState.push] at h; subst h; exact ⟨curr, rfl⟩
  | k :: K, s, curr, s', h => by
      simp only [idxWalk, Option.bind_eq_bind, Bool.false_eq_true, ite_false] at h
      obtain ⟨kv, _, h⟩ := bind_some_elim h
      obtain ⟨⟨cache, e⟩, _, h⟩ := bind_some_elim h
      simpa using idxWalk_push c K _ e s' h

theorem exec_idx_eq (H : Hooks) (c : Bool) (kvs : List AV) (s : VmState) :
    ROp.exec H s (.idx c false (kvs.map Key.value)) =
      (s.pop).bind fun r => (idxWalk c false (kvs.map keyEntry) r.2 r.1).map (·, 0) := by
  simp only [ROp.exec, Option.bind_eq_bind]
  split
  · rename_i hlt
    simp only [ROp.stackReq] at hlt
    rw [filter_values _ _ (fun _ => rfl)] at hlt
    simp only [List.length_nil, Nat.zero_add, Nat.lt_one_iff, List.length_eq_zero_iff] at hlt
    simp [VmState.pop, hlt]
  · rw [filter_values _ _ (fun _ => rfl)]
    simp only [List.length_nil, List.take_zero, List.drop_zero]
    rw [foldl_values _ (fun _ _ => rfl)]
    simp only [List.nil_append]
    cases s.pop with
    | none => rfl
    | some r =>
      simp only [Option.bind_some]
      cases idxWalk c false (kvs.map keyEntry) r.2 r.1 <;> rfl

theorem exec_idx_append (H : Hooks) (c : Bool) (K1 K2 : List AV) (s : VmState) :
    ROp.exec H s (.idx c false ((K1 ++ K2).map Key.value)) =
      (ROp.exec H s (.idx c false (K1.map Key.value))).bind fun r =>
        ROp.exec H r.1 (.idx c false (K2.map Key.value)) := by
  rw [exec_idx_eq, exec_idx_eq]
  cases s.pop with
  | none => rfl
  | some r =>
    obtain ⟨curr, s1⟩ := r
    simp only [Option.bind_some, List.map_append, idxWalk_append]
    cases hw : idxWalk c false (K1.map keyEntry) s1 curr with
    | none => rfl
    | some s2 =>
      simp only [Option.bind_some, Option.map_some]
      rw [exec_idx_eq]
      cases s2.pop with
      | none => rfl
      | some r => simp

theorem exec_idx_length {H : Hooks} {c : Bool} {kvs : List AV} {s s' : VmState} {k : Nat}
    (h : ROp.exec H s (.idx c false (kvs.map Key.value)) = some (s', k)) :
    k = 0 ∧ s'.stack.length = s.stack.length := by
  rw [exec_idx_eq] at h
  obtain ⟨⟨curr, s1⟩, h1, h⟩ := bind_some_elim h
  obtain ⟨s2, h2, h⟩ := Option.map_eq_some_iff.mp h
  simp at h; obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hs1, _⟩ := pop_stack h1
  obtain ⟨e, he⟩ := idxWalk_push c _ _ _ _ h2
  simp [he, hs1]

/-- The two-`idx` read program runs as the one-`idx` one. -/
theorem runR_idx2 (H : Hooks) (K1 K2 : List AV) (rest : List ROp) (s : VmState) :
    runR H (.idx false false (K1.map Key.value) :: .idx false false (K2.map Key.value) :: rest) s =
      runR H (.idx false false ((K1 ++ K2).map Key.value) :: rest) s := by
  rw [runR_cons, runR_cons, exec_idx_append]
  cases h1 : ROp.exec H s (.idx false false (K1.map Key.value)) with
  | none => rfl
  | some r1 =>
    obtain ⟨s1, k1⟩ := r1
    obtain ⟨rfl, hl1⟩ := exec_idx_length h1
    simp only [Option.bind_some, List.length_cons, show ¬ (0 > rest.length + 1) by omega, ite_false]
    cases h2 : ROp.exec H s1 (.idx false false (K2.map Key.value)) with
    | none =>
      simp only [Option.bind_none]
      split <;> simp [runR_cons, h2]
    | some r2 =>
      obtain ⟨s2, k2⟩ := r2
      obtain ⟨rfl, hl2⟩ := exec_idx_length h2
      simp only [Option.bind_some, List.drop_zero]
      by_cases hm : s1.stack.length > maxStackHeight
      · simp only [hm, ite_true]
        simp only [hl2, hm, ite_true, show ¬ (0 > rest.length) by omega, ite_false]
      · simp only [hm, ite_false, runR_cons, h2, Option.bind_some, List.drop_zero]

/-- A read through two uncached `idx` instructions is the plain read along both paths. -/
theorem ledgerOracle_idx2 (H : Hooks) (p1 p2 : List (Aligned Fr)) (c : Bool) (a : List Zkir.AlignAtom)
    (q : LedgerState) :
    ledgerOracle H [.dup 0, .idx false false p1, .idx false false p2, .popeq c a []] q =
      ledgerOracle H (readOps 0 (p1 ++ p2) false c a) q := by
  unfold ledgerOracle readOps
  simp only [List.mapM_cons, List.mapM_nil, Op.toR, Option.bind_eq_bind, List.mapM_append]
  cases hk1 : p1.mapM AV.ofAligned with
  | none => simp
  | some K1 =>
    cases hk2 : p2.mapM AV.ofAligned with
    | none => simp
    | some K2 =>
      simp only [Option.bind_some, Option.pure_def, List.map_append]
      unfold query
      rw [runR_cons, runR_cons]
      simp only [Option.bind_eq_bind]
      cases hd : ROp.exec H q.vm (.dup 0) with
      | none => rfl
      | some r =>
        obtain ⟨s1, k⟩ := r
        obtain ⟨rfl, _⟩ := exec_dup H hd
        simp only [Option.bind_some, List.length_cons, List.drop_zero,
          show ¬ (0 > [].length + 1 + 1 + 1) by simp, show ¬ (0 > [].length + 1 + 1) by simp, ite_false]
        by_cases hm : s1.stack.length > maxStackHeight
        · simp [hm]
        · simp only [hm, ite_false]
          rw [runR_idx2, List.map_append]
          rfl

theorem ledgerOracle_read2 (H : Hooks) (p1 p2 : List (Aligned Fr)) (c : Bool) (a : List Zkir.AlignAtom)
    (q : LedgerState) (hwf : q.WF) :
    ledgerOracle H [.dup 0, .idx false false p1, .idx false false p2, .popeq c a []] q =
      (readSpec 0 (p1 ++ p2) a q).map fun ys => (ys, q) := by
  rw [ledgerOracle_idx2]
  exact ledgerOracle_read H 0 (by omega) (p1 ++ p2) false c (Or.inl rfl) a q hwf

/-! ## A map insert, then a read of the same key -/

/-- The program of `Map.insert` on a top-level map (and of a write of a cell nested one level). -/
def mapInsOps (k₁ k₂ v : Aligned Fr) : List (Op Fr) :=
  [.idx false true [k₁], .push false k₂, .push true v, .ins false 1, .ins true 1]

theorem insNext_not_cell {cv : SV} {k : AV} {x : SV} {c : AV} : insNext cv k x ≠ some (.cell c) := by
  intro h
  cases cv with
  | array es =>
    simp only [insNext] at h
    cases hk : k.toU8 with
    | none => simp [hk] at h
    | some i => by_cases hi : i < es.length <;> simp [hk, hi] at h
  | map m => simp [insNext] at h
  | bmt ht leaves =>
    simp only [insNext] at h
    cases hk : k.toU64 with
    | none => simp [hk] at h
    | some i =>
      by_cases hr : ht < 64 ∧ 2 ^ ht ≤ i
      · simp [hk, hr] at h
      · cases hx : x.asCell with
        | none => simp [hk, hr, hx] at h
        | some c' => cases hh : c'.toHash <;> simp [hk, hr, hx, hh] at h
  | null => simp [insNext] at h
  | cell _ => simp [insNext] at h

/-- After a write at `k`, the entry at `k` is what was written (a Merkle leaf: its hash as a cell). -/
theorem insNext_get {cv : SV} {k : AV} {x next : SV} (h : insNext cv k x = some next) :
    ∃ y, svStep next k = some y ∧ (y = x ∨ ∃ c hh, x = .cell c ∧ c.toHash = some hh ∧ y = .cell (AV.ofHash hh)) := by
  cases cv with
  | array es =>
    simp only [insNext] at h
    cases hi : k.toU8 with
    | none => simp [hi] at h
    | some i =>
      by_cases hl : i < es.length
      · simp [hi, hl] at h; subst h
        exact ⟨x, by simp [svStep, hi, hl], Or.inl rfl⟩
      · simp [hi, hl] at h
  | map m =>
    simp only [insNext, Option.some.injEq] at h; subst h
    exact ⟨x, by simp [svStep, assocGet_set_self'], Or.inl rfl⟩
  | bmt ht leaves =>
    simp only [insNext] at h
    cases hi : k.toU64 with
    | none => simp [hi] at h
    | some i =>
      by_cases hr : ht < 64 ∧ 2 ^ ht ≤ i
      · simp [hi, hr] at h
      · cases hc : x.asCell with
        | none => simp [hi, hr, hc] at h
        | some c =>
          cases hh : c.toHash with
          | none => simp [hi, hr, hc, hh] at h
          | some hash =>
            simp [hi, hr, hc, hh] at h; subst h
            have hx : x = .cell c := by cases x <;> simp_all [SV.asCell]
            exact ⟨_, by simp [svStep, hi, hr, assocGet_set_self'], Or.inr ⟨c, hash, hx, hh, rfl⟩⟩
  | null => simp [insNext] at h
  | cell _ => simp [insNext] at h

theorem toHash_atoms {c : AV} {h : Nat} (hh : c.toHash = some h) : c.atoms = [h] := by
  unfold AV.toHash at hh
  split at hh
  · rename_i y hy
    by_cases hy' : y < 2 ^ 256
    · simp [hy'] at hh; subst hh; exact hy
    · simp [hy'] at hh
  · simp at hh

theorem insLoop_one {c : Bool} {s : VmState} {curr : Entry} {cc : CTree} {s' : VmState} {curr' : Entry} {cc' : CTree}
    (h : insLoop c 1 s curr cc = some (s', curr', cc')) :
    ∃ key cont, s.stack = key :: cont :: s'.stack ∧ ∃ k, key.val.asCell = some k ∧
      insNext cont.val k curr.val = some curr'.val := by
  rw [insLoop_succ] at h
  obtain ⟨⟨key, s1⟩, h1, h⟩ := bind_some_elim h
  obtain ⟨⟨cont, s2⟩, h2, h⟩ := bind_some_elim h
  obtain ⟨k, hk, h⟩ := bind_some_elim h
  simp only at h h2 hk
  split at h
  · simp at h
  · obtain ⟨next, hn, h⟩ := bind_some_elim h
    simp [insLoop] at h; obtain ⟨rfl, rfl, rfl⟩ := h
    obtain ⟨hs1, _⟩ := pop_stack h1
    obtain ⟨hs2, _⟩ := pop_stack h2
    exact ⟨key, cont, by rw [hs1, hs2], k, hk, hn⟩

/-- After a successful map insert of `v` at `[k₁, k₂]`, a read of the contract
    state along `[k₁, k₂]` answers what `v` holds, under the read's alignment. -/
theorem ledgerOracle_mapInsert_read {H : Hooks} {k₁ k₂ v : Aligned Fr} {q q' : LedgerState} {xs : List Fr}
    (h : ledgerOracle H (mapInsOps k₁ k₂ v) q = some (xs, q')) (a : List Zkir.AlignAtom) :
    readSpec 0 [k₁, k₂] a q' = (AV.ofAligned v).bind fun w => fieldsOf a w.atoms := by
  unfold ledgerOracle at h
  simp only [Option.bind_eq_bind] at h
  obtain ⟨rops, hrops, h⟩ := bind_some_elim h
  obtain ⟨⟨reads, q₁⟩, hq, h⟩ := bind_some_elim h
  obtain ⟨vals, _, h⟩ := bind_some_elim h
  simp at h; obtain ⟨_, rfl⟩ := h
  -- the instructions
  cases hk1v : AV.ofAligned k₁ with
  | none => simp [mapInsOps, Op.toR, hk1v] at hrops
  | some k1v =>
  cases hk2v : AV.ofAligned k₂ with
  | none => simp [mapInsOps, Op.toR, hk1v, hk2v] at hrops
  | some k2v =>
  cases hvv : AV.ofAligned v with
  | none => simp [mapInsOps, Op.toR, hk1v, hk2v, hvv] at hrops
  | some vv =>
  simp [mapInsOps, Op.toR, hk1v, hk2v, hvv] at hrops
  subst hrops
  -- the run
  unfold query at hq
  simp only [Option.bind_eq_bind] at hq
  obtain ⟨s5, hs5, hq⟩ := bind_some_elim hq
  rw [runR_cons] at hs5
  obtain ⟨⟨s1, k⟩, he1, hs5⟩ := bind_some_elim hs5
  have e1 := exec_idx H (kvs := [k1v]) he1
  obtain ⟨rfl, curr, rest, hst, hw⟩ := e1
  simp only [show ¬ (0 > 4) by omega, ite_false, List.drop_zero, List.length_cons, List.length_nil] at hs5
  split at hs5; · simp at hs5
  rw [runR_cons] at hs5
  obtain ⟨⟨s2, k⟩, he2, hs5⟩ := bind_some_elim hs5
  obtain ⟨rfl, hs2⟩ := exec_push H he2
  simp only [show ¬ (0 > 3) by omega, ite_false, List.drop_zero, List.length_cons, List.length_nil] at hs5
  split at hs5; · simp at hs5
  rw [runR_cons] at hs5
  obtain ⟨⟨s3, k⟩, he3, hs5⟩ := bind_some_elim hs5
  obtain ⟨rfl, hs3⟩ := exec_push H he3
  simp only [show ¬ (0 > 2) by omega, ite_false, List.drop_zero, List.length_cons, List.length_nil] at hs5
  split at hs5; · simp at hs5
  rw [runR_cons] at hs5
  obtain ⟨⟨s4, k⟩, he4, hs5⟩ := bind_some_elim hs5
  obtain ⟨rfl, c4, s4a, cc4, s4b, cur4, cc4', hst4, hl4, key4, hs4⟩ := exec_ins H he4
  simp only [show ¬ (0 > 1) by omega, ite_false, List.drop_zero, List.length_cons, List.length_nil] at hs5
  split at hs5; · simp at hs5
  rw [runR_cons] at hs5
  obtain ⟨⟨s5', k⟩, he5, hs5⟩ := bind_some_elim hs5
  obtain ⟨rfl, c5, s5a, cc5, s5b, cur5, cc5', hst5, hl5, key5, hs5'⟩ := exec_ins H he5
  simp only [show ¬ (0 > 0) by omega, ite_false, List.drop_zero, List.length_nil] at hs5
  split at hs5; · simp at hs5
  simp [runR] at hs5; subst hs5
  -- the first `idx`: the field's value
  rw [vm_eq] at hst
  simp only [initStack, List.cons.injEq] at hst
  obtain ⟨rfl, rfl⟩ := hst
  simp only [List.map_cons, List.map_nil, idxWalk, Option.bind_eq_bind, ite_true, keyEntry, SV.asCell,
    Option.bind_some] at hw
  obtain ⟨⟨cache1, e1⟩, hi1, hw⟩ := bind_some_elim hw
  have hstep1 := idxOne_val hi1
  simp [idxWalk, VmState.push] at hw; subst hw
  -- the inner `ins`
  rw [hs3, hs2] at hst4
  simp only [List.cons.injEq] at hst4
  obtain ⟨rfl, hst4⟩ := hst4
  obtain ⟨key, cont, hkc, k, hk, hn1⟩ := insLoop_one hl4
  rw [← hst4] at hkc
  simp only [List.cons.injEq] at hkc
  obtain ⟨rfl, rfl, hrest4⟩ := hkc
  simp [SV.asCell] at hk; subst hk
  -- the outer `ins`
  rw [hs4] at hst5
  simp only [List.cons.injEq] at hst5
  obtain ⟨rfl, hst5⟩ := hst5
  obtain ⟨key', cont', hkc', k', hk', hn2⟩ := insLoop_one hl5
  rw [← hst5, ← hrest4] at hkc'
  simp only [List.cons.injEq] at hkc'
  obtain ⟨rfl, rfl, hrest5⟩ := hkc'
  simp [SV.asCell] at hk'; subst hk'
  -- the query's result
  rw [hs5'] at hq
  rw [← hrest5] at hq
  simp only at hq
  split at hq
  · obtain ⟨eff, _, hq⟩ := bind_some_elim hq
    simp at hq; obtain ⟨_, rfl⟩ := hq
    -- the read
    simp only [readSpec, List.mapM_cons, List.mapM_nil, hk1v, hk2v, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def, LedgerState.comp, hvv]
    obtain ⟨y1, hy1, hy1'⟩ := insNext_get hn2
    have hy1e : y1 = cur4.val := by
      rcases hy1' with h | ⟨c, _, hc, _, _⟩
      · exact h
      · exact absurd (hc ▸ hn1) insNext_not_cell
    subst hy1e
    obtain ⟨y2, hy2, hy2'⟩ := insNext_get hn1
    simp only [svWalk, hy1, hy2, Option.bind_some, Option.bind_eq_bind]
    rcases hy2' with h | ⟨c, hh, hc, hch, rfl⟩
    · rw [h]; rfl
    · simp at hc; subst hc
      simp [SV.asCell, AV.ofHash, toHash_atoms hch]
  · simp at hq

end Damp.Ledger
