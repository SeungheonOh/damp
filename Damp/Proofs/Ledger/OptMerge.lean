/-
The merge analysis of `Damp/Optimize/LedgerMerge.lean` is sound against the VM
model: `ledgerOracle_merge`. If `ops₁` passes `mcheck false mboundary` and
`ops₂` passes `mcheck true`, then on a well-formed ledger state one request
of `ops₁ ++ ops₂` is the request of `ops₁` followed by the request of `ops₂`:
the same values read (concatenated), the same final state, and both fail
together.

The proof:

* `runR_append`: the jumps of `ops₁` stay inside it, so running `ops₁ ++ ops₂`
  runs `ops₁`, then `ops₂` from where it stopped.
* `mcheck_sound`: the tags (`MTag.Ok`) hold of every stack entry at every
  step, with respect to the cache at that step. Caches only grow
  (`CacheLe`), so a tag once true stays true. With `check`, every cached
  instruction hits, so the program runs exactly as with every cached flag
  cleared (`ROp.decache`).
* `runR_er`: a program without cached instructions does the same to the
  values, strengths and reads of the stack whatever the cache and the cache
  keys are (`VmState.er` forgets them).
* After `ops₁` the stack is the contract state (strong), the original effects
  and the original call context (weak), exactly the values and strengths of
  the fresh stack the second request starts with; only the cache, the cache
  keys and the reads so far differ. So `ops₂` (with its cached flags cleared,
  which changes nothing in either run) does the same in both.
-/
import Damp.Proofs.Ledger.OptFrame
import Damp.Proofs.Ledger.Effects
import Damp.Optimize.LedgerMerge

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Damp.Ledger
open Damp.IR Damp.Impact
open Damp.Zkir (Prims)

/-! ## Jumps that stay inside a program -/

/-- How far an instruction may skip. -/
def ROp.skipMax : ROp → Nat
  | .branch n => n
  | .jmp n => n
  | _ => 0

theorem exec_skip (H : Hooks) {s s' : VmState} {op : ROp} {k : Nat} (h : op.exec H s = some (s', k)) :
    k ≤ op.skipMax := by
  cases op
  case branch n => rcases (exec_branch H h).1 with h | h <;> simp [ROp.skipMax, h]
  case jmp n => simp [ROp.skipMax, (exec_jmp H h).1]
  case root => simp [ROp.skipMax, (exec_root H h).1]
  case rem c => simp [ROp.skipMax, (exec_rem H h).1]
  all_goals
    simp only [ROp.skipMax]
    simp only [ROp.exec, Option.bind_eq_bind] at h
    split at h
    · simp at h
    · simp [Option.bind_eq_some_iff] at h; grind

/-- Every jump of the program lands inside it (or exactly at its end). -/
def jclosed : List ROp → Prop
  | [] => True
  | op :: rest => op.skipMax ≤ rest.length ∧ jclosed rest

theorem jclosed_drop : ∀ (n : Nat) {l : List ROp}, jclosed l → jclosed (l.drop n)
  | 0, _, h => h
  | _ + 1, [], _ => trivial
  | n + 1, _ :: _, h => jclosed_drop n h.2

/-- Running `l₁ ++ l₂` runs `l₁`, then `l₂`, when the jumps of `l₁` stay inside it. -/
theorem runR_append (H : Hooks) (l₂ : List ROp) :
    ∀ (n : Nat) (l₁ : List ROp), l₁.length ≤ n → jclosed l₁ → ∀ s,
      runR H (l₁ ++ l₂) s = (runR H l₁ s).bind (runR H l₂)
  | _, [], _, _, s => by simp [runR]
  | 0, _ :: _, hn, _, _ => by simp at hn
  | n + 1, op :: rest, hn, hj, s => by
      rw [List.cons_append, runR_cons, runR_cons]
      cases hex : op.exec H s with
      | none => simp
      | some x =>
        obtain ⟨s1, k⟩ := x
        have hk : k ≤ rest.length := Nat.le_trans (exec_skip H hex) hj.1
        have hk1 : ¬ k > (rest ++ l₂).length := by simp; omega
        have hk2 : ¬ k > rest.length := by omega
        simp only [Option.bind_some, hk1, hk2, ite_false]
        split
        · simp
        · rw [List.drop_append_of_le_length hk]
          exact runR_append H l₂ n (rest.drop k) (by simp at hn ⊢; omega) (jclosed_drop k hj.2) s1

/-! ## Clearing the cached flags -/

/-- The instruction with its cached flag cleared, where it matters. -/
def ROp.decache : ROp → ROp
  | .idx _ pp path => .idx false pp path
  | .ins _ n => .ins false n
  | .rem _ => .rem false
  | op => op

theorem ROp.decache_decache (r : ROp) : r.decache.decache = r.decache := by
  cases r <;> rfl

/-! ## The cache only grows -/

/-- Everything fully cached in `c`, and everything `c` contains, is in `c'` too. -/
def CacheLe (c c' : Cache) : Prop :=
  (∀ k, c.get k = .full → c'.get k = .full) ∧ (∀ k, c.contains k = true → c'.contains k = true) ∧
    c.length ≤ c'.length

theorem CacheLe.refl (c : Cache) : CacheLe c c := ⟨fun _ h => h, fun _ h => h, Nat.le_refl _⟩

theorem CacheLe.trans {a b c : Cache} (h₁ : CacheLe a b) (h₂ : CacheLe b c) : CacheLe a c :=
  ⟨fun k h => h₂.1 k (h₁.1 k h), fun k h => h₂.2.1 k (h₁.2.1 k h), Nat.le_trans h₁.2.2 h₂.2.2⟩

theorem assocGet_assocSet {κ ν : Type} [DecidableEq κ] (k j : κ) (v : ν) (m : List (κ × ν)) :
    assocGet j (assocSet k v m) = if k = j then some v else assocGet j m := by
  split
  · subst_vars; exact assocGet_set_self' _ _ _
  · rename_i h; exact assocGet_assocSet_ne' v h m

theorem CTree.visit_snd : ∀ (t : CTree) (p : List AV), (t.visit p).2 = t.contains p
  | .full, _ => by simp [CTree.visit, CTree.contains]
  | .part cs, [] => by simp [CTree.visit, CTree.contains]
  | .part cs, k :: ks => by
      simp only [CTree.visit, CTree.contains]
      cases assocGet k cs with
      | none => rfl
      | some c => exact CTree.visit_snd c ks

theorem CTree.part_contains : ∀ (ks : List AV), ((CTree.part []).visit ks).1.contains ks = true
  | [] => by simp [CTree.visit, CTree.contains]
  | k :: ks => by
      simp only [CTree.visit, assocGet, CTree.contains, assocGet_set_self']
      exact CTree.part_contains ks

theorem CTree.visit_contains_self : ∀ (t : CTree) (p : List AV), (t.visit p).1.contains p = true
  | .full, _ => by simp [CTree.visit, CTree.contains]
  | .part cs, [] => by simp [CTree.visit, CTree.contains]
  | .part cs, k :: ks => by
      simp only [CTree.visit]
      cases hk : assocGet k cs with
      | none => simp only [CTree.contains, assocGet_set_self']; exact CTree.part_contains ks
      | some c => simp only [CTree.contains, assocGet_set_self']; exact CTree.visit_contains_self c ks

theorem CTree.visit_le : ∀ (t : CTree) (p q : List AV),
    (t.get q = .full → (t.visit p).1.get q = .full) ∧ (t.contains q = true → (t.visit p).1.contains q = true)
  | .full, p, q => by simp [CTree.visit]
  | .part cs, [], q => by simp [CTree.visit]
  | .part cs, k :: ks, [] => by
      constructor
      · intro h; simp [CTree.get] at h
      · intro _; cases hk : assocGet k cs <;> simp [CTree.visit, hk, CTree.contains]
  | .part cs, k :: ks, j :: js => by
      have key : ∀ c : CTree, assocGet k cs = some c ∨ (assocGet k cs = none ∧ c = .part []) →
          ((CTree.part cs).get (j :: js) = .full → (CTree.part (assocSet k (c.visit ks).1 cs)).get (j :: js) = .full) ∧
          ((CTree.part cs).contains (j :: js) = true →
            (CTree.part (assocSet k (c.visit ks).1 cs)).contains (j :: js) = true) := by
        intro c hc
        simp only [CTree.get, CTree.contains, assocGet_assocSet]
        by_cases hkj : k = j
        · subst hkj
          rcases hc with hc | ⟨hc, rfl⟩
          · simp only [hc, ite_true]; exact CTree.visit_le c ks js
          · simp only [hc, ite_true]; constructor
            · intro h; simp at h
            · intro h; simp at h
        · simp only [hkj, ite_false]; exact ⟨id, id⟩
      simp only [CTree.visit]
      cases hk : assocGet k cs with
      | none => exact key _ (Or.inr ⟨hk, rfl⟩)
      | some c => exact key c (Or.inl hk)

theorem CTree.get_full_append : ∀ (t : CTree) (p q : List AV), t.get p = .full → t.get (p ++ q) = .full
  | .full, _, _, _ => by simp [CTree.get]
  | .part cs, [], q, h => by simp [CTree.get] at h
  | .part cs, k :: ks, q, h => by
      simp only [CTree.get, List.cons_append] at h ⊢
      cases hk : assocGet k cs with
      | none => simp [hk] at h
      | some c => simp only [hk] at h ⊢; exact CTree.get_full_append c ks q h

theorem CTree.get_full_contains : ∀ (t : CTree) (p : List AV), t.get p = .full → t.contains p = true
  | .full, _, _ => by simp [CTree.contains]
  | .part cs, [], h => by simp [CTree.contains]
  | .part cs, k :: ks, h => by
      simp only [CTree.get, CTree.contains] at h ⊢
      cases hk : assocGet k cs with
      | none => simp [hk] at h
      | some c => simp only [hk] at h ⊢; exact CTree.get_full_contains c ks h

theorem list_set_getElem? {α : Type} (l : List α) (n m : Nat) (x : α) :
    (l.set n x)[m]? = if n = m ∧ m < l.length then some x else l[m]? := by
  rw [List.getElem?_set]; split <;> split <;> simp_all <;> omega

theorem Cache.visit_le (c : Cache) (k : CKey) : CacheLe c (c.visit k).1 := by
  cases k with
  | none => exact CacheLe.refl c
  | some np =>
    obtain ⟨n, p⟩ := np
    simp only [Cache.visit]
    cases hn : c[n]? with
    | none => exact CacheLe.refl c
    | some t =>
      have hl : n < c.length := by
        rcases Nat.lt_or_ge n c.length with h | h
        · exact h
        · simp [List.getElem?_eq_none h] at hn
      refine ⟨?_, ?_, by simp⟩
      · intro k hk
        cases k with
        | none => simp [Cache.get]
        | some mq =>
          obtain ⟨m, q⟩ := mq
          simp only [Cache.get, list_set_getElem?] at hk ⊢
          by_cases hm : n = m
          · subst hm; simp only [hl, and_self, ite_true]; simp only [hn] at hk
            exact (CTree.visit_le t p q).1 hk
          · simp only [hm, false_and, ite_false]; exact hk
      · intro k hk
        cases k with
        | none => simp [Cache.contains]
        | some mq =>
          obtain ⟨m, q⟩ := mq
          simp only [Cache.contains, list_set_getElem?] at hk ⊢
          by_cases hm : n = m
          · subst hm; simp only [hl, and_self, ite_true]; simp only [hn] at hk
            exact (CTree.visit_le t p q).2 hk
          · simp only [hm, false_and, ite_false]; exact hk

theorem Cache.visit_snd (c : Cache) (k : CKey) : (c.visit k).2 = c.contains k := by
  cases k with
  | none => rfl
  | some np =>
    obtain ⟨n, p⟩ := np
    simp only [Cache.visit, Cache.contains]
    cases c[n]? with
    | none => rfl
    | some t => exact CTree.visit_snd t p

theorem Cache.visit_contains_self (c : Cache) (k : CKey) (h : (c.visit k).2 = true) :
    (c.visit k).1.contains k = true := by
  cases k with
  | none => rfl
  | some np =>
    obtain ⟨n, p⟩ := np
    simp only [Cache.visit, Cache.contains] at h ⊢
    cases hn : c[n]? with
    | none => simp [hn] at h
    | some t =>
      have hl : n < c.length := by
        rcases Nat.lt_or_ge n c.length with h | h
        · exact h
        · simp [List.getElem?_eq_none h] at hn
      simp only [list_set_getElem?, hl, and_self, ite_true]
      exact CTree.visit_contains_self t p

/-- After a visit of a key that was in the cache, or not: the key is in the cache. -/
theorem Cache.visit_contains (c : Cache) (k : CKey) : (c.visit k).1.contains k = true ∨ (c.visit k).2 = false := by
  cases k with
  | none => left; rfl
  | some np =>
    obtain ⟨n, p⟩ := np
    simp only [Cache.visit, Cache.contains]
    cases hn : c[n]? with
    | none => right; rfl
    | some t =>
      have hl : n < c.length := by
        rcases Nat.lt_or_ge n c.length with h | h
        · exact h
        · simp [List.getElem?_eq_none h] at hn
      left
      simp only [list_set_getElem?, hl, and_self, ite_true]
      exact CTree.visit_contains_self t p

theorem Cache.keyFor_le (c : Cache) (t : CTree) : CacheLe c (c.keyFor t).1 := by
  unfold Cache.keyFor
  split
  · exact CacheLe.refl c
  · refine ⟨?_, ?_, by simp⟩
    · intro k hk
      cases k with
      | none => simp [Cache.get]
      | some mq =>
        obtain ⟨m, q⟩ := mq
        simp only [Cache.get] at hk ⊢
        cases hm : c[m]? with
        | none => simp [hm] at hk
        | some u =>
          rw [List.getElem?_append_left (by
            rcases Nat.lt_or_ge m c.length with h | h
            · exact h
            · simp [List.getElem?_eq_none h] at hm)]
          simp only [hm] at hk ⊢; exact hk
    · intro k hk
      cases k with
      | none => simp [Cache.contains]
      | some mq =>
        obtain ⟨m, q⟩ := mq
        simp only [Cache.contains] at hk ⊢
        cases hm : c[m]? with
        | none => simp [hm] at hk
        | some u =>
          rw [List.getElem?_append_left (by
            rcases Nat.lt_or_ge m c.length with h | h
            · exact h
            · simp [List.getElem?_eq_none h] at hm)]
          simp only [hm] at hk ⊢; exact hk

theorem Cache.get_full_push (c : Cache) (k : CKey) (x : AV) (h : c.get k = .full) : c.get (k.push x) = .full := by
  cases k with
  | none => rfl
  | some np =>
    obtain ⟨n, p⟩ := np
    simp only [Cache.get, CKey.push, Option.map] at h ⊢
    cases hn : c[n]? with
    | none => simp [hn] at h
    | some t => simp only [hn] at h ⊢; exact CTree.get_full_append t p [x] h

theorem Cache.get_full_contains (c : Cache) (k : CKey) (h : c.get k = .full) : c.contains k = true := by
  cases k with
  | none => rfl
  | some np =>
    obtain ⟨n, p⟩ := np
    simp only [Cache.get, Cache.contains] at h ⊢
    cases hn : c[n]? with
    | none => simp [hn] at h
    | some t => simp only [hn] at h ⊢; exact CTree.get_full_contains t p h

/-- A visit of a key whose root exists leaves it in the cache. -/
theorem Cache.visit_in (c : Cache) (k : CKey) (hk : ∀ n p, k = some (n, p) → n < c.length) :
    (c.visit k).1.contains k = true := by
  rcases Cache.visit_contains c k with h | h
  · exact h
  · cases k with
    | none => rfl
    | some np =>
      obtain ⟨n, p⟩ := np
      have hl := hk n p rfl
      simp only [Cache.visit] at h ⊢
      rw [List.getElem?_eq_getElem hl] at h ⊢
      simp only [Cache.contains, list_set_getElem?, hl, and_self, ite_true]
      exact CTree.visit_contains_self _ p

/-! ## What the tags claim -/

/-- An aligned value of alignment `al` whose atoms fit it (what `AV.ofFields al` builds). -/
def AlignFits (al : List Zkir.AlignAtom) (kv : AV) : Prop :=
  kv.align = al ∧ kv.atoms.length = al.length ∧ ∀ p ∈ al.zip kv.atoms, atomFits p.1 p.2 = true

/-- What a value tag claims, `V i` being initial value `i`. -/
def _root_.Damp.IR.MVal.Ok (V : Nat → SV) : MVal → SV → Prop
  | .orig i, v => v = V i
  | .key k, v => v = .cell k
  | .cell al, v => ∃ kv, v = .cell kv ∧ AlignFits al kv
  | .nul, v => v = .null
  | .dec, v => decodeEffects v = some v
  | .dmap i, v => ∃ m, v = .map m ∧ effectMap i m = some m
  | .other, _ => True

/-! ### The effects' decoded form, through `idx` and `ins` -/

theorem ofFields_fits : ∀ {al : List Zkir.AlignAtom} {vs : List Fr} {kv : AV}, AV.ofFields al vs = some kv →
    AlignFits al kv
  | [], vs, kv, h => by simp [AV.ofFields] at h; subst h; simp [AlignFits]
  | a :: as, vs, kv, h => by
      obtain ⟨rest, hr, hfit, rfl⟩ := ofFields_cons_inv h
      obtain ⟨h1, h2, h3⟩ := ofFields_fits hr
      refine ⟨by simp [h1], by simp [h2], ?_⟩
      intro p hp
      simp only [List.zip_cons_cons, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hfit
      · exact h3 p hp

/-- Every slot of decoded effects is a decoded map. -/
theorem dec_slot {es : List SV} (h : decodeEffects (.array es) = some (.array es)) {i : Nat} {x : SV}
    (hx : es[i]? = some x) : ∃ m, x = .map m ∧ effectMap i m = some m := by
  rw [decodeEffects_array] at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨es', hm, hes⟩ := h
    cases hes
    obtain ⟨y, hy, hy'⟩ := mapM_zipIdx_get slotDecode es 0 i es x hm hx
    rw [hx] at hy'; cases hy'
    cases x with
    | map m =>
      simp only [slotDecode, Nat.zero_add, Option.map_eq_some_iff] at hy
      obtain ⟨m', hm', he⟩ := hy
      cases he
      exact ⟨m, rfl, hm'⟩
    | _ => simp [slotDecode] at hy
  · simp at h

theorem dec_array {v : SV} (h : decodeEffects v = some v) : ∃ es, v = .array es ∧ es.length = 9 := by
  cases v with
  | array es =>
    rw [decodeEffects_array] at h
    split at h
    · exact ⟨es, rfl, by assumption⟩
    · simp at h
  | _ => simp [decodeEffects] at h

section EffDec
variable {V : Nat → SV}

/-- `idx` at a slot of decoded effects finds that slot's decoded map. -/
theorem idxv_ok {ct kt : MVal} {cv res : SV} {k : AV} (hc : ct.Ok V cv) (hk : kt.Ok V (.cell k))
    (h : svStep cv k = some res) : (idxv ct kt).Ok V res := by
  unfold idxv
  split
  · rename_i kv
    simp only [MVal.Ok] at hc hk
    cases hk
    split
    · rename_i i hi
      obtain ⟨es, rfl, -⟩ := dec_array hc
      simp only [svStep, hi, Option.bind_eq_bind, Option.bind_some] at h
      exact dec_slot hc h
    · trivial
  · trivial

theorem effKey_ok {i : Nat} {kt : MVal} {k : AV} (hk : kt.Ok V (.cell k)) (h : effKeyOk i kt = true) :
    effectKey i k = some k := by
  unfold effKeyOk at h
  split at h
  · simp only [MVal.Ok] at hk; cases hk; simpa using h
  · rename_i al
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hi, rfl⟩ := h
    obtain ⟨kv, hkv, hal, hlen, hfit⟩ := hk
    cases hkv
    obtain ⟨al', atoms⟩ := k
    simp only at hal hlen; subst hal
    match atoms, hlen, hfit with
    | [x], _, hfit =>
      have hx : x < 2 ^ 256 := by simpa [atomFits] using hfit (.bytes 32, x) (by simp)
      have hi' : i ≤ 2 ∨ i = 4 ∨ i = 5 := by simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hi; omega
      simp [effectKey, hi', AV.toHash, hx, AV.ofHash]
  · simp at h

theorem effVal_ok {i : Nat} {vt : MVal} {x : SV} (hv : vt.Ok V x) (h : effValOk i vt = true) :
    effectValue i x = some x := by
  unfold effValOk at h
  split at h
  · simp only [MVal.Ok] at hv; subst hv
    simp only [decide_eq_true_eq] at h
    simp [effectValue, h]
  · rename_i kv
    simp only [MVal.Ok] at hv; subst hv
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Option.isSome_iff_exists] at h
    obtain ⟨⟨⟨hi, hal⟩, hlen⟩, y, hy⟩ := h
    have h3 : ¬ i ≤ 3 := by omega
    obtain ⟨al, atoms⟩ := kv
    simp only at hal hlen; subst hal
    match atoms, hlen, hy with
    | [z], _, hy =>
      simp only [AV.toU64] at hy
      split at hy
      · cases hy; simp [effectValue, h3, hi, AV.toU64, *, AV.ofU64]
      · simp at hy
  · rename_i al
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨hi, rfl⟩ := h
    obtain ⟨kv, rfl, hal, hlen, hfit⟩ := hv
    have h3 : ¬ i ≤ 3 := by omega
    obtain ⟨al', atoms⟩ := kv
    simp only at hal hlen; subst hal
    match atoms, hlen, hfit with
    | [z], _, hfit =>
      have hz : z < 2 ^ 64 := by simpa [atomFits] using hfit (.bytes 8, z) (by simp)
      simp [effectValue, h3, hi, AV.toU64, hz, AV.ofU64]
  · simp at h

/-- `ins` keeps the effects decoded when the key and value are in the slot's form. -/
theorem insv_ok {cnt kt ct : MVal} {cv x next : SV} {k : AV} (hcn : cnt.Ok V cv) (hk : kt.Ok V (.cell k))
    (hc : ct.Ok V x) (h : insNext cv k x = some next) : (insv cnt kt ct).Ok V next := by
  cases cnt with
  | dmap i =>
    simp only [insv]
    split
    · rename_i hok
      simp only [Bool.and_eq_true] at hok
      obtain ⟨m, rfl, hm⟩ := hcn
      simp only [insNext, Option.some.injEq] at h; subst h
      have he : effectEntry i k x = some (k, x) := by
        simp [effectEntry, effVal_ok hc hok.2, effKey_ok hk hok.1]
      exact ⟨_, rfl, effectMap_assocSet he hm⟩
    · trivial
  | dec =>
    cases kt with
    | key kv =>
      cases ct with
      | dmap i =>
        simp only [insv]
        split
        · rename_i hki
          simp only [MVal.Ok] at hk; cases hk
          simp only [beq_iff_eq] at hki
          obtain ⟨m', rfl, hm'⟩ := hc
          simp only [MVal.Ok] at hcn
          obtain ⟨es, rfl, hl⟩ := dec_array hcn
          simp only [insNext, hki, Option.bind_eq_bind, Option.bind_some] at h
          split at h
          · rename_i hil
            simp only [Option.some.injEq] at h; subst h
            simp only [MVal.Ok]
            rw [decodeEffects_array] at hcn ⊢
            simp only [hl, ite_true, Option.map_eq_some_iff] at hcn
            obtain ⟨es', hmap, hes⟩ := hcn
            cases hes
            have hs : slotDecode (.map m', 0 + i) = some (.map m') := by simp [slotDecode, hm']
            simp [List.length_set, hl, mapM_zipIdx_set slotDecode es 0 i es _ _ hmap hil hs]
          · simp at h
        · trivial
      | _ => simp [insv, MVal.Ok]
    | _ => simp [insv, MVal.Ok]
  | _ => simp [insv, MVal.Ok]

end EffDec

/-- The root of a cache key exists. -/
def KeyIn (c : Cache) (k : CKey) : Prop := ∀ n p, k = some (n, p) → n < c.length

/-- What a tag claims of a stack entry, against the cache `c`. -/
def _root_.Damp.IR.MTag.Ok (V : Nat → SV) (c : Cache) (t : MTag) (e : Entry) : Prop :=
  t.v.Ok V e.val ∧ (∀ b, t.strong = some b → e.strong = b) ∧ (t.fc = true → c.get e.key = .full) ∧
    (∀ k ∈ t.vis, c.contains (e.key.push k) = true) ∧ KeyIn c e.key

/-- Each tag holds of the entry at its position; same length. -/
def MAgrees (V : Nat → SV) (c : Cache) : List MTag → List Entry → Prop
  | [], [] => True
  | t :: ts, e :: es => t.Ok V c e ∧ MAgrees V c ts es
  | _, _ => False

section Tags
variable {V : Nat → SV}

theorem KeyIn.mono {c c' : Cache} (h : CacheLe c c') {k : CKey} (hk : KeyIn c k) : KeyIn c' k :=
  fun n p e => Nat.lt_of_lt_of_le (hk n p e) h.2.2

theorem KeyIn.push {c : Cache} {k : CKey} (hk : KeyIn c k) (x : AV) : KeyIn c (k.push x) := by
  intro n p e
  cases k with
  | none => simp [CKey.push] at e
  | some np =>
    obtain ⟨m, q⟩ := np
    simp [CKey.push] at e
    exact e.1 ▸ hk m q rfl

theorem KeyIn.none (c : Cache) : KeyIn c none := fun _ _ e => by simp at e

theorem _root_.Damp.IR.MTag.Ok.mono {c c' : Cache} (h : CacheLe c c') {t : MTag} {e : Entry} (ht : t.Ok V c e) : t.Ok V c' e :=
  ⟨ht.1, ht.2.1, fun f => h.1 _ (ht.2.2.1 f), fun k hk => h.2.1 _ (ht.2.2.2.1 k hk), ht.2.2.2.2.mono h⟩

theorem MAgrees.mono {c c' : Cache} (h : CacheLe c c') : ∀ {ts : List MTag} {es : List Entry},
    MAgrees V c ts es → MAgrees V c' ts es
  | [], [], _ => trivial
  | _ :: _, _ :: _, ha => ⟨ha.1.mono h, MAgrees.mono h ha.2⟩
  | [], _ :: _, ha => ha.elim
  | _ :: _, [], ha => ha.elim

theorem MAgrees.drop {c : Cache} : ∀ (n : Nat) {ts : List MTag} {es : List Entry}, MAgrees V c ts es →
    MAgrees V c (ts.drop n) (es.drop n)
  | 0, _, _, h => h
  | _ + 1, [], [], _ => trivial
  | n + 1, _ :: _, _ :: _, h => MAgrees.drop n h.2
  | _ + 1, [], _ :: _, h => h.elim
  | _ + 1, _ :: _, [], h => h.elim

theorem MAgrees.length {c : Cache} : ∀ {ts : List MTag} {es : List Entry}, MAgrees V c ts es → ts.length = es.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp only [List.length_cons, MAgrees.length h.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem MAgrees.get {c : Cache} : ∀ (n : Nat) {ts : List MTag} {es : List Entry} {t : MTag}, MAgrees V c ts es →
    ts[n]? = some t → ∃ e, es[n]? = some e ∧ t.Ok V c e
  | _, [], [], _, _, h => by simp at h
  | 0, t :: ts, e :: es, t', h, ht => by simp at ht; subst ht; exact ⟨e, rfl, h.1⟩
  | n + 1, t :: ts, e :: es, t', h, ht => MAgrees.get n h.2 (by simpa using ht)
  | _, [], _ :: _, _, h, _ => h.elim
  | _, _ :: _, [], _, h, _ => h.elim

theorem MAgrees.set {c : Cache} : ∀ (n : Nat) {ts : List MTag} {es : List Entry} {t : MTag} {e : Entry},
    MAgrees V c ts es → t.Ok V c e → MAgrees V c (ts.set n t) (es.set n e)
  | _, [], [], _, _, _, _ => trivial
  | 0, _ :: _, _ :: _, _, _, h, he => ⟨he, h.2⟩
  | n + 1, _ :: _, _ :: _, _, _, h, he => ⟨h.1, MAgrees.set n h.2 he⟩
  | _, [], _ :: _, _, _, h, _ => h.elim
  | _, _ :: _, [], _, _, h, _ => h.elim

theorem MAgrees.append {c : Cache} : ∀ {ts ts' : List MTag} {es es' : List Entry}, MAgrees V c ts es →
    MAgrees V c ts' es' → MAgrees V c (ts ++ ts') (es ++ es')
  | [], _, [], _, _, h => h
  | _ :: _, _, _ :: _, _, h, h' => ⟨h.1, MAgrees.append h.2 h'⟩
  | [], _, _ :: _, _, h, _ => h.elim
  | _ :: _, _, [], _, h, _ => h.elim

/-- A fresh entry: cache key `None`, fully cached. -/
theorem fresh_ok {c : Cache} {t : MTag} {v : SV} {st : Bool} (hv : t.v.Ok V v) (hs : ∀ b, t.strong = some b → st = b)
    (hvis : t.vis = []) : t.Ok V c ⟨v, st, none⟩ :=
  ⟨hv, hs, fun _ => rfl, by simp [hvis], KeyIn.none c⟩

theorem new_ok {c : Cache} (v : SV) : MTag.new.Ok V c ⟨v, true, none⟩ :=
  fresh_ok (by simp [MTag.new, MVal.Ok]) (by simp [MTag.new]) rfl

theorem mpopPush_ok {c : Cache} {n : Nat} {ts ts' : List MTag} {st st' : List Entry} (hf : mpopPush n ts = some ts')
    (ha : MAgrees V c ts st) (hs : ∃ v, st' = ⟨v, true, none⟩ :: st.drop n) : MAgrees V c ts' st' := by
  unfold mpopPush at hf
  split at hf
  · simp at hf; subst hf
    obtain ⟨v, rfl⟩ := hs
    exact ⟨new_ok v, ha.drop n⟩
  · simp at hf

theorem mkeyVal_ok {k : Aligned Expr} {p : Prims} {env : Env} {k' : Aligned Fr}
    (hk : k.mapM (Expr.eval p env) = some k') {kv : AV} (hkv : AV.ofAligned k' = some kv) :
    (mkeyVal k).Ok V (.cell kv) := by
  unfold mkeyVal
  cases hc : constAV k with
  | none =>
    have hal : k'.align = k.align := by
      simp only [Aligned.mapM, Option.bind_eq_bind] at hk
      obtain ⟨vs, -, h⟩ := bind_some_elim hk
      simp at h; subst h; rfl
    simp only [AV.ofAligned] at hkv
    exact ⟨kv, rfl, hal ▸ ofFields_fits hkv⟩
  | some kv' =>
    have := constAV_eval hc hk
    rw [hkv] at this; cases this
    rfl

theorem litTags_ok {c : Cache} {p : Prims} {env : Env} :
    ∀ {path : List (Aligned Expr)} {path' : List (Aligned Fr)} {kvs : List AV},
      path.mapM (fun k : Aligned Expr => k.mapM (Expr.eval p env)) = some path' →
      path'.mapM AV.ofAligned = some kvs → MAgrees V c (path.map litTag) (kvs.map keyEntry)
  | [], path', kvs, h1, h2 => by
      simp at h1; subst h1; simp at h2; subst h2; trivial
  | k :: ks, path', kvs, h1, h2 => by
      simp only [List.mapM_cons, Option.bind_eq_bind] at h1
      obtain ⟨k', hk', h1⟩ := bind_some_elim h1
      obtain ⟨ks', hks', h1⟩ := bind_some_elim h1
      simp at h1; subst h1
      simp only [List.mapM_cons, Option.bind_eq_bind] at h2
      obtain ⟨kv, hkv, h2⟩ := bind_some_elim h2
      obtain ⟨kvs', hkvs', h2⟩ := bind_some_elim h2
      simp at h2; subst h2
      exact ⟨fresh_ok (mkeyVal_ok hk' hkv) (by simp [litTag]) rfl, litTags_ok hks' hkvs'⟩

theorem sand_ok {x y : Option Bool} {a b : Bool} (hx : ∀ v, x = some v → a = v) (hy : ∀ v, y = some v → b = v) :
    ∀ v, sand x y = some v → (a && b) = v := by
  intro v h
  rcases x with _ | _ | _ <;> rcases y with _ | _ | _ <;> simp [sand] at h <;> subst h <;>
    simp_all

/-- A cached step at key `k` of `curr` hits when the analysis says so. -/
theorem mhit_ok {c : Cache} {ct kt : MTag} {curr key : Entry} {k : AV} (hc : ct.Ok V c curr) (hk : kt.Ok V c key)
    (hkv : key.val.asCell = some k) (h : mhit ct kt = true) : c.contains (curr.key.push k) = true := by
  unfold mhit at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · exact Cache.get_full_contains c _ (Cache.get_full_push c _ k (hc.2.2.1 h))
  · split at h
    · rename_i kv hv
      have hval := hk.1
      rw [hv] at hval
      simp only [MVal.Ok] at hval
      rw [hval] at hkv; simp [SV.asCell] at hkv; subst hkv
      exact hc.2.2.2.1 _ (by simpa using h)
    · simp at h

end Tags

/-! ## Instructions as equations -/

def ROp.newArity : ROp → Option Nat
  | .lt | .eq | .and | .or | .add | .sub | .member | .concat _ _ => some 2
  | .type | .size | .neg | .root | .addi _ | .subi _ => some 1
  | _ => none

/-- The instructions that compute a fresh value from the top `n` entries. -/
theorem exec_new (H : Hooks) {s s' : VmState} {op : ROp} {k n : Nat} (hop : op.newArity = some n)
    (h : op.exec H s = some (s', k)) :
    k = 0 ∧ s'.cache = s.cache ∧ s'.reads = s.reads ∧ ∃ v, s'.stack = ⟨v, true, none⟩ :: s.stack.drop n := by
  cases op <;> simp [ROp.newArity] at hop <;> subst hop
  case root =>
    simp only [ROp.exec, Option.bind_eq_bind] at h
    split at h; · simp at h
    obtain ⟨⟨e, s1⟩, h1, h⟩ := bind_some_elim h
    obtain ⟨hs, hc⟩ := pop_eq h1
    split at h
    · obtain ⟨r, _, h⟩ := bind_some_elim h
      simp [VmState.pushNew, VmState.push] at h; obtain ⟨rfl, rfl⟩ := h
      rw [hc] at hs ⊢; simp [hs]
    · simp at h
  all_goals
    simp [ROp.exec, VmState.pushNew, VmState.push, VmState.popU64, VmState.popCell, VmState.popBool,
      VmState.pop, Option.bind_eq_some_iff] at h <;>
    grind

/-- `add` pushes a `u64` cell. -/
theorem exec_add_val (H : Hooks) {s s' : VmState} {k : Nat} (h : ROp.add.exec H s = some (s', k)) :
    ∃ x, x < 2 ^ 64 ∧ s'.stack = ⟨.cell (AV.ofU64 x), true, none⟩ :: s.stack.drop 2 := by
  simp [ROp.exec, VmState.pushNew, VmState.push, VmState.popU64, VmState.popCell,
    VmState.pop, Option.bind_eq_some_iff] at h
  grind

/-- Only `idx` and `ins` change the cache. -/
theorem exec_cache (H : Hooks) {s s' : VmState} {op : ROp} {k : Nat}
    (hi : ∀ c pp path, op ≠ .idx c pp path) (hn : ∀ c n, op ≠ .ins c n)
    (h : op.exec H s = some (s', k)) : s'.cache = s.cache := by
  cases op
  case idx c pp path => exact absurd rfl (hi c pp path)
  case ins c n => exact absurd rfl (hn c n)
  case root =>
    simp only [ROp.exec, Option.bind_eq_bind] at h
    split at h; · simp at h
    obtain ⟨⟨e, s1⟩, h1, h⟩ := bind_some_elim h
    obtain ⟨hs, hc⟩ := pop_eq h1
    split at h
    · obtain ⟨r, _, h⟩ := bind_some_elim h
      simp [VmState.pushNew, VmState.push] at h; obtain ⟨rfl, rfl⟩ := h
      rw [hc]
    · simp at h
  case rem c =>
    simp only [ROp.exec, Option.bind_eq_bind] at h
    split at h; · simp at h
    obtain ⟨⟨kv, s1⟩, h1, h⟩ := bind_some_elim h
    obtain ⟨⟨cont, s2⟩, h2, h⟩ := bind_some_elim h
    have hc1 : s1.cache = s.cache := by
      simp only [VmState.popCell, Option.bind_eq_bind] at h1
      obtain ⟨⟨e, s0⟩, h0, h1⟩ := bind_some_elim h1
      obtain ⟨_, _, h1⟩ := bind_some_elim h1
      simp at h1; obtain ⟨_, rfl⟩ := h1
      exact (pop_stack h0).2
    have hc2 := (pop_stack h2).2
    split at h; · simp at h
    obtain ⟨cv, cs, ck⟩ := cont
    cases cv <;> simp [VmState.push] at h
    · obtain ⟨rfl, rfl⟩ := h; simp [hc2, hc1]
    · cases hi : kv.toU64 <;> simp [hi] at h
      obtain ⟨_, rfl, rfl⟩ := h; simp [hc2, hc1]
  all_goals
    simp [ROp.exec, VmState.pushNew, VmState.push, VmState.popU64, VmState.popCell, VmState.popBool,
      VmState.pop, Option.bind_eq_some_iff] at h <;>
    grind

/-- Only `popeq`, `idx` and `ins` (through their parts) touch the reads. -/
theorem exec_reads_eq (H : Hooks) {s s' : VmState} {op : ROp} {k : Nat}
    (hi : ∀ c pp path, op ≠ .idx c pp path) (hn : ∀ c n, op ≠ .ins c n) (hp : ∀ c, op ≠ .popeq c)
    (h : op.exec H s = some (s', k)) : s'.reads = s.reads := by
  cases op
  case popeq c => exact absurd rfl (hp c)
  case idx c pp path => exact absurd rfl (hi c pp path)
  case ins c n => exact absurd rfl (hn c n)
  case root =>
    simp only [ROp.exec, Option.bind_eq_bind] at h
    split at h; · simp at h
    obtain ⟨⟨e, s1⟩, h1, h⟩ := bind_some_elim h
    obtain ⟨hs, hc⟩ := pop_eq h1
    split at h
    · obtain ⟨r, _, h⟩ := bind_some_elim h
      simp [VmState.pushNew, VmState.push] at h; obtain ⟨rfl, rfl⟩ := h
      rw [hc]
    · simp at h
  case rem c =>
    simp only [ROp.exec, Option.bind_eq_bind] at h
    split at h; · simp at h
    obtain ⟨⟨kv, s1⟩, h1, h⟩ := bind_some_elim h
    obtain ⟨⟨cont, s2⟩, h2, h⟩ := bind_some_elim h
    have hc1 : s1.reads = s.reads := by
      simp only [VmState.popCell, Option.bind_eq_bind] at h1
      obtain ⟨⟨e, s0⟩, h0, h1⟩ := bind_some_elim h1
      obtain ⟨_, _, h1⟩ := bind_some_elim h1
      simp at h1; obtain ⟨_, rfl⟩ := h1
      rw [(pop_eq h0).2]
    have hc2 : s2.reads = s1.reads := by rw [(pop_eq h2).2]
    split at h; · simp at h
    obtain ⟨cv, cs, ck⟩ := cont
    cases cv <;> simp [VmState.push] at h
    · obtain ⟨rfl, rfl⟩ := h; simp [hc2, hc1]
    · cases hi : kv.toU64 <;> simp [hi] at h
      obtain ⟨_, rfl, rfl⟩ := h; simp [hc2, hc1]
  all_goals
    simp [ROp.exec, VmState.pushNew, VmState.push, VmState.popU64, VmState.popCell, VmState.popBool,
      VmState.pop, Option.bind_eq_some_iff] at h <;>
    grind

theorem exec_idx_gen (H : Hooks) (c pp : Bool) (kvs : List AV) (s : VmState) :
    ROp.exec H s (.idx c pp (kvs.map Key.value)) =
      (s.pop).bind fun r => (idxWalk c pp (kvs.map keyEntry) r.2 r.1).map (·, 0) := by
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
      cases idxWalk c pp (kvs.map keyEntry) r.2 r.1 <;> rfl

theorem exec_idxs_gen (H : Hooks) (c : Bool) (kvs : List AV) (s : VmState) :
    ROp.exec H s (.idx c false (kvs.map Key.value ++ [.stack])) =
      match s.stack with
      | sk :: curr :: rest => (idxWalk c false (kvs.map keyEntry ++ [sk]) { s with stack := rest } curr).map (·, 0)
      | _ => none := by
  simp only [ROp.exec, Option.bind_eq_bind]
  rw [List.filter_append, filter_values _ _ (fun _ => rfl)]
  simp only [List.foldl_append]
  rw [foldl_values _ (fun _ _ => rfl)]
  obtain ⟨st, c0, r0⟩ := s
  rcases st with _ | ⟨sk, _ | ⟨curr, rest⟩⟩
  · simp [ROp.stackReq, filter_values]
  · simp [ROp.stackReq, filter_values]
  · simp only [List.nil_append, List.filter_cons, List.filter_nil, ROp.stackReq, List.filter_append]
    rw [filter_values _ _ (fun _ => rfl)]
    simp [VmState.pop]
    cases idxWalk c false (kvs.map keyEntry ++ [sk]) ⟨rest, c0, r0⟩ curr <;> rfl

theorem exec_ins_gen (H : Hooks) (c : Bool) (n : Nat) (s : VmState) :
    ROp.exec H s (.ins c n) =
      if s.stack.length < 2 * n + 1 then none
      else (s.pop).bind fun r => (insLoop c n r.2 r.1 (r.2.cache.get r.1.key)).map fun x =>
        ({ x.1 with cache := (x.1.cache.keyFor x.2.2).1, stack := { x.2.1 with key := (x.1.cache.keyFor x.2.2).2 } :: x.1.stack }, 0) := by
  simp only [ROp.exec, ROp.stackReq, Option.bind_eq_bind]
  by_cases hl : s.stack.length < 2 * n + 1
  · simp [hl]
  · simp only [hl, ite_false]
    cases s.pop with
    | none => rfl
    | some r =>
      simp only [Option.bind_some]
      cases insLoop c n r.2 r.1 (r.2.cache.get r.1.key) <;> rfl

theorem exec_rem_gen (H : Hooks) (c : Bool) (s : VmState) :
    ROp.exec H s (.rem c) =
      (s.popCell).bind fun r => (r.2.pop).bind fun r' =>
        if (c && !r'.2.cache.contains (r'.1.key.push r.1)) = true then none
        else (remNext r'.1.val r.1).map fun next => (r'.2.push { r'.1 with val := next }, 0) := by
  obtain ⟨st, c0, r0⟩ := s
  rcases st with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp [ROp.exec, ROp.stackReq, VmState.popCell, VmState.pop]
  · simp [ROp.exec, ROp.stackReq, VmState.popCell, VmState.pop]
    cases a.val.asCell <;> simp
  · simp only [ROp.exec, ROp.stackReq, Option.bind_eq_bind]
    simp only [List.length_cons, show ¬ rest.length + 1 + 1 < 2 by omega, ite_false]
    simp only [VmState.popCell, VmState.pop, Option.bind_eq_bind, Option.bind_some]
    cases a.val.asCell with
    | none => rfl
    | some kv =>
      simp only [Option.bind_some, Option.pure_def]
      split
      · rfl
      · obtain ⟨bv, bs, bk⟩ := b
        cases bv <;> simp [remNext]
        cases kv.toU64 <;> simp
        split <;> rfl

theorem idxOne_hit (cache : Cache) (curr : Entry) (k : AV) (h : (cache.visit (curr.key.push k)).2 = true) :
    idxOne cache curr k true = idxOne cache curr k false := by
  unfold idxOne
  simp only [Option.bind_eq_bind, h, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false]

theorem idxOne_some {cache : Cache} {curr : Entry} {k : AV} {c : Bool} {r : Cache × Entry}
    (h : idxOne cache curr k c = some r) : idxOne cache curr k false = some r := by
  cases c with
  | false => exact h
  | true =>
    unfold idxOne at h ⊢
    simp only [Option.bind_eq_bind] at h ⊢
    split at h
    · simp at h
    · simpa using h

/-! ## The walk of `idx` and the loop of `ins` keep the tags -/

section Walk
variable (V : Nat → SV)

theorem idxWalk_cons (c pp : Bool) (key : Entry) (keys : List Entry) (s : VmState) (curr : Entry) (k : AV)
    (hkv : key.val.asCell = some k) :
    idxWalk c pp (key :: keys) s curr =
      (idxOne s.cache curr k c).bind fun r =>
        idxWalk c pp keys { (if pp then (s.push curr).push { key with key := none } else s) with cache := r.1 } r.2 := by
  cases pp <;> simp [idxWalk, hkv, VmState.push] <;> rfl

theorem midx_ok {check cached pp : Bool} :
    ∀ (keys : List Entry) (kts : List MTag) (s : VmState) (curr : Entry) (ct : MTag) (ts out : List MTag),
    midx check cached pp kts ct ts = some out → MAgrees V s.cache kts keys → ct.Ok V s.cache curr →
    MAgrees V s.cache ts s.stack →
    (check = true → idxWalk cached pp keys s curr = idxWalk false pp keys s curr) ∧
    (∀ s', idxWalk cached pp keys s curr = some s' → MAgrees V s'.cache out s'.stack)
  | [], [], s, curr, ct, ts, out, hm, _, hc, hts => by
      simp [midx] at hm; subst hm
      refine ⟨fun _ => rfl, fun s' h => ?_⟩
      simp [idxWalk, VmState.push] at h; subst h; exact ⟨hc, hts⟩
  | key :: keys, kt :: kts, s, curr, ct, ts, out, hm, hk, hc, hts => by
      simp only [midx] at hm
      split at hm
      · simp at hm
      · rename_i hnh
        cases hkv : key.val.asCell with
        | none =>
          refine ⟨fun _ => by simp [idxWalk, hkv], fun s' h => by simp [idxWalk, hkv] at h⟩
        | some k =>
          have hone_eq : check = true → idxOne s.cache curr k cached = idxOne s.cache curr k false := by
            intro hch
            cases cached with
            | false => rfl
            | true =>
              apply idxOne_hit
              rw [Cache.visit_snd]
              have : mhit ct kt = true := by simp_all
              exact mhit_ok hc hk.1 hkv this
          rw [idxWalk_cons _ _ _ _ _ _ _ hkv, idxWalk_cons _ _ _ _ _ _ _ hkv]
          rw [idxOne_uncached] at hone_eq ⊢
          cases hsv : svStep curr.val k with
          | none =>
            refine ⟨fun hch => by rw [hone_eq hch, hsv]; rfl, fun s' h => ?_⟩
            obtain ⟨r, hr, _⟩ := bind_some_elim h
            have := idxOne_some hr
            rw [idxOne_uncached, hsv] at this; simp at this
          | some res =>
            have hle := Cache.visit_le s.cache (curr.key.push k)
            have hin : KeyIn s.cache (curr.key.push k) := hc.2.2.2.2.push k
            have hts2 : MAgrees V (s.cache.visit (curr.key.push k)).1
                (if pp then { kt with fc := true, vis := [] } :: { ct with vis := addVis kt.v ct.vis } :: ts else ts)
                ({ (if pp then (s.push curr).push { key with key := none } else s) with
                    cache := (s.cache.visit (curr.key.push k)).1 }).stack := by
              cases pp
              · exact hts.mono hle
              · refine ⟨⟨hk.1.1, hk.1.2.1, fun _ => rfl, by simp, KeyIn.none _⟩, ⟨hc.1, hc.2.1,
                  fun f => hle.1 _ (hc.2.2.1 f), ?_, hc.2.2.2.2.mono hle⟩, hts.mono hle⟩
                intro kv hkv'
                unfold addVis at hkv'
                split at hkv'
                · rename_i kv0 hv0
                  rcases List.mem_cons.mp hkv' with rfl | hmem
                  · have hval := hk.1.1
                    rw [hv0] at hval; simp only [MVal.Ok] at hval
                    rw [hval] at hkv; simp [SV.asCell] at hkv; subst hkv
                    exact Cache.visit_in _ _ hin
                  · exact hle.2.1 _ (hc.2.2.2.1 kv hmem)
                · exact hle.2.1 _ (hc.2.2.2.1 kv hkv')
            have hkey : key.val = .cell k := by
              cases hkk : key.val <;> simp [hkk, SV.asCell] at hkv; rw [hkv]
            have hc2 : (⟨idxv ct.v kt.v, ct.strong, ct.fc, []⟩ : MTag).Ok V (s.cache.visit (curr.key.push k)).1
                { val := res, strong := curr.strong, key := curr.key.push k } :=
              ⟨idxv_ok hc.1 (hkey ▸ hk.1.1) hsv, hc.2.1, fun f => Cache.get_full_push _ _ k (hle.1 _ (hc.2.2.1 f)), by simp, hin.mono hle⟩
            have ih := midx_ok keys kts
              { (if pp then (s.push curr).push { key with key := none } else s) with
                    cache := (s.cache.visit (curr.key.push k)).1 }
              { val := res, strong := curr.strong, key := curr.key.push k } _ _ out hm (hk.2.mono hle) hc2 hts2
            refine ⟨fun hch => ?_, fun s' h => ?_⟩
            · rw [hone_eq hch, hsv]; simp only [Option.map_some, Option.bind_some]; exact ih.1 hch
            · obtain ⟨r, hr, h⟩ := bind_some_elim h
              have := idxOne_some hr
              rw [idxOne_uncached, hsv] at this; simp at this; subst this
              exact ih.2 s' h
  | [], _ :: _, _, _, _, _, _, _, hk, _, _ => hk.elim
  | _ :: _, [], _, _, _, _, _, _, hk, _, _ => hk.elim

/-- What the loop of `ins` knows of the entry it builds: its value and
    strength, and that the cache tree it carries is full. -/
def LoopOk (t : MTag) (curr : Entry) (cc : CTree) : Prop :=
  t.v.Ok V curr.val ∧ (∀ b, t.strong = some b → curr.strong = b) ∧ (t.fc = true → cc = .full)

theorem mins_ok {check cached : Bool} :
    ∀ (n : Nat) (s : VmState) (curr : Entry) (cc : CTree) (ct : MTag) (ts : List MTag) (ct' : MTag) (ts' : List MTag),
    mins check cached n ct ts = some (ct', ts') → MAgrees V s.cache ts s.stack → LoopOk V ct curr cc →
    (check = true → insLoop cached n s curr cc = insLoop false n s curr cc) ∧
    (∀ s' curr' cc', insLoop cached n s curr cc = some (s', curr', cc') →
       s'.cache = s.cache ∧ MAgrees V s.cache ts' s'.stack ∧ LoopOk V ct' curr' cc')
  | 0, s, curr, cc, ct, ts, ct', ts', hm, hts, hc => by
      simp [mins] at hm; obtain ⟨rfl, rfl⟩ := hm
      refine ⟨fun _ => rfl, fun s' curr' cc' h => ?_⟩
      simp [insLoop] at h; obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, hts, hc⟩
  | n + 1, s, curr, cc, ct, ts, ct', ts', hm, hts, hc => by
      match ts, hts, hm with
      | kt :: cnt :: ts₀, hts, hm =>
        simp only [mins] at hm
        split at hm
        · simp at hm
        · rename_i hnh
          match hst : s.stack, hts with
          | key :: cont :: rest, hts =>
            have hp1 : s.pop = some (key, { s with stack := cont :: rest }) := by simp [VmState.pop, hst]
            have hp2 : ({ s with stack := cont :: rest } : VmState).pop = some (cont, { s with stack := rest }) := by
              simp [VmState.pop]
            rw [insLoop_succ, insLoop_succ, hp1]
            simp only [Option.bind_some, hp2]
            cases hkv : key.val.asCell with
            | none => exact ⟨fun _ => rfl, fun s' curr' cc' h => by simp at h⟩
            | some k =>
              simp only [Option.bind_some]
              have hnb : insBlocked false { s with stack := rest } cont k = false := by simp [insBlocked]
              have hb_eq : check = true → insBlocked cached { s with stack := rest } cont k = false := by
                intro hch
                cases cached with
                | false => rfl
                | true =>
                  have : mhit cnt kt = true := by simp_all
                  simp [insBlocked, mhit_ok hts.2.1 hts.1 hkv this]
              cases hn : insNext cont.val k curr.val with
              | none =>
                refine ⟨fun hch => by simp [hb_eq hch, hnb, hn], fun s' curr' cc' h => ?_⟩
                split at h <;> simp [hn] at h
              | some next =>
                have hkey : key.val = .cell k := by
                  cases hkk : key.val <;> simp [hkk, SV.asCell] at hkv; rw [hkv]
                have hc2 : LoopOk V ⟨insv cnt.v kt.v ct.v, sand ct.strong cnt.strong, ct.fc && cnt.fc, []⟩
                    { val := next, strong := curr.strong && cont.strong, key := curr.key }
                    (insCache (({ s with stack := rest } : VmState).cache.get cont.key) k cc) := by
                  refine ⟨insv_ok hts.2.1.1 (hkey ▸ hts.1.1) hc.1 hn, sand_ok hc.2.1 hts.2.1.2.1, fun f => ?_⟩
                  simp only [Bool.and_eq_true] at f
                  have h1 := hc.2.2 f.1
                  have h2 := hts.2.1.2.2.1 f.2
                  simp only at h2 ⊢
                  rw [h1, h2]; rfl
                have ih := mins_ok n { s with stack := rest } _ _ _ ts₀ ct' ts' hm hts.2.2 hc2
                refine ⟨fun hch => ?_, fun s' curr' cc' h => ?_⟩
                · simp only [hb_eq hch, hnb, Bool.false_eq_true, ite_false, hn, Option.bind_some]
                  exact ih.1 hch
                · split at h
                  · simp at h
                  · simp only [hn, Option.bind_some] at h
                    obtain ⟨h1, h2, h3⟩ := ih.2 s' curr' cc' h
                    exact ⟨h1, h2, h3⟩
          | [], hts => exact hts.elim
          | [_], hts => exact hts.2.elim
      | [], _, hm => simp [mins] at hm
      | [_], _, hm => simp [mins] at hm

end Walk

/-! ## One instruction keeps the tags, and its cached flag does not matter -/

section Step
variable (V : Nat → SV)

theorem exec_pop1 (H : Hooks) {s s' : VmState} {r : ROp} {k : Nat} (hr : r = .popeq false ∨ r = .popeq true ∨ r = .pop ∨ r = .log)
    (h : r.exec H s = some (s', k)) : k = 0 ∧ s'.cache = s.cache ∧ s'.stack = s.stack.drop 1 := by
  have hc := exec_cache H (op := r) (by rcases hr with rfl | rfl | rfl | rfl <;> simp) (by rcases hr with rfl | rfl | rfl | rfl <;> simp) h
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨(exec_popeq H h).1, hc, (exec_popeq H h).2⟩
  · exact ⟨(exec_popeq H h).1, hc, (exec_popeq H h).2⟩
  · exact ⟨(exec_pop H h).1, hc, (exec_pop H h).2⟩
  · exact ⟨(exec_log H h).1, hc, (exec_log H h).2⟩

theorem mstep_ok (H : Hooks) {p : Prims} {env : Env} {op : Op Expr} {r : ROp} (hr : OpEvals p env op r)
    {check : Bool} {ts ts' : List MTag} (hf : mstep check op ts = some ts') {s : VmState}
    (ha : MAgrees V s.cache ts s.stack) :
    (check = true → r.exec H s = r.decache.exec H s) ∧
    (∀ s' k, r.exec H s = some (s', k) → k = 0 ∧ MAgrees V s'.cache ts' s'.stack) := by
  obtain ⟨op', hop, hr⟩ := hr
  cases op with
  | add =>
    simp [Op.mapM] at hop; subst hop; simp [Exec.blank, Op.toR] at hr; subst hr
    refine ⟨fun _ => rfl, fun s' k hex => ?_⟩
    obtain ⟨hk, hc, _, _⟩ := exec_new H (by rfl) hex
    obtain ⟨x, hx, hs⟩ := exec_add_val H hex
    refine ⟨hk, ?_⟩
    simp only [mstep] at hf
    split at hf
    · simp at hf; subst hf
      rw [hc, hs]
      refine ⟨fresh_ok ⟨_, rfl, by simp [AlignFits, AV.ofU64, atomFits, hx]⟩ (by simp) rfl, ha.drop 2⟩
    · simp at hf
  | lt | eq | and | or | sub | member | type | size | neg | root | concat _ | concatCached _ =>
    simp [Op.mapM] at hop; subst hop; simp [Exec.blank, Op.toR] at hr; subst hr
    refine ⟨fun _ => rfl, fun s' k hex => ?_⟩
    obtain ⟨hk, hc, _, hs⟩ := exec_new H (by rfl) hex
    exact ⟨hk, by rw [hc]; exact mpopPush_ok hf ha hs⟩
  | addi i | subi i =>
    cases hx : Expr.eval p env i with
    | none => simp [Op.mapM, hx] at hop
    | some i' =>
    simp [Op.mapM, hx] at hop; subst hop
    cases hm : immOf i' with
    | none => simp [Exec.blank, Op.toR, hm] at hr
    | some imm =>
    simp [Exec.blank, Op.toR, hm] at hr; subst hr
    refine ⟨fun _ => rfl, fun s' k hex => ?_⟩
    obtain ⟨hk, hc, _, hs⟩ := exec_new H (by rfl) hex
    exact ⟨hk, by rw [hc]; exact mpopPush_ok hf ha hs⟩
  | popeq c a res =>
    cases hx : res.mapM (Expr.eval p env) with
    | none => simp [Op.mapM, hx] at hop
    | some res' =>
    simp [Op.mapM, hx] at hop; subst hop
    simp [Exec.blank, Op.toR] at hr; subst hr
    refine ⟨fun _ => rfl, fun s' k hex => ?_⟩
    obtain ⟨hk, hc, hs⟩ := exec_pop1 H (by cases c <;> simp) hex
    match ts, ha, hf with
    | _ :: ts₀, ha, hf =>
      simp [mstep] at hf; subst hf
      exact ⟨hk, by rw [hs, hc]; exact ha.drop 1⟩
  | pop | log =>
    simp [Op.mapM] at hop; subst hop; simp [Exec.blank, Op.toR] at hr; subst hr
    refine ⟨fun _ => rfl, fun s' k hex => ?_⟩
    obtain ⟨hk, hc, hs⟩ := exec_pop1 H (by simp) hex
    match ts, ha, hf with
    | _ :: ts₀, ha, hf =>
      simp [mstep] at hf; subst hf
      exact ⟨hk, by rw [hs, hc]; exact ha.drop 1⟩
  | ckpt =>
    simp [Op.mapM] at hop; subst hop; simp [Exec.blank, Op.toR] at hr; subst hr
    refine ⟨fun _ => rfl, fun s' k hex => ?_⟩
    obtain ⟨hk, rfl⟩ := exec_ckpt H hex
    simp [mstep] at hf; subst hf; exact ⟨hk, ha⟩
  | push st v =>
    cases hv' : v.mapM (Expr.eval p env) with
    | none => simp [Op.mapM, hv'] at hop
    | some v' =>
    simp [Op.mapM, hv'] at hop; subst hop
    cases hvv : AV.ofAligned v' with
    | none => simp [Exec.blank, Op.toR, hvv] at hr
    | some vv =>
    simp [Exec.blank, Op.toR, hvv] at hr; subst hr
    refine ⟨fun _ => rfl, fun s' k hex => ?_⟩
    have hc := exec_cache H (by simp) (by simp) hex
    obtain ⟨hk, hs⟩ := exec_push H hex
    simp [mstep] at hf; subst hf
    exact ⟨hk, by rw [hs, hc]; exact ⟨fresh_ok (mkeyVal_ok hv' hvv) (by simp) rfl, ha⟩⟩
  | pushNull st =>
    simp [Op.mapM] at hop; subst hop; simp [Exec.blank, Op.toR] at hr; subst hr
    refine ⟨fun _ => rfl, fun s' k hex => ?_⟩
    have hc := exec_cache H (by simp) (by simp) hex
    obtain ⟨hk, hs⟩ := exec_push H hex
    simp [mstep] at hf; subst hf
    exact ⟨hk, by rw [hs, hc]; exact ⟨fresh_ok rfl (by simp) rfl, ha⟩⟩
  | pushState st v =>
    cases hv' : v.mapM (Expr.eval p env) with
    | none => simp [Op.mapM, hv'] at hop
    | some v' =>
    simp [Op.mapM, hv'] at hop; subst hop
    cases hsv : SV.ofLit v' with
    | none => simp [Exec.blank, Op.toR, hsv] at hr
    | some sv =>
    simp [Exec.blank, Op.toR, hsv] at hr; subst hr
    refine ⟨fun _ => rfl, fun s' k hex => ?_⟩
    have hc := exec_cache H (by simp) (by simp) hex
    obtain ⟨hk, hs⟩ := exec_push H hex
    simp [mstep] at hf; subst hf
    exact ⟨hk, by rw [hs, hc]; exact ⟨fresh_ok trivial (by simp) rfl, ha⟩⟩
  | dup n =>
    simp [Op.mapM] at hop; subst hop; simp [Exec.blank, Op.toR] at hr; subst hr
    refine ⟨fun _ => rfl, fun s' k hex => ?_⟩
    have hc := exec_cache H (by simp) (by simp) hex
    obtain ⟨hk, e, he, hs⟩ := exec_dup H hex
    simp only [mstep] at hf
    cases ht : ts[n]? with
    | none => simp [ht] at hf
    | some t =>
      simp [ht] at hf; subst hf
      obtain ⟨e', he', hok⟩ := ha.get n ht
      rw [he] at he'; cases he'
      exact ⟨hk, by rw [hs, hc]; exact ⟨hok, ha⟩⟩
  | swap n =>
    simp [Op.mapM] at hop; subst hop; simp [Exec.blank, Op.toR] at hr; subst hr
    refine ⟨fun _ => rfl, fun s' k hex => ?_⟩
    have hc := exec_cache H (by simp) (by simp) hex
    obtain ⟨hk, top, oth, htop, hoth, hs⟩ := exec_swap H hex
    simp only [mstep, Option.bind_eq_bind] at hf
    obtain ⟨tt, htt, hf⟩ := bind_some_elim hf
    obtain ⟨to, hto, hf⟩ := bind_some_elim hf
    simp at hf; subst hf
    obtain ⟨e1, he1, hok1⟩ := ha.get 0 htt
    obtain ⟨e2, he2, hok2⟩ := ha.get (n + 1) hto
    rw [htop] at he1; cases he1
    rw [hoth] at he2; cases he2
    exact ⟨hk, by rw [hs, hc]; exact (ha.set 0 hok2).set (n + 1) hok1⟩
  | idx c pp path =>
    cases hp' : path.mapM (fun k : Aligned Expr => k.mapM (Expr.eval p env)) with
    | none => simp [Op.mapM, hp'] at hop
    | some path' =>
    simp [Op.mapM, hp'] at hop; subst hop
    cases hkvs : path'.mapM AV.ofAligned with
    | none => simp [Exec.blank, Op.toR, hkvs] at hr
    | some kvs =>
    simp [Exec.blank, Op.toR, hkvs] at hr; subst hr
    match hst : s.stack, ts, ha, hf with
    | curr :: rest, ct :: ts₀, ha, hf =>
      simp only [mstep] at hf
      have hp : s.pop = some (curr, { s with stack := rest }) := by simp [VmState.pop, hst]
      have hw := midx_ok V (kvs.map keyEntry) (path.map litTag) { s with stack := rest } curr ct ts₀ ts' hf
        (litTags_ok hp' hkvs) ha.1 ha.2
      refine ⟨fun hch => ?_, fun s' k hex => ?_⟩
      · simp only [ROp.decache]
        rw [exec_idx_gen, exec_idx_gen, hp]
        simp only [Option.bind_some]
        rw [hw.1 hch]
      · rw [exec_idx_gen, hp] at hex
        simp only [Option.bind_some] at hex
        obtain ⟨s2, h2, h⟩ := Option.map_eq_some_iff.mp hex
        simp at h; obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, hw.2 s2 h2⟩
    | [], [], ha, hf => simp [mstep] at hf
    | [], _ :: _, ha, hf => exact ha.elim
    | _ :: _, [], ha, hf => exact ha.elim
  | idxStack pre =>
    cases hp' : pre.mapM (fun k : Aligned Expr => k.mapM (Expr.eval p env)) with
    | none => simp [Op.mapM, hp'] at hop
    | some pre' =>
    simp [Op.mapM, hp'] at hop; subst hop
    cases hkvs : pre'.mapM AV.ofAligned with
    | none => simp [Exec.blank, Op.toR, hkvs] at hr
    | some kvs =>
    simp [Exec.blank, Op.toR, hkvs] at hr; subst hr
    match hst : s.stack, ts, ha, hf with
    | sk :: curr :: rest, skt :: ct :: ts₀, ha, hf =>
      simp only [mstep] at hf
      have hw := midx_ok V (kvs.map keyEntry ++ [sk]) (pre.map litTag ++ [skt]) { s with stack := rest } curr ct ts₀ ts' hf
        (MAgrees.append (litTags_ok hp' hkvs) (show MAgrees V s.cache [skt] [sk] from ⟨ha.1, trivial⟩)) ha.2.1 ha.2.2
      refine ⟨fun hch => ?_, fun s' k hex => ?_⟩
      · simp only [ROp.decache]
        rw [exec_idxs_gen, exec_idxs_gen, hst]
        simp only
        rw [hw.1 hch]
      · rw [exec_idxs_gen, hst] at hex
        simp only at hex
        obtain ⟨s2, h2, h⟩ := Option.map_eq_some_iff.mp hex
        simp at h; obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, hw.2 s2 h2⟩
    | [], [], ha, hf => simp [mstep] at hf
    | [], _ :: _, ha, hf => exact ha.elim
    | [_], [], ha, hf => exact ha.elim
    | [_], [_], ha, hf => simp [mstep] at hf
    | [_], _ :: _ :: _, ha, hf => exact ha.2.elim
    | _ :: _ :: _, [], ha, hf => exact ha.elim
    | _ :: _ :: _, [_], ha, hf => exact ha.2.elim
  | ins c n =>
    simp [Op.mapM] at hop; subst hop; simp [Exec.blank, Op.toR] at hr; subst hr
    match hst : s.stack, ts, ha, hf with
    | curr :: rest, ct :: ts₀, ha, hf =>
      simp only [mstep] at hf
      cases hmi : mins check c n ct ts₀ with
      | none => simp [hmi] at hf
      | some res =>
      obtain ⟨ct', ts₁⟩ := res
      simp [hmi] at hf; subst hf
      have hp : s.pop = some (curr, { s with stack := rest }) := by simp [VmState.pop, hst]
      have hl := mins_ok V n { s with stack := rest } curr (s.cache.get curr.key) ct ts₀ ct' ts₁ hmi ha.2
        ⟨ha.1.1, ha.1.2.1, fun f => ha.1.2.2.1 f⟩
      refine ⟨fun hch => ?_, fun s' k hex => ?_⟩
      · simp only [ROp.decache]
        rw [exec_ins_gen, exec_ins_gen, hp]
        simp only [Option.bind_some]
        rw [hl.1 hch]
      · rw [exec_ins_gen, hp] at hex
        split at hex
        · simp at hex
        · simp only [Option.bind_some] at hex
          obtain ⟨⟨s2, curr', cc'⟩, h2, h⟩ := Option.map_eq_some_iff.mp hex
          simp at h; obtain ⟨rfl, rfl⟩ := h
          obtain ⟨hc2, ha2, hok⟩ := hl.2 s2 curr' cc' h2
          refine ⟨rfl, ?_, ?_⟩
          · have hle := Cache.keyFor_le s2.cache cc'
            refine ⟨hok.1, hok.2.1, fun f => ?_, by simp, ?_⟩
            · have := hok.2.2 f; subst this; simp [Cache.keyFor, Cache.get]
            · unfold Cache.keyFor
              split
              · exact KeyIn.none _
              · intro m q e; simp at e; obtain ⟨rfl, -⟩ := e; simp
          · have hle := Cache.keyFor_le s2.cache cc'
            simp only at hc2 ha2
            rw [hc2] at hle ⊢
            exact ha2.mono hle
    | [], [], ha, hf => simp [mstep] at hf
    | [], _ :: _, ha, hf => exact ha.elim
    | _ :: _, [], ha, hf => exact ha.elim
  | rem c =>
    simp [Op.mapM] at hop; subst hop; simp [Exec.blank, Op.toR] at hr; subst hr
    match hst : s.stack, ts, ha, hf with
    | key :: cont :: rest, kt :: ct :: ts₀, ha, hf =>
      simp only [mstep] at hf
      split at hf
      · simp at hf
      · rename_i hnh
        simp at hf; subst hf
        cases hkv : key.val.asCell with
        | none =>
          refine ⟨fun _ => ?_, fun s' k hex => ?_⟩
          · simp [ROp.decache, exec_rem_gen, VmState.popCell, VmState.pop, hst, hkv]
          · simp [exec_rem_gen, VmState.popCell, VmState.pop, hst, hkv] at hex
        | some kv =>
          have hpc : s.popCell = some (kv, { s with stack := cont :: rest }) := by
            simp [VmState.popCell, VmState.pop, hst, hkv]
          have hp2 : ({ s with stack := cont :: rest } : VmState).pop = some (cont, { s with stack := rest }) := by
            simp [VmState.pop]
          refine ⟨fun hch => ?_, fun s' k hex => ?_⟩
          · simp only [ROp.decache]
            rw [exec_rem_gen, exec_rem_gen, hpc]
            simp only [Option.bind_some, hp2]
            cases c with
            | false => rfl
            | true =>
              have : mhit ct kt = true := by simp_all
              simp [mhit_ok ha.2.1 ha.1 hkv this]
          · rw [exec_rem_gen, hpc] at hex
            simp only [Option.bind_some, hp2] at hex
            split at hex
            · simp at hex
            · obtain ⟨next, hn, h⟩ := Option.map_eq_some_iff.mp hex
              simp [VmState.push] at h; obtain ⟨rfl, rfl⟩ := h
              exact ⟨rfl, ⟨⟨trivial, ha.2.1.2.1, ha.2.1.2.2.1, ha.2.1.2.2.2.1, ha.2.1.2.2.2.2⟩, ha.2.2⟩⟩
    | [], [], ha, hf => simp [mstep] at hf
    | [], _ :: _, ha, hf => exact ha.elim
    | [_], [], ha, hf => exact ha.elim
    | [_], [_], ha, hf => simp [mstep] at hf
    | [_], _ :: _ :: _, ha, hf => exact ha.2.elim
    | _ :: _ :: _, [], ha, hf => exact ha.elim
    | _ :: _ :: _, [_], ha, hf => exact ha.2.elim
  | branch n => simp [mstep] at hf
  | jmp n => simp [mstep] at hf

end Step

/-! ## Forgetting the cache -/

/-- An entry without its cache key. -/
def Entry.er (e : Entry) : Entry := { e with key := none }
def VmState.er (pre : List AV) (s : VmState) : VmState := ⟨s.stack.map Entry.er, [], pre ++ s.reads⟩

@[simp] theorem er_stack (pre : List AV) (s : VmState) : (s.er pre).stack = s.stack.map Entry.er := rfl
@[simp] theorem er_cache (pre : List AV) (s : VmState) : (s.er pre).cache = [] := rfl
@[simp] theorem er_reads (pre : List AV) (s : VmState) : (s.er pre).reads = pre ++ s.reads := rfl
@[simp] theorem Entry.er_val (e : Entry) : e.er.val = e.val := rfl
@[simp] theorem Entry.er_strong (e : Entry) : e.er.strong = e.strong := rfl
@[simp] theorem Entry.er_key (e : Entry) : e.er.key = none := rfl

theorem pop_er (pre : List AV) (s : VmState) :
    (s.er pre).pop = s.pop.map fun r => (r.1.er, r.2.er pre) := by
  obtain ⟨st, c, r⟩ := s
  cases st <;> rfl

theorem popCell_er (pre : List AV) (s : VmState) :
    (s.er pre).popCell = s.popCell.map fun r => (r.1, r.2.er pre) := by
  obtain ⟨st, c, r⟩ := s
  cases st with
  | nil => rfl
  | cons e es => simp [VmState.popCell, VmState.pop]; cases e.val.asCell <;> rfl

theorem popU64_er (pre : List AV) (s : VmState) :
    (s.er pre).popU64 = s.popU64.map fun r => (r.1, r.2.er pre) := by
  simp only [VmState.popU64, popCell_er, Option.bind_eq_bind]
  cases s.popCell with
  | none => rfl
  | some r => simp; cases r.1.toU64 <;> rfl

theorem popBool_er (pre : List AV) (s : VmState) :
    (s.er pre).popBool = s.popBool.map fun r => (r.1, r.2.er pre) := by
  simp only [VmState.popBool, popCell_er, Option.bind_eq_bind]
  cases s.popCell with
  | none => rfl
  | some r => simp; cases r.1.toBool <;> rfl

theorem pushNew_er (pre : List AV) (s : VmState) (v : SV) : (s.pushNew v).er pre = (s.er pre).pushNew v := rfl
theorem push_er (pre : List AV) (s : VmState) (e : Entry) : (s.push e).er pre = (s.er pre).push e.er := rfl


theorem Entry.er_none (v : SV) (st : Bool) : ({ val := v, strong := st, key := none } : Entry).er = ⟨v, st, none⟩ := rfl

theorem reads_er (pre : List AV) (s : VmState) (v : AV) :
    ({ s with reads := s.reads ++ [v] } : VmState).er pre = { s.er pre with reads := (s.er pre).reads ++ [v] } := by
  simp [VmState.er]

theorem idxWalk_er (pre : List AV) (pp : Bool) : ∀ (keys : List Entry) (s : VmState) (curr : Entry),
    (idxWalk false pp keys s curr).map (·.er pre) = idxWalk false pp (keys.map Entry.er) (s.er pre) curr.er
  | [], s, curr => by simp [idxWalk, VmState.push, VmState.er]
  | key :: keys, s, curr => by
      cases hkv : key.val.asCell with
      | none => simp [idxWalk, hkv]
      | some k =>
        rw [idxWalk_cons _ _ _ _ _ _ _ hkv, List.map_cons, idxWalk_cons _ _ _ _ _ _ _ (by simpa using hkv)]
        rw [idxOne_uncached, idxOne_uncached]
        cases hsv : svStep curr.val k with
        | none => simp [hsv]
        | some res =>
          simp only [Entry.er_val, hsv, Option.map_some, Option.bind_some]
          have := idxWalk_er pre pp keys
            { (if pp then (s.push curr).push { key with key := none } else s) with
                cache := (s.cache.visit (curr.key.push k)).1 }
            { val := res, strong := curr.strong, key := curr.key.push k }
          rw [this]
          cases pp <;> rfl

theorem insLoop_er (pre : List AV) : ∀ (n : Nat) (s : VmState) (curr : Entry) (cc : CTree),
    (insLoop false n s curr cc).map (fun x => (x.1.er pre, x.2.1.er, CTree.full)) =
      insLoop false n (s.er pre) curr.er .full
  | 0, s, curr, cc => by simp [insLoop]
  | n + 1, s, curr, cc => by
      rw [insLoop_succ, insLoop_succ, pop_er]
      cases hp : s.pop with
      | none => rfl
      | some r =>
        obtain ⟨key, s1⟩ := r
        simp only [Option.map_some, Option.bind_some, pop_er]
        cases hp2 : s1.pop with
        | none => rfl
        | some r' =>
          obtain ⟨cont, s2⟩ := r'
          simp only [Option.map_some, Option.bind_some, Entry.er_val]
          cases key.val.asCell with
          | none => rfl
          | some k =>
            simp only [Option.bind_some, insBlocked, Bool.false_and, Bool.false_eq_true, ite_false]
            cases insNext cont.val k curr.val with
            | none => rfl
            | some next =>
              simp only [Option.bind_some]
              rw [insLoop_er pre n s2 _ _]
              simp [Cache.get, insCache]
              rfl

def ROp.shaped : ROp → Prop
  | .idx _ pp path => (∃ kvs : List AV, path = kvs.map Key.value) ∨
      (pp = false ∧ ∃ kvs : List AV, path = kvs.map Key.value ++ [.stack])
  | _ => True

theorem keyEntry_er (kvs : List AV) : (kvs.map keyEntry).map Entry.er = kvs.map keyEntry := by
  induction kvs <;> simp_all [keyEntry, Entry.er]

theorem exec_er (H : Hooks) (pre : List AV) (s : VmState) (r : ROp) (hr : r.decache = r) (hs : r.shaped) :
    (ROp.exec H s r).map (fun x => (x.1.er pre, x.2)) = ROp.exec H (s.er pre) r := by
  cases r
  case idx c pp path =>
    simp only [ROp.decache, ROp.idx.injEq] at hr; obtain ⟨rfl, -, -⟩ := hr
    rcases hs with ⟨kvs, rfl⟩ | ⟨rfl, kvs, rfl⟩
    · rw [exec_idx_gen, exec_idx_gen, pop_er]
      cases s.pop with
      | none => rfl
      | some r =>
        simp only [Option.bind_some, Option.map_some, Option.map_map]
        have := idxWalk_er pre pp (kvs.map keyEntry) r.2 r.1
        rw [keyEntry_er] at this
        rw [← this]
        cases idxWalk false pp (kvs.map keyEntry) r.2 r.1 <;> rfl
    · rw [exec_idxs_gen, exec_idxs_gen]
      obtain ⟨st, c0, r0⟩ := s
      rcases st with _ | ⟨sk, _ | ⟨curr, rest⟩⟩
      · rfl
      · rfl
      · simp only [er_stack, List.map_cons]
        have := idxWalk_er pre false (kvs.map keyEntry ++ [sk]) ⟨rest, c0, r0⟩ curr
        simp only [List.map_append, keyEntry_er, List.map_cons, List.map_nil] at this
        rw [show ({ VmState.er pre ⟨sk :: curr :: rest, c0, r0⟩ with stack := rest.map Entry.er } : VmState) =
          VmState.er pre ⟨rest, c0, r0⟩ from rfl, ← this]
        cases idxWalk false false (kvs.map keyEntry ++ [sk]) ⟨rest, c0, r0⟩ curr <;> rfl
  case ins c n =>
    simp only [ROp.decache, ROp.ins.injEq] at hr; obtain ⟨rfl, -⟩ := hr
    rw [exec_ins_gen, exec_ins_gen]
    simp only [er_stack, List.length_map]
    split
    · rfl
    · rw [pop_er]
      cases s.pop with
      | none => rfl
      | some r =>
        simp only [Option.bind_some, Option.map_some, Option.map_map]
        have := insLoop_er pre n r.2 r.1 (r.2.cache.get r.1.key)
        simp only [er_cache] at this ⊢
        rw [show Cache.get ([] : Cache) r.1.er.key = .full from rfl, ← this]
        cases insLoop false n r.2 r.1 (r.2.cache.get r.1.key) with
        | none => rfl
        | some x => simp [VmState.er, Cache.keyFor, Entry.er]
  case rem c =>
    simp only [ROp.decache, ROp.rem.injEq] at hr; subst hr
    rw [exec_rem_gen, exec_rem_gen, popCell_er]
    cases s.popCell with
    | none => rfl
    | some r =>
      simp only [Option.bind_some, Option.map_some, pop_er]
      cases r.2.pop with
      | none => rfl
      | some r' =>
        simp only [Option.bind_some, Option.map_some, Bool.false_and, Bool.false_eq_true, ite_false, Entry.er_val]
        cases remNext r'.1.val r.1 <;> rfl
  case swap n =>
    simp only [ROp.exec, er_stack, List.length_map]
    split
    · rfl
    · obtain ⟨st, c0, r0⟩ := s
      simp only [List.getElem?_map]
      cases st[0]? <;> cases st[n + 1]? <;> simp [VmState.er, List.map_set]
  case popeq c =>
    simp only [ROp.exec, er_stack, List.length_map]
    split
    · rfl
    · simp [popCell_er, Option.map_bind, Option.bind_map, Function.comp_def, reads_er]
  case push st v =>
    simp only [ROp.exec, VmState.push]
    split <;> simp_all [VmState.er, Entry.er]
  case eq =>
    simp only [ROp.exec, er_stack, List.length_map]
    split
    · rfl
    · simp only [popCell_er, Option.bind_eq_bind, Option.map_bind, Option.bind_map, Function.comp_def]
      congr 1; funext x; congr 1; funext y
      cases decide (x.1.size ≤ 64) <;> cases decide (y.1.size ≤ 64) <;> rfl
  case size =>
    simp only [ROp.exec, er_stack, List.length_map]
    split
    · rfl
    · simp only [pop_er, Option.bind_eq_bind, Option.map_bind, Option.bind_map, Function.comp_def, Entry.er_val]
      congr 1; funext x
      split <;> simp [pushNew_er]
  case root =>
    simp only [ROp.exec, er_stack, List.length_map]
    split
    · rfl
    · simp only [pop_er, Option.bind_eq_bind, Option.map_bind, Option.bind_map, Function.comp_def, Entry.er_val]
      congr 1; funext x
      split
      · cases H.root _ _ <;> rfl
      · rfl
  case member =>
    simp only [ROp.exec, er_stack, List.length_map]
    split
    · rfl
    · simp only [popCell_er, pop_er, Option.bind_eq_bind, Option.map_bind, Option.bind_map, Function.comp_def,
        Entry.er_val]
      congr 1; funext x; congr 1; funext y
      split <;> simp [pushNew_er]
  case concat c n =>
    simp only [ROp.exec, er_stack, List.length_map]
    split
    · rfl
    · split
      · rfl
      · simp only [popCell_er, Option.bind_eq_bind, Option.map_bind, Option.bind_map, Function.comp_def]
        congr 1; funext x; congr 1; funext y
        split <;> simp [pushNew_er]
  all_goals
    simp only [ROp.exec, er_stack, List.length_map]
    split
    · rfl
    · simp [Function.comp_def, popU64_er, popCell_er, popBool_er, pop_er, Option.map_bind, Option.bind_map,
        pushNew_er, push_er]

theorem runR_er (H : Hooks) (pre : List AV) :
    ∀ (n : Nat) (rops : List ROp), rops.length ≤ n → (∀ r ∈ rops, r.decache = r ∧ r.shaped) → ∀ s,
      (runR H rops s).map (·.er pre) = runR H rops (s.er pre)
  | _, [], _, _, s => by simp [runR]
  | 0, _ :: _, hn, _, _ => by simp at hn
  | n + 1, r :: rest, hn, hr, s => by
      rw [runR_cons, runR_cons, ← exec_er H pre s r (hr r (by simp)).1 (hr r (by simp)).2]
      cases hex : r.exec H s with
      | none => rfl
      | some x =>
        obtain ⟨s1, k⟩ := x
        simp only [Option.bind_some, Option.map_some, er_stack, List.length_map]
        split
        · rfl
        · split
          · rfl
          · exact runR_er H pre n (rest.drop k) (by simp at hn ⊢; omega)
              (fun r' hr' => hr r' (List.mem_cons_of_mem _ (List.mem_of_mem_drop hr'))) s1

/-! ## Whole programs -/

def _root_.Damp.Impact.Op.skipN {α : Type} : Op α → Nat
  | .branch n => n
  | .jmp n => n
  | _ => 0

theorem toR_props {o : Op Fr} {r : ROp} (h : Op.toR o = some r) :
    r.skipMax = o.skipN ∧ r.shaped ∧ r.decache.shaped := by
  cases o
  case addi i =>
    cases hm : immOf i <;> simp [Op.toR, hm] at h; subst h; exact ⟨rfl, trivial, trivial⟩
  case subi i =>
    cases hm : immOf i <;> simp [Op.toR, hm] at h; subst h; exact ⟨rfl, trivial, trivial⟩
  case push st v =>
    cases hm : AV.ofAligned v <;> simp [Op.toR, hm] at h; subst h; exact ⟨rfl, trivial, trivial⟩
  case pushState st v =>
    cases hm : SV.ofLit v <;> simp [Op.toR, hm] at h; subst h; exact ⟨rfl, trivial, trivial⟩
  case idx c pp path =>
    cases hm : path.mapM AV.ofAligned with
    | none => simp [Op.toR, hm] at h
    | some kvs =>
      simp [Op.toR, hm] at h; subst h
      exact ⟨rfl, Or.inl ⟨kvs, rfl⟩, Or.inl ⟨kvs, rfl⟩⟩
  case idxStack pre =>
    cases hm : pre.mapM AV.ofAligned with
    | none => simp [Op.toR, hm] at h
    | some kvs =>
      simp [Op.toR, hm] at h; subst h
      exact ⟨rfl, Or.inr ⟨rfl, kvs, rfl⟩, Or.inr ⟨rfl, kvs, rfl⟩⟩
  all_goals (simp [Op.toR] at h; subst h; exact ⟨rfl, trivial, trivial⟩)

theorem blank_skipN (o : Op Fr) : (Exec.blank o).skipN = o.skipN := by
  cases o <;> rfl

theorem mapM_skipN {p : Prims} {env : Env} {op : Op Expr} {op' : Op Fr} (h : op.mapM (Expr.eval p env) = some op') :
    op'.skipN = op.skipN := by
  cases op <;> simp [Op.mapM, Option.bind_eq_some_iff] at h <;> (try (obtain ⟨_, _, rfl⟩ := h)) <;>
    (try subst h) <;> rfl

theorem OpEvals.props {p : Prims} {env : Env} {op : Op Expr} {r : ROp} (h : OpEvals p env op r) :
    r.skipMax = op.skipN ∧ r.shaped ∧ r.decache.shaped := by
  obtain ⟨op', hop, hr⟩ := h
  obtain ⟨h1, h2, h3⟩ := toR_props hr
  exact ⟨by rw [h1, blank_skipN, mapM_skipN hop], h2, h3⟩

theorem AllEval.length {p : Prims} {env : Env} : ∀ {ops : List (Op Expr)} {rs : List ROp},
    AllEval p env ops rs → rs.length = ops.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [AllEval.length h.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem AllEval.props {p : Prims} {env : Env} : ∀ {ops : List (Op Expr)} {rs : List ROp},
    AllEval p env ops rs → ∀ r ∈ rs.map ROp.decache, r.decache = r ∧ r.shaped
  | [], [], _ => by simp
  | _ :: _, r :: _, h => by
      intro x hx
      simp only [List.map_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨ROp.decache_decache r, (h.1.props).2.2⟩
      · exact AllEval.props h.2 x hx
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem mcheck_other {check : Bool} {fin : List MTag → Bool} {fuel : Nat} {op : Op Expr} {rest : List (Op Expr)}
    {ts : List MTag} (hb : ∀ n, op ≠ .branch n) (hj : ∀ n, op ≠ .jmp n)
    (h : mcheck check fin (fuel + 1) (op :: rest) ts = true) :
    ∃ ts', mstep check op ts = some ts' ∧ mcheck check fin fuel rest ts' = true := by
  cases op
  case branch n => exact absurd rfl (hb n)
  case jmp n => exact absurd rfl (hj n)
  all_goals
    simp only [mcheck] at h
    split at h
    · rename_i ts' hts; exact ⟨ts', hts, h⟩
    · simp at h

theorem runR_cons_eq (H : Hooks) {r r' : ROp} {rest rest' : List ROp} {s : VmState}
    (he : r.exec H s = r'.exec H s) (hl : rest.length = rest'.length)
    (hk : ∀ s1 k, r.exec H s = some (s1, k) → runR H (rest.drop k) s1 = runR H (rest'.drop k) s1) :
    runR H (r :: rest) s = runR H (r' :: rest') s := by
  rw [runR_cons, runR_cons, ← he]
  cases hex : r.exec H s with
  | none => rfl
  | some x =>
    obtain ⟨s1, k⟩ := x
    simp only [Option.bind_some, hl]
    split
    · rfl
    · split
      · rfl
      · exact hk s1 k hex

theorem runR_cons_append (H : Hooks) {r : ROp} {rest l₂ : List ROp} {s : VmState}
    (hk : ∀ s1 k, r.exec H s = some (s1, k) →
      k ≤ rest.length ∧ runR H (rest.drop k ++ l₂) s1 = (runR H (rest.drop k) s1).bind (runR H l₂)) :
    runR H (r :: rest ++ l₂) s = (runR H (r :: rest) s).bind (runR H l₂) := by
  rw [List.cons_append, runR_cons, runR_cons]
  cases hex : r.exec H s with
  | none => rfl
  | some x =>
    obtain ⟨s1, k⟩ := x
    obtain ⟨hkl, hrec⟩ := hk s1 k hex
    have hk1 : ¬ k > (rest ++ l₂).length := by simp; omega
    have hk2 : ¬ k > rest.length := by omega
    simp only [Option.bind_some, hk1, hk2, ite_false]
    split
    · rfl
    · rw [List.drop_append_of_le_length hkl]; exact hrec

/-- **The analysis is sound.** If `mcheck` accepts a program, then in any run
    from a state the starting tags describe: running the program followed by
    anything runs the program, then the rest (its jumps stay inside it); with
    `check`, the program runs exactly as with its cached flags cleared; and a
    successful run ends in a state described by tags that pass `fin`. -/
theorem mcheck_sound (V : Nat → SV) (H : Hooks) {p : Prims} {env : Env} {check : Bool} {fin : List MTag → Bool} :
    ∀ (fuel : Nat) (ops : List (Op Expr)) (rops : List ROp) (ts : List MTag) (s : VmState),
      mcheck check fin fuel ops ts = true → AllEval p env ops rops → MAgrees V s.cache ts s.stack →
      (∀ l₂, runR H (rops ++ l₂) s = (runR H rops s).bind (runR H l₂)) ∧
      (check = true → runR H rops s = runR H (rops.map ROp.decache) s) ∧
      (∀ s', runR H rops s = some s' → ∃ ts', fin ts' = true ∧ MAgrees V s'.cache ts' s'.stack)
  | 0, _, _, _, _, hf, _, _ => by simp [mcheck] at hf
  | fuel + 1, [], rops, ts, s, hf, he, ha => by
      cases rops with
      | cons => exact he.elim
      | nil =>
        refine ⟨fun l₂ => by simp [runR], fun _ => rfl, fun s' hr => ?_⟩
        simp [runR] at hr; subst hr
        simp only [mcheck] at hf
        exact ⟨ts, hf, ha⟩
  | fuel + 1, op :: rest, rops, ts, s, hf, he, ha => by
      cases rops with
      | nil => exact he.elim
      | cons r rrest =>
        obtain ⟨hr1, hrest⟩ := he
        have hlen := AllEval.length hrest
        by_cases hbr : ∃ n, op = .branch n
        · obtain ⟨n, rfl⟩ := hbr
          obtain ⟨op', hop, hr1'⟩ := hr1
          simp [Op.mapM] at hop; subst hop; simp [Exec.blank, Op.toR] at hr1'; subst hr1'
          simp only [mcheck] at hf
          match ts, ha, hf with
          | _ :: ts₀, ha, hf =>
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
            obtain ⟨⟨hn, hf1⟩, hf2⟩ := hf
            have hstep : ∀ s1 k, (ROp.branch n).exec H s = some (s1, k) →
                (k = 0 ∨ k = n) ∧ MAgrees V s1.cache ts₀ s1.stack := by
              intro s1 k hex
              obtain ⟨hk, hs1⟩ := exec_branch H hex
              have hc := exec_cache H (by simp) (by simp) hex
              exact ⟨hk, by rw [hs1, hc]; exact ha.drop 1⟩
            have ih : ∀ s1 k, (ROp.branch n).exec H s = some (s1, k) →
                k ≤ rrest.length ∧
                (∀ l₂, runR H (rrest.drop k ++ l₂) s1 = (runR H (rrest.drop k) s1).bind (runR H l₂)) ∧
                (check = true → runR H (rrest.drop k) s1 = runR H ((rrest.drop k).map ROp.decache) s1) ∧
                (∀ s', runR H (rrest.drop k) s1 = some s' → ∃ ts', fin ts' = true ∧ MAgrees V s'.cache ts' s'.stack) := by
              intro s1 k hex
              obtain ⟨hk, ha1⟩ := hstep s1 k hex
              rcases hk with rfl | rfl
              · simpa using mcheck_sound V H fuel rest rrest ts₀ s1 hf1 hrest ha1
              · exact ⟨by omega, mcheck_sound V H fuel (rest.drop k) (rrest.drop k) ts₀ s1 hf2 (hrest.drop k) ha1⟩
            refine ⟨fun l₂ => runR_cons_append H fun s1 k hex => ⟨(ih s1 k hex).1, (ih s1 k hex).2.1 l₂⟩,
              fun hch => ?_, fun s' hr => ?_⟩
            · exact runR_cons_eq H rfl (by simp) fun s1 k hex => by
                rw [← List.map_drop]; exact (ih s1 k hex).2.2.1 hch
            · rw [runR_cons] at hr
              obtain ⟨⟨s1, k⟩, hex, hr⟩ := bind_some_elim hr
              simp only at hr
              split at hr; · simp at hr
              split at hr; · simp at hr
              exact (ih s1 k hex).2.2.2 s' hr
        · by_cases hjm : ∃ n, op = .jmp n
          · obtain ⟨n, rfl⟩ := hjm
            obtain ⟨op', hop, hr1'⟩ := hr1
            simp [Op.mapM] at hop; subst hop; simp [Exec.blank, Op.toR] at hr1'; subst hr1'
            simp only [mcheck, Bool.and_eq_true, decide_eq_true_eq] at hf
            obtain ⟨hn, hf⟩ := hf
            have ih : ∀ s1 k, (ROp.jmp n).exec H s = some (s1, k) →
                k ≤ rrest.length ∧
                (∀ l₂, runR H (rrest.drop k ++ l₂) s1 = (runR H (rrest.drop k) s1).bind (runR H l₂)) ∧
                (check = true → runR H (rrest.drop k) s1 = runR H ((rrest.drop k).map ROp.decache) s1) ∧
                (∀ s', runR H (rrest.drop k) s1 = some s' → ∃ ts', fin ts' = true ∧ MAgrees V s'.cache ts' s'.stack) := by
              intro s1 k hex
              obtain ⟨hk, hss⟩ := exec_jmp H hex
              subst hk; subst s1
              exact ⟨by omega, mcheck_sound V H fuel (rest.drop k) (rrest.drop k) ts s hf (hrest.drop k) ha⟩
            refine ⟨fun l₂ => runR_cons_append H fun s1 k hex => ⟨(ih s1 k hex).1, (ih s1 k hex).2.1 l₂⟩,
              fun hch => ?_, fun s' hr => ?_⟩
            · exact runR_cons_eq H rfl (by simp) fun s1 k hex => by
                rw [← List.map_drop]; exact (ih s1 k hex).2.2.1 hch
            · rw [runR_cons] at hr
              obtain ⟨⟨s1, k⟩, hex, hr⟩ := bind_some_elim hr
              simp only at hr
              split at hr; · simp at hr
              split at hr; · simp at hr
              exact (ih s1 k hex).2.2.2 s' hr
          · have hb : ∀ n, op ≠ .branch n := fun n h => hbr ⟨n, h⟩
            have hj : ∀ n, op ≠ .jmp n := fun n h => hjm ⟨n, h⟩
            obtain ⟨ts', hfs, hf⟩ := mcheck_other hb hj hf
            have hok := mstep_ok V H hr1 hfs ha
            have ih : ∀ s1 k, r.exec H s = some (s1, k) →
                k ≤ rrest.length ∧
                (∀ l₂, runR H (rrest.drop k ++ l₂) s1 = (runR H (rrest.drop k) s1).bind (runR H l₂)) ∧
                (check = true → runR H (rrest.drop k) s1 = runR H ((rrest.drop k).map ROp.decache) s1) ∧
                (∀ s', runR H (rrest.drop k) s1 = some s' → ∃ ts', fin ts' = true ∧ MAgrees V s'.cache ts' s'.stack) := by
              intro s1 k hex
              obtain ⟨rfl, ha1⟩ := hok.2 s1 k hex
              simpa using mcheck_sound V H fuel rest rrest ts' s1 hf hrest ha1
            refine ⟨fun l₂ => runR_cons_append H fun s1 k hex => ⟨(ih s1 k hex).1, (ih s1 k hex).2.1 l₂⟩,
              fun hch => ?_, fun s' hr => ?_⟩
            · exact runR_cons_eq H (hok.1 hch) (by simp) fun s1 k hex => by
                rw [← List.map_drop]; exact (ih s1 k hex).2.2.1 hch
            · rw [runR_cons] at hr
              obtain ⟨⟨s1, k⟩, hex, hr⟩ := bind_some_elim hr
              simp only at hr
              split at hr; · simp at hr
              split at hr; · simp at hr
              exact (ih s1 k hex).2.2.2 s' hr

/-! ## How many values a program reads -/

def ROp.reads1 : ROp → Nat
  | .popeq _ => 1
  | _ => 0

theorem idxWalk_reads (c pp : Bool) : ∀ (keys : List Entry) (s : VmState) (curr : Entry) (s' : VmState),
    idxWalk c pp keys s curr = some s' → s'.reads = s.reads
  | [], s, curr, s', h => by simp [idxWalk, VmState.push] at h; subst h; rfl
  | key :: keys, s, curr, s', h => by
      cases hkv : key.val.asCell with
      | none => simp [idxWalk, hkv] at h
      | some k =>
        rw [idxWalk_cons _ _ _ _ _ _ _ hkv] at h
        obtain ⟨r, _, h⟩ := bind_some_elim h
        rw [idxWalk_reads c pp keys _ r.2 s' h]
        cases pp <;> rfl

theorem insLoop_reads (c : Bool) : ∀ (n : Nat) (s : VmState) (curr : Entry) (cc : CTree) (s' : VmState) (curr' : Entry)
    (cc' : CTree), insLoop c n s curr cc = some (s', curr', cc') → s'.reads = s.reads
  | 0, s, curr, cc, s', curr', cc', h => by simp [insLoop] at h; obtain ⟨rfl, -, -⟩ := h; rfl
  | n + 1, s, curr, cc, s', curr', cc', h => by
      rw [insLoop_succ] at h
      obtain ⟨⟨key, s1⟩, h1, h⟩ := bind_some_elim h
      obtain ⟨⟨cont, s2⟩, h2, h⟩ := bind_some_elim h
      obtain ⟨k, _, h⟩ := bind_some_elim h
      split at h; · simp at h
      obtain ⟨next, _, h⟩ := bind_some_elim h
      rw [insLoop_reads c n _ _ _ s' curr' cc' h, (pop_eq h2).2, (pop_eq h1).2]

theorem exec_reads (H : Hooks) {s s' : VmState} {r : ROp} {k : Nat} (hs : r.shaped) (h : r.exec H s = some (s', k)) :
    ∃ X, s'.reads = s.reads ++ X ∧ X.length ≤ r.reads1 := by
  cases r
  case popeq c =>
    simp only [ROp.exec, Option.bind_eq_bind] at h
    split at h; · simp at h
    obtain ⟨⟨v, s1⟩, h1, h⟩ := bind_some_elim h
    simp at h; obtain ⟨rfl, -⟩ := h
    obtain ⟨e, he, _⟩ := popCell_entry h1
    simp only [VmState.popCell, Option.bind_eq_bind] at h1
    obtain ⟨⟨e', s0⟩, h0, h1⟩ := bind_some_elim h1
    obtain ⟨_, _, h1⟩ := bind_some_elim h1
    simp at h1; obtain ⟨-, rfl⟩ := h1
    exact ⟨[v], by rw [(pop_eq h0).2], by simp [ROp.reads1]⟩
  case idx c pp path =>
    rcases hs with ⟨kvs, rfl⟩ | ⟨rfl, kvs, rfl⟩
    · rw [exec_idx_gen] at h
      obtain ⟨⟨curr, s1⟩, h1, h⟩ := bind_some_elim h
      obtain ⟨s2, h2, h⟩ := Option.map_eq_some_iff.mp h
      simp at h; obtain ⟨rfl, -⟩ := h
      exact ⟨[], by rw [idxWalk_reads _ _ _ _ _ _ h2, (pop_eq h1).2]; simp, by simp⟩
    · rw [exec_idxs_gen] at h
      split at h
      · obtain ⟨s2, h2, h⟩ := Option.map_eq_some_iff.mp h
        simp at h; obtain ⟨rfl, -⟩ := h
        exact ⟨[], by rw [idxWalk_reads _ _ _ _ _ _ h2]; simp, by simp⟩
      · simp at h
  case ins c n =>
    rw [exec_ins_gen] at h
    split at h; · simp at h
    obtain ⟨⟨curr, s1⟩, h1, h⟩ := bind_some_elim h
    obtain ⟨⟨s2, curr', cc'⟩, h2, h⟩ := Option.map_eq_some_iff.mp h
    simp at h; obtain ⟨rfl, -⟩ := h
    exact ⟨[], by simp only [List.append_nil]; rw [insLoop_reads _ _ _ _ _ _ _ _ h2, (pop_eq h1).2], by simp⟩
  all_goals exact ⟨[], by rw [exec_reads_eq H (by simp) (by simp) (by simp) h]; simp, by simp⟩

theorem runR_reads (H : Hooks) : ∀ (n : Nat) (rops : List ROp), rops.length ≤ n → (∀ r ∈ rops, r.shaped) →
    ∀ s s', runR H rops s = some s' → ∃ X, s'.reads = s.reads ++ X ∧ X.length ≤ (rops.map ROp.reads1).sum
  | _, [], _, _, s, s', h => by simp [runR] at h; subst h; exact ⟨[], by simp, by simp⟩
  | 0, _ :: _, hn, _, _, _, _ => by simp at hn
  | n + 1, r :: rest, hn, hr, s, s', h => by
      rw [runR_cons] at h
      obtain ⟨⟨s1, k⟩, hex, h⟩ := bind_some_elim h
      simp only at h
      split at h; · simp at h
      split at h; · simp at h
      obtain ⟨X1, hX1, hl1⟩ := exec_reads H (hr r (by simp)) hex
      obtain ⟨X2, hX2, hl2⟩ := runR_reads H n (rest.drop k) (by simp at hn ⊢; omega)
        (fun r' hr' => hr r' (List.mem_cons_of_mem _ (List.mem_of_mem_drop hr'))) s1 s' h
      refine ⟨X1 ++ X2, by rw [hX2, hX1, List.append_assoc], ?_⟩
      have hdrop : ((rest.drop k).map ROp.reads1).sum ≤ (rest.map ROp.reads1).sum := by
        rw [List.map_drop]
        conv => rhs; rw [← List.take_append_drop k (rest.map ROp.reads1)]
        rw [List.sum_append]; omega
      simp only [List.length_append, List.map_cons, List.sum_cons]
      omega

theorem popeqAligns_append : ∀ (a b : List (Op Fr)), popeqAligns (a ++ b) = popeqAligns a ++ popeqAligns b
  | [], b => rfl
  | op :: a, b => by
      cases op <;> simp [popeqAligns, popeqAligns_append a b]

theorem popeqAligns_length : ∀ {req : List (Op Fr)} {rops : List ROp}, req.mapM Op.toR = some rops →
    (rops.map ROp.reads1).sum = (popeqAligns req).length
  | [], rops, h => by simp at h; subst h; rfl
  | o :: os, rops, h => by
      simp only [List.mapM_cons, Option.bind_eq_bind] at h
      obtain ⟨r, hr, h⟩ := bind_some_elim h
      obtain ⟨rs, hrs, h⟩ := bind_some_elim h
      simp at h; subst h
      have ih := popeqAligns_length hrs
      cases o <;> simp [Op.toR, Option.bind_eq_some_iff] at hr <;>
        (try obtain ⟨_, _, rfl⟩ := hr) <;> (try subst hr) <;> simp [popeqAligns, ROp.reads1, ih] <;> omega

theorem readBack_length : ∀ {as : List (List Zkir.AlignAtom)} {vs : List AV} {f : List Fr},
    readBack as vs = some f → as.length = vs.length
  | [], [], _, _ => rfl
  | a :: as, v :: vs, f, h => by
      rw [readBack_cons] at h
      obtain ⟨_, _, h⟩ := bind_some_elim h
      obtain ⟨_, h', _⟩ := bind_some_elim h
      simp [readBack_length h']
  | [], _ :: _, _, h => by simp [readBack] at h
  | _ :: _, [], _, h => by simp [readBack] at h

theorem readBack_append : ∀ (as₁ as₂ : List (List Zkir.AlignAtom)) (vs₁ vs₂ : List AV), as₁.length = vs₁.length →
    readBack (as₁ ++ as₂) (vs₁ ++ vs₂) = (readBack as₁ vs₁).bind fun f₁ => (readBack as₂ vs₂).map (f₁ ++ ·)
  | [], as₂, [], vs₂, _ => by simp [readBack_nil]
  | a :: as₁, as₂, v :: vs₁, vs₂, h => by
      simp only [List.cons_append, readBack_cons, Option.bind_eq_bind]
      rw [readBack_append as₁ as₂ vs₁ vs₂ (by simpa using h)]
      cases fieldsOf a v.atoms with
      | none => rfl
      | some f =>
        simp only [Option.bind_some]
        cases readBack as₁ vs₁ with
        | none => rfl
        | some g =>
          simp only [Option.bind_some]
          cases readBack as₂ vs₂ <;> simp
  | [], _, _ :: _, _, h => by simp at h
  | _ :: _, _, [], _, h => by simp at h

/-! ## One request -/

theorem shaped_decache (r : ROp) : r.decache.shaped ↔ r.shaped := by
  cases r <;> exact Iff.rfl

/-- What `query` does after the program has run. -/
def finish (q : LedgerState) (s : VmState) : Option (List AV × LedgerState) :=
  match s.stack with
  | [st, eff, _] =>
      if st.strong then (decodeEffects eff.val).map fun effects => (s.reads, { q with state := st.val, effects })
      else none
  | _ => none

theorem query_eq (H : Hooks) (rops : List ROp) (q : LedgerState) :
    query H rops q = (runR H rops q.vm).bind (finish q) := by
  unfold query finish
  cases runR H rops q.vm with
  | none => rfl
  | some s =>
    simp only [Option.bind_some, Option.bind_eq_bind]
    rcases h : s.stack with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;> simp only [h]
    by_cases ha : a.strong = true <;> simp only [ha, ite_true, ite_false, Bool.false_eq_true]
    cases decodeEffects b.val <;> rfl

theorem finish_er (q : LedgerState) (pre : List AV) (s : VmState) :
    finish q (s.er pre) = (finish q s).map fun x => (pre ++ x.1, x.2) := by
  unfold finish
  obtain ⟨st, c, r⟩ := s
  rcases st with _ | ⟨a, _ | ⟨b, _ | ⟨d, _ | ⟨e, rest⟩⟩⟩⟩ <;> simp [VmState.er]
  split <;> simp_all
  cases decodeEffects b.val <;> simp

/-- The initial values of a request, as the tags `orig i` name them. -/
def qV (q : LedgerState) : Nat → SV
  | 0 => q.context
  | 1 => q.effects
  | _ => q.state

theorem minit_ok (q : LedgerState) (hq : q.WF) : MAgrees (qV q) q.vm.cache minit q.vm.stack := by
  rw [vm_eq]
  refine ⟨⟨rfl, by simp [minit, initStack], by simp [minit], by simp [minit], ?_⟩,
    ⟨hq, by simp [minit, initStack], fun _ => rfl, by simp [minit], ?_⟩,
    ⟨rfl, by simp [minit, initStack], fun _ => rfl, by simp [minit], ?_⟩, trivial⟩ <;>
  · intro n p h; simp [initStack] at h; obtain ⟨rfl, -⟩ := h; simp

/-- **One request is two.** If `ops₁` leaves the stack as a request starts it
    (`mcheck false mboundary`) and every cached instruction of `ops₂` hits
    (`mcheck true`), then on a well-formed state the request of `ops₁ ++ ops₂`
    reads what the request of `ops₁` and then the request of `ops₂` read, and
    leaves the same state; one fails exactly when the other does. -/
theorem ledgerOracle_merge (H : Hooks) {p : Prims} {env : Env} {ops₁ ops₂ : List (Op Expr)} {f₁ f₂ : Nat}
    (hm₁ : mcheck false mboundary f₁ ops₁ minit = true) (hm₂ : mcheck true (fun _ => true) f₂ ops₂ minit = true)
    {req₁ req₂ : List (Op Fr)} (hr₁ : Exec.request p env ops₁ = some req₁) (hr₂ : Exec.request p env ops₂ = some req₂)
    (q : LedgerState) (hq : q.WF) :
    ledgerOracle H (req₁ ++ req₂) q =
      (ledgerOracle H req₁ q).bind fun r₁ => (ledgerOracle H req₂ r₁.2).map fun r₂ => (r₁.1 ++ r₂.1, r₂.2) := by
  unfold ledgerOracle
  rw [List.mapM_append, popeqAligns_append]
  cases hrops₁ : req₁.mapM Op.toR with
  | none => rfl
  | some rops₁ =>
  cases hrops₂ : req₂.mapM Op.toR with
  | none =>
    simp only [Option.bind_some, Option.bind_none, Option.bind_eq_bind]
    cases query H rops₁ q with
    | none => rfl
    | some x => cases readBack (popeqAligns req₁) x.1 <;> simp
  | some rops₂ =>
  simp only [Option.bind_some, Option.pure_def, Option.bind_eq_bind]
  have he₁ := request_allEval hr₁ hrops₁
  have he₂ := request_allEval hr₂ hrops₂
  have hs₁ := mcheck_sound (qV q) H f₁ ops₁ rops₁ minit q.vm hm₁ he₁ (minit_ok q hq)
  rw [query_eq, query_eq, hs₁.1 rops₂]
  cases hb : runR H rops₁ q.vm with
  | none => rfl
  | some sb =>
  simp only [Option.bind_some]
  obtain ⟨tb, hfin, hab⟩ := hs₁.2.2 sb hb
  -- the stack after `ops₁`
  obtain ⟨stt, efft, ctxt, rfl⟩ : ∃ a b c, tb = [a, b, c] := by
    unfold mboundary at hfin; split at hfin
    · exact ⟨_, _, _, rfl⟩
    · simp at hfin
  obtain ⟨st, eff, ctx, hst⟩ : ∃ x y z, sb.stack = [x, y, z] := by
    have hl := hab.length
    match h : sb.stack, hl with
    | [x, y, z], _ => exact ⟨x, y, z, rfl⟩
  rw [hst] at hab
  simp only [mboundary, Bool.and_eq_true, beq_iff_eq] at hfin
  obtain ⟨⟨⟨⟨⟨⟨hst1, hev⟩, hes⟩, hefc⟩, hcv⟩, hcs⟩, hcfc⟩ := hfin
  have hstrong : st.strong = true := hab.1.2.1 true hst1
  have hdec : decodeEffects eff.val = some eff.val := by have := hab.2.1.1; rw [hev] at this; exact this
  have heffs : eff.strong = false := hab.2.1.2.1 false hes
  have hctxv : ctx.val = q.context := by have := hab.2.2.1.1; rw [hcv] at this; exact this
  have hctxs : ctx.strong = false := hab.2.2.1.2.1 false hcs
  have hfin₁ : finish q sb = some (sb.reads, { q with state := st.val, effects := eff.val }) := by
    unfold finish; rw [hst]
    simp only [hstrong, ite_true, hdec]
    rfl
  rw [hfin₁]
  simp only [Option.bind_some]
  generalize hq₁ : ({ q with state := st.val, effects := eff.val } : LedgerState) = q₁
  have hq₁c : q₁.context = q.context := by rw [← hq₁]
  have hq₁e : q₁.effects = eff.val := by rw [← hq₁]
  have hq₁wf : q₁.WF := by rw [LedgerState.WF, hq₁e]; exact hdec
  have hq₁s : q₁.state = st.val := by rw [← hq₁]
  -- `ops₂` runs as with its cached flags cleared, after `ops₁` and alone
  have hinit_b : MAgrees (qV q₁) sb.cache minit sb.stack := by
    rw [hst]
    refine ⟨⟨by simp [MVal.Ok, minit, qV, hq₁s], by simp [minit, hstrong], by simp [minit], by simp [minit],
        hab.1.2.2.2.2⟩,
      ⟨by simp [qV, hq₁e, MVal.Ok, minit, hdec], by simp [minit, heffs], fun _ => hab.2.1.2.2.1 hefc, by simp [minit],
        hab.2.1.2.2.2.2⟩,
      ⟨by simp [qV, hq₁c, hctxv, MVal.Ok, minit], by simp [minit, hctxs], fun _ => hab.2.2.1.2.2.1 hcfc,
        by simp [minit], hab.2.2.1.2.2.2.2⟩, trivial⟩
  have hs₂b := mcheck_sound (qV q₁) H f₂ ops₂ rops₂ minit sb hm₂ he₂ hinit_b
  have hs₂f := mcheck_sound (qV q₁) H f₂ ops₂ rops₂ minit q₁.vm hm₂ he₂ (minit_ok q₁ hq₁wf)
  have hprops := AllEval.props he₂
  have hsb : sb.er [] = q₁.vm.er sb.reads := by
    rw [vm_eq]
    simp only [VmState.er, hst, initStack, List.map_cons, List.map_nil, List.nil_append, List.append_nil]
    simp [Entry.er, ← hq₁, hctxv, hstrong, heffs, hctxs]
  have hmerged : (runR H rops₂ sb).map (·.er []) = (runR H rops₂ q₁.vm).map (·.er sb.reads) := by
    rw [hs₂b.2.1 rfl, hs₂f.2.1 rfl, runR_er H [] _ _ (Nat.le_refl _) hprops, hsb,
      ← runR_er H sb.reads _ _ (Nat.le_refl _) hprops]
  have hfinq : ∀ t : VmState, finish q t = finish q (t.er []) := by
    intro t; rw [finish_er]; cases finish q t <;> rfl
  have hfinq₁ : ∀ t : VmState, finish q t = finish q₁ t := by
    intro t; unfold finish; split
    · split
      · cases decodeEffects _ <;> simp [hq₁c]
      · rfl
    · rfl
  have hq₂ : (runR H rops₂ sb).bind (finish q) =
      ((runR H rops₂ q₁.vm).bind (finish q₁)).map fun x => (sb.reads ++ x.1, x.2) := by
    have : (runR H rops₂ sb).bind (finish q) = ((runR H rops₂ sb).map (·.er [])).bind (finish q) := by
      cases runR H rops₂ sb with
      | none => rfl
      | some t => simp only [Option.bind_some, Option.map_some]; exact hfinq t
    rw [this, hmerged]
    cases runR H rops₂ q₁.vm with
    | none => rfl
    | some t => simp only [Option.map_some, Option.bind_some]; rw [finish_er, hfinq₁]
  rw [hq₂]
  -- reading the values back
  have hshape₁ : ∀ r ∈ rops₁, r.shaped := fun r hr =>
    (shaped_decache r).1 (AllEval.props he₁ r.decache (List.mem_map_of_mem hr)).2
  have hshape₂ : ∀ r ∈ rops₂, r.shaped := fun r hr =>
    (shaped_decache r).1 (AllEval.props he₂ r.decache (List.mem_map_of_mem hr)).2
  obtain ⟨X₁, hX₁, hl₁⟩ := runR_reads H _ rops₁ (Nat.le_refl _) hshape₁ q.vm sb hb
  rw [popeqAligns_length hrops₁] at hl₁
  rw [vm_eq] at hX₁; simp only [List.nil_append] at hX₁
  subst hX₁
  cases hr2 : runR H rops₂ q₁.vm with
  | none =>
    simp only [Option.bind_none, Option.map_none]
    cases readBack (popeqAligns req₁) sb.reads <;> simp [query_eq, hr2]
  | some t =>
    obtain ⟨X₂, hX₂, hl₂⟩ := runR_reads H _ rops₂ (Nat.le_refl _) hshape₂ q₁.vm t hr2
    rw [popeqAligns_length hrops₂] at hl₂
    rw [vm_eq] at hX₂; simp only [List.nil_append] at hX₂
    cases hf : finish q₁ t with
    | none =>
      simp only [Option.bind_some, hf, Option.bind_none, Option.map_none]
      cases readBack (popeqAligns req₁) sb.reads <;> simp [query_eq, hr2, hf]
    | some x =>
      obtain ⟨rd, q₂⟩ := x
      have hrd : rd = t.reads := by
        unfold finish at hf; split at hf
        · split at hf
          · obtain ⟨_, _, h⟩ := Option.map_eq_some_iff.mp hf; simp at h; exact h.1.symm
          · simp at hf
        · simp at hf
      subst hrd
      simp only [Option.bind_some, hf, Option.map_some]
      by_cases hlen : (popeqAligns req₁).length = sb.reads.length
      · rw [readBack_append _ _ _ _ hlen]
        cases readBack (popeqAligns req₁) sb.reads with
        | none => rfl
        | some v₁ =>
          simp only [Option.bind_some, query_eq, hr2, hf]
          cases readBack (popeqAligns req₂) t.reads <;> simp
      · have hnone : readBack (popeqAligns req₁ ++ popeqAligns req₂) (sb.reads ++ t.reads) = none := by
          cases h : readBack (popeqAligns req₁ ++ popeqAligns req₂) (sb.reads ++ t.reads) with
          | none => rfl
          | some f =>
            have := readBack_length h
            simp only [List.length_append] at this
            rw [hX₂] at this
            omega
        have hnone₁ : readBack (popeqAligns req₁) sb.reads = none := by
          cases h : readBack (popeqAligns req₁) sb.reads with
          | none => rfl
          | some f => exact absurd (readBack_length h) hlen
        rw [hnone, hnone₁]; rfl

end Damp.Ledger
