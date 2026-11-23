/-
The kernel operations that write the transaction's effects
(`Damp/Lang/Ledger.lean`, namespace `Kernel`) against the VM model.

The effects are the second value of the VM stack (`QueryContext::to_vm_stack`):
an array of nine maps (`docs/ledger-model.md`), weak and fully cached. A
well-formed ledger state (`LedgerState.WF`) holds them as the runtime
re-encodes them (`decodeEffects`). The operations:

| operation | slot | entry written |
|---|---|---|
| `claimZswapNullifier n` | 0 | `n ↦ null` |
| `claimZswapCoinReceive cm` | 1 | `cm ↦ null` |
| `claimZswapCoinSpend cm` | 2 | `cm ↦ null` |
| `claimContractCall a e c` | 3 | `(size, a, e, c) ↦ null`, `size` the number of entries before |
| `mintShielded d k` | 4 | `d ↦ old + k` (`u64`) |
| `mintUnshielded d k` | 5 | `d ↦ old + k` (`u64`) |
| `incUnshieldedInputs t k` | 6 | `t ↦ old + k` (`u128`) |
| `incUnshieldedOutputs t k` | 7 | `t ↦ old + k` (`u128`) |
| `claimUnshieldedCoinSpend t r k` | 8 | `(t, r) ↦ old + k` (`u128`) |

Each theorem gives the oracle's answer on a well-formed state whose effects
are `.array es` with `es[slot]? = some (.map m)`: nothing is read, the
contract state and the call context are unchanged, and the effects become
`es.set slot (.map m')`, `m'` the map above, written with `assocSet` (an
existing entry for the key is replaced in place, a new one is added at the
end) and re-encoded as the runtime does. And when it fails:

* the claims (slots 0 to 2) never fail;
* `claimContractCall` fails only when the set already has `2^64` entries;
* the additions (slots 4 to 8, `addIn`) fail exactly when an entry for the key
  is present and the sum does not fit 64 bits: the VM adds with `u64`
  arithmetic (`vm.rs` `Add`), even for the `u128` amounts of slots 6 to 8; an
  absent entry is simply set to the amount, up to `2^128 - 1`;
* the unshielded operations (slots 6 to 8) fail when the key is not a
  well-formed `TokenType` (or `(TokenType, PublicAddress)`): an `Either` with
  both sides set, or the wrong side empty (`tokenTypeOk`, `publicAddressOk`),
  rejected by the runtime's typed decoding at the end of the query;
* an amount too wide for its alignment makes the request itself fail
  (`AV.ofFields`), as for every pushed value.

No hash or commitment is involved: the keys are whatever field elements the
circuit computed.
-/
import Damp.Proofs.Ledger.Kernel
import Damp.Proofs.Ledger.OptEffects
import Damp.Proofs.Ledger.Map

namespace Damp.Ledger
open Damp.IR Damp.Impact

set_option linter.unusedSimpArgs false

/-! ## Lists indexed by `zipIdx` -/

theorem mapM_zipIdx_set {α β : Type} (f : α × Nat → Option β) :
    ∀ (l : List α) (n i : Nat) (l' : List β) (x : α) (y : β),
      (l.zipIdx n).mapM f = some l' → i < l.length → f (x, n + i) = some y →
      ((l.set i x).zipIdx n).mapM f = some (l'.set i y)
  | [], _, _, _, _, _, _, hi, _ => by simp at hi
  | e :: es, n, i, l', x, y, h, hi, hx => by
      simp only [List.zipIdx_cons, List.mapM_cons] at h
      cases he : f (e, n) with
      | none => simp [he] at h
      | some e' =>
        cases hes : (es.zipIdx (n + 1)).mapM f with
        | none => simp [he, hes] at h
        | some es' =>
          simp [he, hes] at h
          subst h
          cases i with
          | zero =>
            simp only [Nat.add_zero] at hx
            simp [List.zipIdx_cons, List.mapM_cons, hx, hes]
          | succ j =>
            have hj : j < es.length := by simp at hi; omega
            have hx' : f (x, n + 1 + j) = some y := by rw [Nat.add_assoc, Nat.add_comm 1 j]; exact hx
            have ih := mapM_zipIdx_set f es (n + 1) j es' x y hes hj hx'
            simp [List.zipIdx_cons, List.mapM_cons, he, ih]

theorem mapM_zipIdx_set_none {α β : Type} (f : α × Nat → Option β) :
    ∀ (l : List α) (n i : Nat) (x : α),
      i < l.length → f (x, n + i) = none → ((l.set i x).zipIdx n).mapM f = none
  | [], _, _, _, hi, _ => by simp at hi
  | e :: es, n, i, x, hi, hx => by
      cases i with
      | zero =>
        simp only [Nat.add_zero] at hx
        simp [List.zipIdx_cons, List.mapM_cons, hx]
      | succ j =>
        have hj : j < es.length := by simp at hi; omega
        have hx' : f (x, n + 1 + j) = none := by rw [Nat.add_assoc, Nat.add_comm 1 j]; exact hx
        have ih := mapM_zipIdx_set_none f es (n + 1) j x hj hx'
        cases he : f (e, n) <;> simp [List.zipIdx_cons, List.mapM_cons, he, ih]

theorem mapM_zipIdx_get {α β : Type} (f : α × Nat → Option β) :
    ∀ (l : List α) (n i : Nat) (l' : List β) (x : α),
      (l.zipIdx n).mapM f = some l' → l[i]? = some x → ∃ y, f (x, n + i) = some y ∧ l'[i]? = some y
  | [], _, _, _, _, _, hx => by simp at hx
  | e :: es, n, i, l', x, h, hx => by
      simp only [List.zipIdx_cons, List.mapM_cons] at h
      cases he : f (e, n) with
      | none => simp [he] at h
      | some e' =>
        cases hes : (es.zipIdx (n + 1)).mapM f with
        | none => simp [he, hes] at h
        | some es' =>
          simp [he, hes] at h
          subst h
          cases i with
          | zero => simp at hx; subst hx; exact ⟨e', by simpa using he, rfl⟩
          | succ j =>
            simp at hx
            obtain ⟨y, hy, hy'⟩ := mapM_zipIdx_get f es (n + 1) j es' x hes hx
            refine ⟨y, ?_, by simpa using hy'⟩
            rw [show n + (j + 1) = n + 1 + j by omega]; exact hy

/-! ## The effects' decoding, one slot at a time -/

/-- The function `decodeEffects` maps over the slots. -/
def slotDecode (p : SV × Nat) : Option SV :=
  match p.1 with
  | .map m => (effectMap p.2 m).map SV.map
  | _ => none

theorem decodeEffects_array (es : List SV) :
    decodeEffects (.array es) = if es.length = 9 then ((es.zipIdx).mapM slotDecode).map SV.array else none := by
  simp only [decodeEffects]
  split
  · change Option.bind (List.mapM slotDecode es.zipIdx) (fun es' => some (SV.array es')) = _
    cases (List.mapM slotDecode es.zipIdx) <;> rfl
  · rfl

theorem effectMap_length_le (slot : Nat) : ∀ {m m' : List (AV × SV)}, effectMap slot m = some m' →
    m'.length ≤ m.length
  | [], m', h => by simp [effectMap] at h; subst h; simp
  | (k, v) :: rest, m', h => by
      simp only [effectMap] at h
      cases hr : effectMap slot rest with
      | none => simp [hr] at h
      | some r =>
        have ih := effectMap_length_le slot hr
        cases he : effectEntry slot k v with
        | none => simp [hr, he] at h
        | some e =>
          obtain ⟨k', v'⟩ := e
          simp only [hr, he, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
          split at h <;> (subst h; simp; omega)

/-- A map the decoding leaves unchanged, entry by entry: the rest is unchanged,
    the first entry is in its type's form, and its key does not occur again. -/
theorem effectMap_fixed_cons {slot : Nat} {k : AV} {v : SV} {rest : List (AV × SV)}
    (h : effectMap slot ((k, v) :: rest) = some ((k, v) :: rest)) :
    effectMap slot rest = some rest ∧ effectEntry slot k v = some (k, v) ∧ assocGet k rest = none := by
  simp only [effectMap] at h
  cases hr : effectMap slot rest with
  | none => simp [hr] at h
  | some r =>
    have hl := effectMap_length_le slot hr
    cases he : effectEntry slot k v with
    | none => simp [hr, he] at h
    | some e =>
      obtain ⟨k', v'⟩ := e
      simp only [hr, he, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
      split at h
      · subst h; simp at hl; omega
      · rename_i hg
        simp only [List.cons.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
        refine ⟨rfl, rfl, ?_⟩
        cases hk : assocGet k' r <;> simp_all

theorem effectMap_cons_of_fixed {slot : Nat} {k : AV} {v : SV} {rest : List (AV × SV)}
    (hr : effectMap slot rest = some rest) (he : effectEntry slot k v = some (k, v))
    (hg : assocGet k rest = none) : effectMap slot ((k, v) :: rest) = some ((k, v) :: rest) := by
  simp [effectMap, hr, he, hg]

/-- Setting an entry of a decoded map, with a key and value in their types'
    form, gives a decoded map. -/
theorem effectMap_assocSet {slot : Nat} {kv : AV} {v v' : SV} (he : effectEntry slot kv v = some (kv, v')) :
    ∀ {m : List (AV × SV)}, effectMap slot m = some m → effectMap slot (assocSet kv v m) = some (assocSet kv v' m)
  | [], _ => by simp [effectMap, assocSet, he, assocGet]
  | (k', w) :: rest, hm => by
      obtain ⟨hr, hew, hg⟩ := effectMap_fixed_cons hm
      by_cases hk : k' = kv
      · subst hk
        simp [assocSet, effectMap, hr, he, hg]
      · have ih := effectMap_assocSet he hr
        have hg' : assocGet k' (assocSet kv v' rest) = none := by
          rw [assocGet_assocSet_ne v' hk]; exact hg
        simp [assocSet, hk, effectMap, ih, hew, hg']

theorem mem_assocSet {κ ν : Type} [DecidableEq κ] (k : κ) (v : ν) :
    ∀ m : List (κ × ν), (k, v) ∈ assocSet k v m
  | [] => by simp [assocSet]
  | (k', v') :: rest => by
      by_cases h : k' = k
      · simp [assocSet, h]
      · simp [assocSet, h, mem_assocSet k v rest]

/-- In a decoded map, every entry is in its type's form. -/
theorem effectEntry_of_assocGet {slot : Nat} {k : AV} {v : SV} :
    ∀ {m : List (AV × SV)}, effectMap slot m = some m → assocGet k m = some v → effectEntry slot k v = some (k, v)
  | [], _, h => by simp [assocGet] at h
  | (k', w) :: rest, hm, h => by
      obtain ⟨hr, hew, _⟩ := effectMap_fixed_cons hm
      by_cases hk : k' = k
      · subst hk; simp [assocGet] at h; subst h; exact hew
      · simp [assocGet, hk] at h; exact effectEntry_of_assocGet hr h

/-- In well-formed effects, slot `i` (a map) is decoded. -/
theorem effectMap_of_wf {es : List SV} (hwf : decodeEffects (.array es) = some (.array es)) {i : Nat}
    {m : List (AV × SV)} (hi : es[i]? = some (.map m)) : effectMap i m = some m := by
  rw [decodeEffects_array] at hwf
  split at hwf
  · simp only [Option.map_eq_some_iff] at hwf
    obtain ⟨es', hm, hes⟩ := hwf
    cases hes
    obtain ⟨y, hy, hy'⟩ := mapM_zipIdx_get slotDecode es 0 i es (.map m) hm hi
    rw [hi] at hy'
    cases hy'
    simp only [slotDecode, Nat.zero_add, Option.map_eq_some_iff] at hy
    obtain ⟨m', hm', he⟩ := hy
    cases he
    exact hm'
  · simp at hwf

/-- The effects after setting an entry of slot `i`'s map: decoded as the same
    entry in its type's form. -/
theorem decodeEffects_set {es : List SV} (hwf : decodeEffects (.array es) = some (.array es)) {i : Nat}
    {m : List (AV × SV)} (hi : es[i]? = some (.map m)) {kv : AV} {v v' : SV}
    (he : effectEntry i kv v = some (kv, v')) :
    decodeEffects (.array (es.set i (.map (assocSet kv v m)))) = some (.array (es.set i (.map (assocSet kv v' m)))) := by
  have hm := effectMap_of_wf hwf hi
  rw [decodeEffects_array] at hwf ⊢
  have hlen : es.length = 9 := by split at hwf <;> simp_all
  simp only [hlen, ite_true, Option.map_eq_some_iff] at hwf
  obtain ⟨es', hmap, hes⟩ := hwf
  cases hes
  have hil : i < es.length := lt_of_getElem? hi
  have hs : slotDecode (.map (assocSet kv v m), 0 + i) = some (.map (assocSet kv v' m)) := by
    simp [slotDecode, effectMap_assocSet he hm]
  simp [List.length_set, hlen, mapM_zipIdx_set slotDecode es 0 i es _ _ hmap hil hs]

/-- Setting an entry whose key or value is not of the slot's type: the effects
    do not decode. -/
theorem decodeEffects_set_none {es : List SV} {i : Nat} (hil : i < es.length) (m : List (AV × SV)) {kv : AV} {v : SV}
    (he : effectEntry i kv v = none) :
    decodeEffects (.array (es.set i (.map (assocSet kv v m)))) = none := by
  rw [decodeEffects_array]
  split
  · have hs : slotDecode (.map (assocSet kv v m), 0 + i) = none := by
      simp [slotDecode, effectMap_none_of_mem i he _ (mem_assocSet kv v m)]
    simp [mapM_zipIdx_set_none slotDecode es 0 i _ hil hs]
  · rfl

/-! ## Claims: slots 0 to 3 hold sets -/

/-- The instructions of `claimIn i` with operands evaluated: bring the effects
    to the top, descend into slot `i`, insert `key ↦ null`, put them back. -/
def claimReq (i : Nat) (key : Aligned Fr) : List (Op Fr) :=
  [.swap 0, .idx true true [⟨[.bytes 1], [Fr.ofInt i]⟩], .push false key, .pushNull false, .ins true 2, .swap 0]

/-- What the VM does with `claimReq`: the entry `kv ↦ null` is set in slot
    `i`'s map, decoded as the runtime does; nothing else changes. -/
theorem claimReq_spec (H : Hooks) (σ : LedgerState) (es : List SV) (m : List (AV × SV)) (i : Nat)
    (key : Aligned Fr) (kv : AV) (hb : i < 256) (hwf : σ.WF) (heff : σ.effects = .array es)
    (hm : es[i]? = some (.map m)) (hkv : AV.ofAligned key = some kv) (hent : effectEntry i kv .null = some (kv, .null)) :
    ledgerOracle H (claimReq i key) σ = some ([], { σ with effects := .array (es.set i (.map (assocSet kv .null m))) }) := by
  have hkey := ofAligned_byteKey hb
  simp only [AV.ofAligned] at hkey hkv
  rw [LedgerState.WF, heff] at hwf
  have hdec := decodeEffects_set hwf hm hent
  have hi := lt_of_getElem? hm
  have hm' := getElem_of_getElem? hm
  obtain ⟨ctx, eff, st⟩ := σ
  simp only at heff ⊢
  subst heff
  vm_simp [claimReq, hb, hkey, hkv, hi, hm, hm', hdec, popeqAligns]

/-! ### Aligned values built from field elements -/

theorem ofFields_cons_inv {a : Zkir.AlignAtom} {as : List Zkir.AlignAtom} {vs : List Fr} {kv : AV}
    (h : AV.ofFields (a :: as) vs = some kv) :
    ∃ rest, AV.ofFields as (vs.drop (atomWidth a)) = some rest ∧
      atomFits a (atomOfFields a (vs.take (atomWidth a))) = true ∧
      kv = ⟨a :: rest.align, atomOfFields a (vs.take (atomWidth a)) :: rest.atoms⟩ := by
  simp only [AV.ofFields] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i h2
      cases hr : AV.ofFields as (vs.drop (atomWidth a)) with
      | none => simp [hr] at h
      | some rest =>
        simp [hr] at h
        exact ⟨rest, rfl, by simpa using h2, h.symm⟩

/-- A one-atom aligned value: its atom fits. -/
theorem ofFields_one {a : Zkir.AlignAtom} {vs : List Fr} {kv : AV} (h : AV.ofFields [a] vs = some kv) :
    ∃ x, atomFits a x = true ∧ kv = ⟨[a], [x]⟩ := by
  obtain ⟨rest, hr, hf, rfl⟩ := ofFields_cons_inv h
  simp [AV.ofFields] at hr
  subst hr
  exact ⟨_, hf, rfl⟩

theorem byteLen_le {x n : Nat} (h : x < 2 ^ (8 * n)) : byteLen x ≤ n := by
  unfold byteLen
  split
  · omega
  · rename_i hx
    have := (Nat.log2_lt hx).2 h
    omega

theorem atomSize_le_34 {x : Nat} (h : x < 2 ^ 256) : atomSize x ≤ 34 := by
  have hb : byteLen x ≤ 32 := byteLen_le (n := 32) h
  unfold atomSize
  split
  · rename_i h1; unfold flaggedIntSize; split <;> omega
  · unfold flaggedIntSize; split <;> (try split) <;> omega

theorem modulus_lt_2_256 : Fr.modulus < 2 ^ 256 := by decide

/-! ### The three Zswap claims -/

section
variable (H : Hooks) (p : Zkir.Prims) (env : Env) (σ : LedgerState) (es : List SV) (m : List (AV × SV))

theorem effectEntry_hash {i : Nat} (hi : i ≤ 2) {x : Nat} (hx : x < 2 ^ 256) :
    effectEntry i ⟨[.bytes 32], [x]⟩ .null = some (⟨[.bytes 32], [x]⟩, .null) := by
  have h3 : i ≤ 3 := by omega
  simp [effectEntry, effectValue, effectKey, h3, hi, AV.toHash, hx, AV.ofHash]

/-- A `Bytes 32` key as the VM stores it: one atom below `2^256`, aligned `bytes 32`. -/
theorem bytes32_key {ks : List Fr} {kv : AV} (hkv : AV.ofFields [.bytes 32] ks = some kv) :
    ∃ x, x < 2 ^ 256 ∧ kv = ⟨[.bytes 32], [x]⟩ := by
  obtain ⟨x, hf, rfl⟩ := ofFields_one hkv
  exact ⟨x, by simpa [atomFits] using hf, rfl⟩

private theorem claim_of {i : Nat} (hi : i ≤ 2) (n : Bytes 32) (ks : List Fr) (kv : AV)
    (hwf : σ.WF) (heff : σ.effects = .array es) (hm : es[i]? = some (.map m))
    (hk : Expr.evalList p env (Value.toExprs n) = some ks) (hkv : AV.ofFields [.bytes 32] ks = some kv) :
    ∃ req, (some [.swap 0, .idx true true [fieldKey i], .push false (alignedOf n), .pushNull false, .ins true 2,
        .swap 0] : Option (List (Op Expr))).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some ([], { σ with effects := .array (es.set i (.map (assocSet kv .null m))) }) := by
  rw [evalList_eq_mapM] at hk
  refine ⟨claimReq i ⟨[.bytes 32], ks⟩, ?_, ?_⟩
  · simp [Exec.request, Op.mapM, Aligned.mapM, Exec.blank, fieldKey, Expr.eval, claimReq, alignedOf, hk]
    rfl
  · obtain ⟨x, hx, rfl⟩ := bytes32_key hkv
    exact claimReq_spec H σ es m i _ _ (by omega) hwf heff hm hkv (effectEntry_hash hi hx)

/-- `Kernel.claimZswapNullifier n`: `n`'s atom is added to the nullifiers
    claimed (effects slot 0). Never fails; nothing is read; only the effects change. -/
theorem Kernel.claimZswapNullifier_spec (n : Bytes 32) (ks : List Fr) (kv : AV)
    (hwf : σ.WF) (heff : σ.effects = .array es) (hm : es[0]? = some (.map m))
    (hk : Expr.evalList p env (Value.toExprs n) = some ks) (hkv : AV.ofFields [.bytes 32] ks = some kv) :
    ∃ req, (emitted (Kernel.claimZswapNullifier n)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some ([], { σ with effects := .array (es.set 0 (.map (assocSet kv .null m))) }) :=
  claim_of H p env σ es m (by decide) n ks kv hwf heff hm hk hkv

/-- `Kernel.claimZswapCoinReceive cm`: `cm` is added to the coins received (slot 1). -/
theorem Kernel.claimZswapCoinReceive_spec (cm : Bytes 32) (ks : List Fr) (kv : AV)
    (hwf : σ.WF) (heff : σ.effects = .array es) (hm : es[1]? = some (.map m))
    (hk : Expr.evalList p env (Value.toExprs cm) = some ks) (hkv : AV.ofFields [.bytes 32] ks = some kv) :
    ∃ req, (emitted (Kernel.claimZswapCoinReceive cm)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some ([], { σ with effects := .array (es.set 1 (.map (assocSet kv .null m))) }) :=
  claim_of H p env σ es m (by decide) cm ks kv hwf heff hm hk hkv

/-- `Kernel.claimZswapCoinSpend cm`: `cm` is added to the coins spent (created) (slot 2). -/
theorem Kernel.claimZswapCoinSpend_spec (cm : Bytes 32) (ks : List Fr) (kv : AV)
    (hwf : σ.WF) (heff : σ.effects = .array es) (hm : es[2]? = some (.map m))
    (hk : Expr.evalList p env (Value.toExprs cm) = some ks) (hkv : AV.ofFields [.bytes 32] ks = some kv) :
    ∃ req, (emitted (Kernel.claimZswapCoinSpend cm)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some ([], { σ with effects := .array (es.set 2 (.map (assocSet kv .null m))) }) :=
  claim_of H p env σ es m (by decide) cm ks kv hwf heff hm hk hkv

end

/-! ### Claimed contract calls (slot 3) -/

/-- The triple a call's claim pushes, as the VM stores it: two 32-byte atoms
    and a field element. -/
theorem ofFields_callTriple {ks : List Fr} {kv : AV}
    (h : AV.ofFields [.bytes 32, .bytes 32, .field] ks = some kv) :
    ∃ a e c, a < 2 ^ 256 ∧ e < 2 ^ 256 ∧ c < Fr.modulus ∧ kv = ⟨[.bytes 32, .bytes 32, .field], [a, e, c]⟩ := by
  obtain ⟨r1, h1, f1, rfl⟩ := ofFields_cons_inv h
  obtain ⟨r2, h2, f2, rfl⟩ := ofFields_cons_inv h1
  obtain ⟨c, fc, rfl⟩ := ofFields_one h2
  refine ⟨_, _, _, by simpa [atomFits] using f1, by simpa [atomFits] using f2, ?_, rfl⟩
  -- the field atom is the value of a field element
  obtain ⟨r3, h3, _, hc⟩ := ofFields_cons_inv h2
  simp [AV.ofFields] at h3
  subst h3
  simp only [AV.mk.injEq, List.cons.injEq, and_true] at hc
  obtain ⟨-, rfl⟩ := hc
  simp only [atomOfFields]
  exact ((List.take (atomWidth .field) (List.drop (atomWidth (.bytes 32)) (List.drop (atomWidth (.bytes 32)) ks))).headD 0).isLt

/-- The instructions of `Kernel.claimContractCall`, operands evaluated. -/
def callClaimReq (triple : List Fr) : List (Op Fr) :=
  [.swap 0, .idx true true [⟨[.bytes 1], [Fr.ofInt 3]⟩], .dup 0, .size,
   .push false ⟨[.bytes 32, .bytes 32, .field], triple⟩, .concatCached 160, .pushNull false, .ins true 2, .swap 0]

theorem callClaimReq_spec (H : Hooks) (σ : LedgerState) (es : List SV) (m : List (AV × SV))
    (ks : List Fr) (kv : AV) (hwf : σ.WF) (heff : σ.effects = .array es) (hm : es[3]? = some (.map m))
    (hkv : AV.ofFields [.bytes 32, .bytes 32, .field] ks = some kv) :
    ledgerOracle H (callClaimReq ks) σ =
      if m.length < 2 ^ 64 then
        some ([], { σ with effects := .array (es.set 3 (.map (assocSet ⟨alignContractCall, m.length :: kv.atoms⟩ .null m))) })
      else none := by
  have hkey := ofFields_key3
  obtain ⟨a, e, c, ha, he, hc, rfl⟩ := ofFields_callTriple hkv
  rw [LedgerState.WF, heff] at hwf
  have hi := lt_of_getElem? hm
  have hm' := getElem_of_getElem? hm
  obtain ⟨ctx, eff, st⟩ := σ
  simp only at heff ⊢
  subst heff
  have hsa : AV.size ⟨[.bytes 32, .bytes 32, .field], [a, e, c]⟩ ≤ 109 := by
    have h1 := atomSize_le_34 ha
    have h2 := atomSize_le_34 he
    have h3 := atomSize_le_34 (Nat.lt_trans hc modulus_lt_2_256)
    simp [AV.size, flaggedIntSize, alignAtomSize]
    omega
  by_cases hl : m.length < 2 ^ 64
  · have hsb : AV.size (AV.ofU64 m.length) ≤ 10 := by
      have h1 : byteLen m.length ≤ 8 := byteLen_le (n := 8) hl
      have h2 : atomSize m.length ≤ 9 := by
        unfold atomSize; split
        · unfold flaggedIntSize; split <;> omega
        · unfold flaggedIntSize; split <;> (try split) <;> omega
      simp [AV.size, AV.ofU64, alignAtomSize, flaggedIntSize]
      omega
    have hsz : AV.size ⟨[.bytes 32, .bytes 32, .field], [a, e, c]⟩ + AV.size (AV.ofU64 m.length) ≤ 160 := by omega
    have hent : effectEntry 3 ⟨alignContractCall, [m.length, a, e, c]⟩ .null =
        some (⟨alignContractCall, [m.length, a, e, c]⟩, .null) := by
      simp [effectEntry, effectValue, effectKey, contractCallOk, hashOk, hl, ha, he, hc]
    have hdec := decodeEffects_set hwf hm hent
    simp only [alignContractCall] at hdec
    simp only [AV.ofU64] at hsz
    simp only [hl, ite_true]
    vm_simp [callClaimReq, hkey, hkv, hi, hm, hm', hdec, hsz, cellBound, alignContractCall, AV.ofU64]
  · simp only [hl, ite_false]
    have hent : effectEntry 3 ⟨alignContractCall, [m.length, a, e, c]⟩ .null = none := by
      simp [effectEntry, effectValue, effectKey, contractCallOk, hl]
    have hdec := decodeEffects_set_none (es := es) (i := 3) hi m hent
    simp only [alignContractCall] at hdec
    by_cases hsz : AV.size ⟨[.bytes 32, .bytes 32, .field], [a, e, c]⟩ + AV.size (AV.ofU64 m.length) ≤ 160
    · simp only [AV.ofU64] at hsz
      vm_simp [callClaimReq, hkey, hkv, hi, hm, hm', hdec, hsz, cellBound, alignContractCall, AV.ofU64]
    · simp only [AV.ofU64] at hsz
      vm_simp [callClaimReq, hkey, hkv, hi, hm, hm', hsz, cellBound, AV.ofU64]

/-- `Kernel.claimContractCall address entryPoint comm`: the claimed calls (effects
    slot 3) get the key `(n, address, entryPoint, comm)`, `n` the number of
    claims before (the sequence number), aligned as the runtime's
    `ClaimedContractCallsValue`; fails only when there are already `2^64`
    claims. Nothing is read; the contract state and context are unchanged. -/
theorem Kernel.claimContractCall_spec (H : Hooks) (p : Zkir.Prims) (env : Env) (σ : LedgerState)
    (es : List SV) (m : List (AV × SV)) (address : ContractAddress) (entryPoint : Bytes 32) (comm : Field)
    (ks : List Fr) (kv : AV) (hwf : σ.WF) (heff : σ.effects = .array es) (hm : es[3]? = some (.map m))
    (hk : Expr.evalList p env (address.bytes.limbs ++ entryPoint.limbs ++ [comm.expr]) = some ks)
    (hkv : AV.ofFields [.bytes 32, .bytes 32, .field] ks = some kv) :
    ∃ req, (emitted (Kernel.claimContractCall address entryPoint comm)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ =
        if m.length < 2 ^ 64 then
          some ([], { σ with effects := .array (es.set 3 (.map (assocSet ⟨alignContractCall, m.length :: kv.atoms⟩ .null m))) })
        else none := by
  rw [evalList_eq_mapM] at hk
  have he : emitted (Kernel.claimContractCall address entryPoint comm) = some [.swap 0, .idx true true [fieldKey 3],
      .dup 0, .size, .push false ⟨[.bytes 32, .bytes 32, .field], address.bytes.limbs ++ entryPoint.limbs ++ [comm.expr]⟩,
      .concatCached 160, .pushNull false, .ins true 2, .swap 0] := rfl
  refine ⟨callClaimReq ks, ?_, callClaimReq_spec H σ es m ks kv hwf heff hm hkv⟩
  rw [he]
  generalize address.bytes.limbs ++ entryPoint.limbs ++ [comm.expr] = vs at hk ⊢
  simp [Exec.request, Op.mapM, Aligned.mapM, Exec.blank, fieldKey, Expr.eval, callClaimReq, hk]

/-! ## Additions: slots 4 to 8 map keys to amounts -/

/-- The byte width the runtime re-encodes an amount of slot `slot` with:
    `u64` for the mints (4, 5), `u128` for the unshielded amounts (6 to 8). -/
def amountWidth (slot : Nat) : Nat := if slot = 4 ∨ slot = 5 then 8 else 16

/-- An amount as the runtime re-encodes it in slot `slot`. -/
def amountCell (slot x : Nat) : SV := .cell ⟨[.bytes (amountWidth slot)], [x]⟩

/-- The amount an effects map holds for `kv`: its one atom, 0 when absent. -/
def effAmount (m : List (AV × SV)) (kv : AV) : Nat :=
  match assocGet kv m with
  | some (.cell ⟨_, [x]⟩) => x
  | _ => 0

/-- The instructions of `addIn slot` with operands evaluated: if the map in
    slot `slot` has `key`, add the amount to its value (`u64` arithmetic),
    otherwise set it to the amount. -/
def addReq (slot : Nat) (key amt : Aligned Fr) : List (Op Fr) :=
  [.swap 0, .idx true true [⟨[.bytes 1], [Fr.ofInt slot]⟩], .push false key, .dup 1, .dup 1, .member,
   .push false amt, .swap 0, .neg, .branch 4, .dup 2, .dup 2, .idxStack [], .add, .ins true 2, .swap 0]

theorem effectEntry_amount {slot : Nat} (hs : 4 ≤ slot ∧ slot ≤ 8) {kv : AV} (hkey : effectKey slot kv = some kv)
    {x : Nat} (hx : x < 2 ^ (8 * amountWidth slot)) :
    effectEntry slot kv (amountCell slot x) = some (kv, amountCell slot x) := by
  have h3 : ¬ slot ≤ 3 := by omega
  unfold amountWidth at hx
  by_cases h45 : slot = 4 ∨ slot = 5
  · simp only [h45, ite_true] at hx
    simp [effectEntry, effectValue, amountCell, amountWidth, h3, h45, hkey, AV.toU64, hx, AV.ofU64]
  · simp only [h45, ite_false] at hx
    simp [effectEntry, effectValue, amountCell, amountWidth, h3, h45, hkey, AV.toU128, hx]

theorem effectEntry_u64 {slot : Nat} (hs : 4 ≤ slot ∧ slot ≤ 8) {kv : AV} (hkey : effectKey slot kv = some kv)
    {x : Nat} (hx : x < 2 ^ 64) :
    effectEntry slot kv (.cell (AV.ofU64 x)) = some (kv, amountCell slot x) := by
  have h3 : ¬ slot ≤ 3 := by omega
  by_cases h45 : slot = 4 ∨ slot = 5
  · simp [effectEntry, effectValue, amountCell, amountWidth, h3, h45, hkey, AV.toU64, hx, AV.ofU64]
  · have hx' : x < 2 ^ 128 := Nat.lt_trans hx (by decide)
    simp [effectEntry, effectValue, amountCell, amountWidth, h3, h45, hkey, AV.toU128, hx', AV.ofU64]

/-- A value of a decoded amount map is an amount in the slot's form. -/
theorem amount_of_entry {slot : Nat} (hs : 4 ≤ slot ∧ slot ≤ 8) {kv : AV} {v : SV}
    (h : effectEntry slot kv v = some (kv, v)) :
    ∃ x, x < 2 ^ (8 * amountWidth slot) ∧ v = amountCell slot x := by
  have h3 : ¬ slot ≤ 3 := by omega
  unfold effectEntry at h
  cases hv : effectValue slot v with
  | none => simp [hv] at h
  | some v' =>
    cases hk : effectKey slot kv with
    | none => simp [hv, hk] at h
    | some k' =>
      simp [hv, hk] at h
      obtain ⟨-, rfl⟩ := h
      unfold effectValue at hv
      simp only [h3, ite_false] at hv
      by_cases h45 : slot = 4 ∨ slot = 5
      · simp only [h45, ite_true] at hv
        cases v' with
        | null => simp at hv
        | cell c =>
          cases hc : c.toU64 with
          | none => simp [hc] at hv
          | some x =>
            simp [hc, AV.ofU64] at hv
            unfold AV.toU64 at hc
            split at hc
            · rename_i y hy
              by_cases hy64 : y < 2 ^ 64
              · simp [hy64] at hc; subst hc
                refine ⟨y, by simpa [amountWidth, h45] using hy64, ?_⟩
                obtain ⟨a, atoms⟩ := c; simp at hy hv; subst hy
                simp [amountCell, amountWidth, h45, hv]
              · simp [hy64] at hc
            · simp at hc
        | _ => simp at hv
      · simp only [h45, ite_false] at hv
        cases v' with
        | null => simp at hv
        | cell c =>
          cases hc : c.toU128 with
          | none => simp [hc] at hv
          | some x =>
            simp [hc] at hv
            unfold AV.toU128 at hc
            split at hc
            · rename_i y hy
              by_cases hy128 : y < 2 ^ 128
              · simp [hy128] at hc; subst hc
                refine ⟨y, by simpa [amountWidth, h45] using hy128, ?_⟩
                obtain ⟨a, atoms⟩ := c; simp at hy hv; subst hy
                simp [amountCell, amountWidth, h45, hv]
              · simp [hy128] at hc
            · simp at hc
        | _ => simp at hv

/-- What the VM does with `addReq`: on a well-formed state, with the key in
    its type's form (`effectKey slot kv = some kv`) and the amount `a` pushed
    with the slot's width, the entry for `kv` becomes `old + a` (`old` 0 when
    absent). It fails exactly when an entry is present and `old + a` does not
    fit 64 bits. -/
theorem addReq_spec (H : Hooks) (σ : LedgerState) (es : List SV) (m : List (AV × SV)) (slot : Nat)
    (hs : 4 ≤ slot ∧ slot ≤ 8) (key : Aligned Fr) (kv : AV) (a : Fr) (hwf : σ.WF) (heff : σ.effects = .array es)
    (hm : es[slot]? = some (.map m)) (hkv : AV.ofAligned key = some kv) (hkey : effectKey slot kv = some kv)
    (ha : a.val < 2 ^ (8 * amountWidth slot))
    (hamt : AV.ofFields [.bytes (amountWidth slot)] [a] = some ⟨[.bytes (amountWidth slot)], [a.val]⟩) :
    ledgerOracle H (addReq slot key ⟨[.bytes (amountWidth slot)], [a]⟩) σ =
      if (assocGet kv m).isNone ∨ effAmount m kv + a.val < 2 ^ 64 then
        some ([], { σ with
          effects := .array (es.set slot (.map (assocSet kv (amountCell slot (effAmount m kv + a.val)) m))) })
      else none := by
  have hb : slot < 256 := by omega
  have hslot := ofAligned_byteKey hb
  simp only [AV.ofAligned] at hslot hkv
  rw [LedgerState.WF, heff] at hwf
  have hmm := effectMap_of_wf hwf hm
  have hi := lt_of_getElem? hm
  have hm' := getElem_of_getElem? hm
  obtain ⟨ctx, eff, st⟩ := σ
  simp only at heff ⊢
  subst heff
  cases hg : assocGet kv m with
  | none =>
    have hent := effectEntry_amount hs hkey ha
    have hdec := decodeEffects_set hwf hm hent
    simp only [amountCell] at hdec
    simp only [effAmount, hg, Option.isNone_none, true_or, ite_true, Nat.zero_add]
    vm_simp [addReq, hb, hslot, hkv, hamt, hi, hm, hm', hg, hdec, amountCell, AV.ofBool, AV.toBool]
  | some v =>
    obtain ⟨x, hx, rfl⟩ := amount_of_entry hs (effectEntry_of_assocGet hmm hg)
    have hx' : effAmount m kv = x := by simp [effAmount, hg, amountCell]
    rw [hx']
    simp only [hg, Option.isNone_some, false_or]
    by_cases hsum : x + a.val < 2 ^ 64
    · have hx64 : x < 2 ^ 64 := by omega
      have ha64 : a.val < 2 ^ 64 := by omega
      have hent := effectEntry_u64 hs hkey hsum
      have hdec := decodeEffects_set hwf hm hent
      simp only [amountCell, AV.ofU64] at hdec
      simp only [hsum, ite_true]
      vm_simp [addReq, hb, hslot, hkv, hamt, hi, hm, hm', hg, hdec, amountCell, AV.ofBool, AV.toBool, hx64, ha64, hsum,
        AV.ofU64]
    · simp only [hsum, ite_false]
      by_cases hx64 : x < 2 ^ 64
      · by_cases ha64 : a.val < 2 ^ 64
        · vm_simp [addReq, hb, hslot, hkv, hamt, hi, hm, hm', hg, amountCell, AV.ofBool, AV.toBool, hsum, AV.ofU64,
            hx64, ha64]
        · vm_simp [addReq, hb, hslot, hkv, hamt, hi, hm, hm', hg, amountCell, AV.ofBool, AV.toBool, AV.ofU64,
            hx64, ha64]
      · vm_simp [addReq, hb, hslot, hkv, hamt, hi, hm, hm', hg, amountCell, AV.ofBool, AV.toBool, AV.ofU64, hx64]

/-- `addReq` with a key that is not of the slot's type (for slots 6 to 8, a
    `TokenType` or `PublicAddress` the runtime rejects): the query fails when
    the effects are decoded. -/
theorem addReq_badKey (H : Hooks) (σ : LedgerState) (es : List SV) (m : List (AV × SV)) (slot : Nat)
    (hs : 4 ≤ slot ∧ slot ≤ 8) (key : Aligned Fr) (kv : AV) (a : Fr) (hwf : σ.WF) (heff : σ.effects = .array es)
    (hm : es[slot]? = some (.map m)) (hkv : AV.ofAligned key = some kv) (hkey : effectKey slot kv = none)
    (hamt : AV.ofFields [.bytes (amountWidth slot)] [a] = some ⟨[.bytes (amountWidth slot)], [a.val]⟩) :
    ledgerOracle H (addReq slot key ⟨[.bytes (amountWidth slot)], [a]⟩) σ = none := by
  have hb : slot < 256 := by omega
  have hslot := ofAligned_byteKey hb
  simp only [AV.ofAligned] at hslot hkv
  rw [LedgerState.WF, heff] at hwf
  have hmm := effectMap_of_wf hwf hm
  have hi := lt_of_getElem? hm
  have hm' := getElem_of_getElem? hm
  have hg : assocGet kv m = none := by
    cases hg : assocGet kv m with
    | none => rfl
    | some v =>
      have := effectEntry_of_assocGet hmm hg
      simp [effectEntry, hkey] at this
  have hent : effectEntry slot kv (.cell ⟨[.bytes (amountWidth slot)], [a.val]⟩) = none := by
    simp [effectEntry, hkey]
  have hdec := decodeEffects_set_none (es := es) hi m hent
  obtain ⟨ctx, eff, st⟩ := σ
  simp only at heff ⊢
  subst heff
  vm_simp [addReq, hb, hslot, hkv, hamt, hi, hm, hm', hg, hdec, AV.ofBool, AV.toBool]

theorem ofFields_align : ∀ {al : List Zkir.AlignAtom} {vs : List Fr} {kv : AV}, AV.ofFields al vs = some kv →
    kv.align = al ∧ kv.atoms.length = al.length
  | [], vs, kv, h => by simp [AV.ofFields] at h; subst h; simp
  | a :: as, vs, kv, h => by
      obtain ⟨rest, hr, _, rfl⟩ := ofFields_cons_inv h
      have := ofFields_align hr
      simp [this.1, this.2]

/-- A `TokenType` key (slots 6, 7) as Damp writes it: in the runtime's form
    exactly when its atoms are a well-formed `TokenType`. -/
theorem effectKey_tokenType {slot : Nat} (hs : slot = 6 ∨ slot = 7) {ks : List Fr} {kv : AV}
    (hkv : AV.ofFields alignTokenType ks = some kv) :
    effectKey slot kv = if tokenTypeOk kv.atoms then some kv else none := by
  have ha := (ofFields_align hkv).1
  have h1 : ¬ (slot ≤ 2 ∨ slot = 4 ∨ slot = 5) := by omega
  have h3 : slot ≠ 3 := by omega
  obtain ⟨al, atoms⟩ := kv
  simp only at ha
  subst ha
  simp [effectKey, h1, h3, hs]

/-- A `(TokenType, PublicAddress)` key (slot 8): in the runtime's form exactly
    when both halves are well formed. -/
theorem effectKey_spend {ks : List Fr} {kv : AV}
    (hkv : AV.ofFields (alignTokenType ++ alignPublicAddress) ks = some kv) :
    effectKey 8 kv = if spendKeyOk kv.atoms then some kv else none := by
  have ha := (ofFields_align hkv).1
  obtain ⟨al, atoms⟩ := kv
  simp only at ha
  subst ha
  simp [effectKey]

/-! ### The operations -/

section
variable (H : Hooks) (p : Zkir.Prims) (env : Env) (σ : LedgerState) (es : List SV) (m : List (AV × SV))

private theorem add_req {α : Type} [Value α] (slot w : Nat) (key : α) (amt : Expr) (ks : List Fr) (a : Fr)
    (hk : Expr.evalList p env (Value.toExprs key) = some ks) (ha : Expr.eval p env amt = some a) :
    (some [.swap 0, .idx true true [fieldKey slot], .push false (alignedOf key), .dup 1, .dup 1, .member,
        .push false ⟨[.bytes w], [amt]⟩, .swap 0, .neg, .branch 4, .dup 2, .dup 2, .idxStack [], .add, .ins true 2,
        .swap 0] : Option (List (Op Expr))).bind (Exec.request p env) =
      some (addReq slot ⟨alignOf α, ks⟩ ⟨[.bytes w], [a]⟩) := by
  rw [evalList_eq_mapM] at hk
  simp [Exec.request, Op.mapM, Aligned.mapM, Exec.blank, fieldKey, Expr.eval, addReq, alignedOf, hk, ha]

theorem ofFields_u64 {a : Fr} (h : a.val < 2 ^ 64) : AV.ofFields [.bytes 8] [a] = some ⟨[.bytes 8], [a.val]⟩ := by
  simp [AV.ofFields, atomWidth, atomOfFields, atomFits, h]

theorem ofFields_u128 {a : Fr} (h : a.val < 2 ^ 128) : AV.ofFields [.bytes 16] [a] = some ⟨[.bytes 16], [a.val]⟩ := by
  simp [AV.ofFields, atomWidth, atomOfFields, atomFits, h]

/-- The amount pushed by an addition that does not fit its width: the request fails. -/
theorem addReq_wide (slot : Nat) (key : Aligned Fr) (w : Nat) (a : Fr) (h : AV.ofFields [.bytes w] [a] = none) :
    ledgerOracle H (addReq slot key ⟨[.bytes w], [a]⟩) σ = none :=
  ledgerOracle_of_toR_none H (o := .push false ⟨[.bytes w], [a]⟩) (by simp [addReq])
    (by simp [Op.toR, AV.ofAligned, h]) σ

/-- `Kernel.mintShielded d amount`: the shielded mints (effects slot 4) map `d`
    to its previous amount (0 if none) plus `amount`; fails exactly when `d`
    was already minted and the sum does not fit 64 bits. -/
theorem Kernel.mintShielded_spec (d : Bytes 32) (amount : Uint64) (ks : List Fr) (kv : AV) (a : Fr)
    (hwf : σ.WF) (heff : σ.effects = .array es) (hm : es[4]? = some (.map m))
    (hk : Expr.evalList p env (Value.toExprs d) = some ks) (hkv : AV.ofFields [.bytes 32] ks = some kv)
    (ha : Expr.eval p env amount.expr = some a) (ha64 : a.val < 2 ^ 64) :
    ∃ req, (emitted (Kernel.mintShielded d amount)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ =
        if (assocGet kv m).isNone ∨ effAmount m kv + a.val < 2 ^ 64 then
          some ([], { σ with effects := .array (es.set 4 (.map (assocSet kv (amountCell 4 (effAmount m kv + a.val)) m))) })
        else none := by
  refine ⟨_, add_req p env 4 8 d amount.expr ks a hk ha, ?_⟩
  obtain ⟨x, hx, rfl⟩ := bytes32_key hkv
  exact addReq_spec H σ es m 4 (by decide) _ _ a hwf heff hm hkv
    (by simp [effectKey, AV.toHash, hx, AV.ofHash]) (by simpa [amountWidth] using ha64) (ofFields_u64 ha64)

/-- `Kernel.mintUnshielded d amount`: as `mintShielded`, in slot 5. -/
theorem Kernel.mintUnshielded_spec (d : Bytes 32) (amount : Uint64) (ks : List Fr) (kv : AV) (a : Fr)
    (hwf : σ.WF) (heff : σ.effects = .array es) (hm : es[5]? = some (.map m))
    (hk : Expr.evalList p env (Value.toExprs d) = some ks) (hkv : AV.ofFields [.bytes 32] ks = some kv)
    (ha : Expr.eval p env amount.expr = some a) (ha64 : a.val < 2 ^ 64) :
    ∃ req, (emitted (Kernel.mintUnshielded d amount)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ =
        if (assocGet kv m).isNone ∨ effAmount m kv + a.val < 2 ^ 64 then
          some ([], { σ with effects := .array (es.set 5 (.map (assocSet kv (amountCell 5 (effAmount m kv + a.val)) m))) })
        else none := by
  refine ⟨_, add_req p env 5 8 d amount.expr ks a hk ha, ?_⟩
  obtain ⟨x, hx, rfl⟩ := bytes32_key hkv
  exact addReq_spec H σ es m 5 (by decide) _ _ a hwf heff hm hkv
    (by simp [effectKey, AV.toHash, hx, AV.ofHash]) (by simpa [amountWidth] using ha64) (ofFields_u64 ha64)

/-- `Kernel.incUnshieldedInputs t amount` (slot 6), with `t` a well-formed
    `TokenType`: `t`'s amount becomes `old + amount`. An absent entry takes
    any `u128` amount; a present one fails unless the sum fits 64 bits (the
    VM's `add` is `u64`). -/
theorem Kernel.incUnshieldedInputs_spec (t : TokenType) (amount : Uint128) (ks : List Fr) (kv : AV) (a : Fr)
    (hwf : σ.WF) (heff : σ.effects = .array es) (hm : es[6]? = some (.map m))
    (hk : Expr.evalList p env (Value.toExprs t) = some ks) (hkv : AV.ofFields alignTokenType ks = some kv)
    (hok : tokenTypeOk kv.atoms) (ha : Expr.eval p env amount.expr = some a) (ha128 : a.val < 2 ^ 128) :
    ∃ req, (emitted (Kernel.incUnshieldedInputs t amount)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ =
        if (assocGet kv m).isNone ∨ effAmount m kv + a.val < 2 ^ 64 then
          some ([], { σ with effects := .array (es.set 6 (.map (assocSet kv (amountCell 6 (effAmount m kv + a.val)) m))) })
        else none := by
  refine ⟨_, add_req p env 6 16 t amount.expr ks a hk ha, ?_⟩
  exact addReq_spec H σ es m 6 (by decide) _ _ a hwf heff hm hkv
    (by rw [effectKey_tokenType (by decide) hkv]; simp [hok]) (by simpa [amountWidth] using ha128) (ofFields_u128 ha128)

/-- `Kernel.incUnshieldedOutputs t amount`: as `incUnshieldedInputs`, in slot 7. -/
theorem Kernel.incUnshieldedOutputs_spec (t : TokenType) (amount : Uint128) (ks : List Fr) (kv : AV) (a : Fr)
    (hwf : σ.WF) (heff : σ.effects = .array es) (hm : es[7]? = some (.map m))
    (hk : Expr.evalList p env (Value.toExprs t) = some ks) (hkv : AV.ofFields alignTokenType ks = some kv)
    (hok : tokenTypeOk kv.atoms) (ha : Expr.eval p env amount.expr = some a) (ha128 : a.val < 2 ^ 128) :
    ∃ req, (emitted (Kernel.incUnshieldedOutputs t amount)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ =
        if (assocGet kv m).isNone ∨ effAmount m kv + a.val < 2 ^ 64 then
          some ([], { σ with effects := .array (es.set 7 (.map (assocSet kv (amountCell 7 (effAmount m kv + a.val)) m))) })
        else none := by
  refine ⟨_, add_req p env 7 16 t amount.expr ks a hk ha, ?_⟩
  exact addReq_spec H σ es m 7 (by decide) _ _ a hwf heff hm hkv
    (by rw [effectKey_tokenType (by decide) hkv]; simp [hok]) (by simpa [amountWidth] using ha128) (ofFields_u128 ha128)

/-- `Kernel.claimUnshieldedCoinSpend t r amount` (slot 8), keyed by the six
    atoms of `(t, r)`, both well formed (`spendKeyOk`): as the other additions. -/
theorem Kernel.claimUnshieldedCoinSpend_spec (t : TokenType) (r : Either ContractAddress UserAddress)
    (amount : Uint128) (ks : List Fr) (kv : AV) (a : Fr)
    (hwf : σ.WF) (heff : σ.effects = .array es) (hm : es[8]? = some (.map m))
    (hk : Expr.evalList p env (Value.toExprs (t, r)) = some ks)
    (hkv : AV.ofFields (alignTokenType ++ alignPublicAddress) ks = some kv)
    (hok : spendKeyOk kv.atoms) (ha : Expr.eval p env amount.expr = some a) (ha128 : a.val < 2 ^ 128) :
    ∃ req, (emitted (Kernel.claimUnshieldedCoinSpend t r amount)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ =
        if (assocGet kv m).isNone ∨ effAmount m kv + a.val < 2 ^ 64 then
          some ([], { σ with effects := .array (es.set 8 (.map (assocSet kv (amountCell 8 (effAmount m kv + a.val)) m))) })
        else none := by
  refine ⟨_, add_req p env 8 16 (t, r) amount.expr ks a hk ha, ?_⟩
  exact addReq_spec H σ es m 8 (by decide) _ _ a hwf heff hm hkv
    (by rw [effectKey_spend hkv]; simp [hok]) (by simpa [amountWidth] using ha128) (ofFields_u128 ha128)

/-- The unshielded additions with a malformed key fail: `incUnshieldedInputs`
    with a `TokenType` that is not well formed (e.g. an `Either` with both sides
    set). Likewise for slots 7 and 8 (`addReq_badKey`). -/
theorem Kernel.incUnshieldedInputs_badKey (t : TokenType) (amount : Uint128) (ks : List Fr) (kv : AV) (a : Fr)
    (hwf : σ.WF) (heff : σ.effects = .array es) (hm : es[6]? = some (.map m))
    (hk : Expr.evalList p env (Value.toExprs t) = some ks) (hkv : AV.ofFields alignTokenType ks = some kv)
    (hok : tokenTypeOk kv.atoms = false) (ha : Expr.eval p env amount.expr = some a) (ha128 : a.val < 2 ^ 128) :
    ∃ req, (emitted (Kernel.incUnshieldedInputs t amount)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = none := by
  refine ⟨_, add_req p env 6 16 t amount.expr ks a hk ha, ?_⟩
  exact addReq_badKey H σ es m 6 (by decide) _ _ a hwf heff hm hkv
    (by rw [effectKey_tokenType (by decide) hkv]; simp [hok]) (ofFields_u128 ha128)

theorem Kernel.incUnshieldedOutputs_badKey (t : TokenType) (amount : Uint128) (ks : List Fr) (kv : AV) (a : Fr)
    (hwf : σ.WF) (heff : σ.effects = .array es) (hm : es[7]? = some (.map m))
    (hk : Expr.evalList p env (Value.toExprs t) = some ks) (hkv : AV.ofFields alignTokenType ks = some kv)
    (hok : tokenTypeOk kv.atoms = false) (ha : Expr.eval p env amount.expr = some a) (ha128 : a.val < 2 ^ 128) :
    ∃ req, (emitted (Kernel.incUnshieldedOutputs t amount)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = none := by
  refine ⟨_, add_req p env 7 16 t amount.expr ks a hk ha, ?_⟩
  exact addReq_badKey H σ es m 7 (by decide) _ _ a hwf heff hm hkv
    (by rw [effectKey_tokenType (by decide) hkv]; simp [hok]) (ofFields_u128 ha128)

theorem Kernel.claimUnshieldedCoinSpend_badKey (t : TokenType) (r : Either ContractAddress UserAddress)
    (amount : Uint128) (ks : List Fr) (kv : AV) (a : Fr)
    (hwf : σ.WF) (heff : σ.effects = .array es) (hm : es[8]? = some (.map m))
    (hk : Expr.evalList p env (Value.toExprs (t, r)) = some ks)
    (hkv : AV.ofFields (alignTokenType ++ alignPublicAddress) ks = some kv)
    (hok : spendKeyOk kv.atoms = false) (ha : Expr.eval p env amount.expr = some a) (ha128 : a.val < 2 ^ 128) :
    ∃ req, (emitted (Kernel.claimUnshieldedCoinSpend t r amount)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = none := by
  refine ⟨_, add_req p env 8 16 (t, r) amount.expr ks a hk ha, ?_⟩
  exact addReq_badKey H σ es m 8 (by decide) _ _ a hwf heff hm hkv
    (by rw [effectKey_spend hkv]; simp [hok]) (ofFields_u128 ha128)

end

/-- `Kernel.checkpoint` (`ckpt`): nothing is read and nothing changes. -/
theorem Kernel.checkpoint_spec (H : Hooks) (p : Zkir.Prims) (env : Env) (σ : LedgerState) (hwf : σ.WF) :
    ∃ req, (emitted Kernel.checkpoint).bind (Exec.request p env) = some req ∧ ledgerOracle H req σ = some ([], σ) := by
  refine ⟨[.ckpt], rfl, ?_⟩
  rw [LedgerState.WF] at hwf
  obtain ⟨ctx, eff, st⟩ := σ
  simp only at hwf ⊢
  vm_simp [hwf]

end Damp.Ledger
