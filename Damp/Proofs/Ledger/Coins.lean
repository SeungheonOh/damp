/-
The coin-storing operations (`Damp/Lang/Tokens.lean`: `Cell.writeCoin`,
`Map.insertCoin`, `Set.insertCoin`, `LedgerList.pushFrontCoin`) against the VM
model.

Each pushes the commitment of the coin it stores (`coinCommitment coin
recipient`, the 32-byte atom `cmv`), looks it up in the call context's
commitment indices (context slot 1, a map from commitments to `u64` Merkle-tree
indices that `createZswapOutput` fills in: `idx cached [{1: 1}, stack]`), and
appends what it finds to the coin (`concat cached 91`): the qualified coin
`(nonce, color, value, mt_index)` the field then stores.

`qualifyAV cv idx cmv` is that qualified coin, for the coin `cv` as the VM
holds it and the index map `idx`:

* the commitment absent (or not mapped to a cell): `none`, the request fails
  (the VM indexes to null and `concat` needs a cell);
* present, mapped to the cell `w`: `⟨cv.align ++ w.align, cv.atoms ++ w.atoms⟩`,
  provided the two serialized sizes add up to at most 91 bytes; otherwise the
  request fails. The runtime agrees (`test/vm.sh`, "synthetic coin storage"):
  a coin with 32-byte nonce and color and a value of `2^64` or more cannot be
  stored with an index of `2^32` or more ("exceeded structure bounds"), and the
  maximum value cannot be stored at all. compactc emits the same bound.

`qualifyAV_index`: for an index `n < 2^64` stored as the runtime stores it
(`AV.ofU64 n`), the qualified coin is exactly what `AV.ofFields` makes of the
coin's field elements followed by `n` under `QualifiedShieldedCoinInfo`'s
alignment, i.e. what `Cell.write` of the qualified coin would store.

Nothing is read, and only the contract state changes (the effects and the
context are as they were).
-/
import Damp.Proofs.Ledger.TokensRuns
import Damp.Proofs.Ledger.List

namespace Damp.Ledger
open Damp.IR Damp.Impact

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-- The qualified coin `concat cached 91` builds from the coin `cv` and the
    entry of the commitment index map `idx` for the commitment `cmv`; `none`
    when there is no such entry or the result is over the bound. -/
def qualifyAV (cv : AV) (idx : List (AV × SV)) (cmv : AV) : Option AV :=
  match assocGet cmv idx with
  | some (.cell w) => if w.size + cv.size ≤ 91 then some ⟨cv.align ++ w.align, cv.atoms ++ w.atoms⟩ else none
  | _ => none

theorem qualifyAV_absent {cv : AV} {idx : List (AV × SV)} {cmv : AV} (h : assocGet cmv idx = none) :
    qualifyAV cv idx cmv = none := by
  simp [qualifyAV, h]

/-- `AV.ofFields` of two alignments one after the other, when the first takes
    exactly its field elements. -/
theorem ofFields_append : ∀ (as : List Zkir.AlignAtom) (fs gs : List Fr) (v : AV) (bs : List Zkir.AlignAtom),
    AV.ofFields as fs = some v → fs.length = (as.map atomWidth).sum →
    AV.ofFields (as ++ bs) (fs ++ gs) = (AV.ofFields bs gs).map fun r => ⟨v.align ++ r.align, v.atoms ++ r.atoms⟩
  | [], fs, gs, v, bs, h, hl => by
      have : fs = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
      subst this
      simp [AV.ofFields] at h; subst h
      simp only [List.nil_append]
      cases AV.ofFields bs gs <;> rfl
  | a :: as, fs, gs, v, bs, h, hl => by
      simp only [List.map_cons, List.sum_cons] at hl
      have hw : atomWidth a ≤ fs.length := by omega
      simp only [AV.ofFields] at h
      split at h
      · omega
      split at h
      · simp at h
      rename_i h1 h2
      cases hr : AV.ofFields as (fs.drop (atomWidth a)) with
      | none => simp [hr] at h
      | some r =>
        simp only [hr, Option.bind_eq_bind, Option.bind_some] at h
        obtain rfl := Option.some.inj h
        have ih := ofFields_append as (fs.drop (atomWidth a)) gs r bs hr (by simp; omega)
        have ht : (fs ++ gs).take (atomWidth a) = fs.take (atomWidth a) := List.take_append_of_le_length hw
        have hd : (fs ++ gs).drop (atomWidth a) = fs.drop (atomWidth a) ++ gs := List.drop_append_of_le_length hw
        simp only [List.cons_append, AV.ofFields, List.length_append, ht, hd, ih]
        have : ¬ (fs.length + gs.length < atomWidth a) := by omega
        simp only [this, ↓reduceIte, h2]
        cases AV.ofFields bs gs <;> simp

theorem length_coinFs {coinFs : List Fr} {cv : AV} (h : AV.ofFields (alignOf ShieldedCoinInfo) coinFs = some cv) :
    5 ≤ coinFs.length := by
  simp only [show alignOf ShieldedCoinInfo = [.bytes 32, .bytes 32, .bytes 16] from rfl, AV.ofFields] at h
  split at h
  · simp at h
  rename_i h1
  simp only [atomWidth] at h1
  split at h
  · simp at h
  simp only [atomWidth, List.length_drop] at h
  split at h
  · simp at h
  rename_i h3
  split at h
  · simp at h
  split at h
  · simp at h
  rename_i h5
  simp at h1 h3 h5
  omega

/-- **The qualified coin, for an index stored as the runtime stores it** (a
    `u64` cell): exactly what `AV.ofFields` makes of the coin's field elements
    followed by the index, under `QualifiedShieldedCoinInfo`'s alignment, if it
    fits the bound. -/
theorem qualifyAV_index {coinFs : List Fr} {cv : AV} {idx : List (AV × SV)} {cmv : AV} {n : Nat}
    (hcv : AV.ofFields (alignOf ShieldedCoinInfo) coinFs = some cv) (hlen : coinFs.length = 5)
    (hn : n < 2 ^ 64) (hq : assocGet cmv idx = some (.cell (AV.ofU64 n))) :
    qualifyAV cv idx cmv =
      if (AV.ofU64 n).size + cv.size ≤ 91 then AV.ofFields (alignOf QualifiedShieldedCoinInfo) (coinFs ++ [Fr.ofNat n])
      else none := by
  have hm : n < Fr.modulus := Nat.lt_trans hn modulus_gt_2_64
  have h8 : AV.ofFields [.bytes 8] [Fr.ofNat n] = some (AV.ofU64 n) := by
    simp [AV.ofFields, atomWidth, atomOfFields, atomFits, AV.ofU64, Fr.val_ofNat_of_lt hm]; omega
  have ha : alignOf QualifiedShieldedCoinInfo = alignOf ShieldedCoinInfo ++ [.bytes 8] := rfl
  rw [ha, ofFields_append _ coinFs [Fr.ofNat n] cv [.bytes 8] hcv (by rw [hlen]; rfl), h8]
  by_cases hs : (AV.ofU64 n).size + cv.size ≤ 91 <;> simp [qualifyAV, hq, hs] <;> simp_all [AV.ofU64]

/-- The coin's commitment, as the operations push it. -/
theorem alignOf_bytes32 : alignOf (Bytes 32) = [.bytes 32] := rfl
theorem alignOf_coin : alignOf ShieldedCoinInfo = [.bytes 32, .bytes 32, .bytes 16] := rfl
theorem alignOf_qcoin : alignOf QualifiedShieldedCoinInfo = [.bytes 32, .bytes 32, .bytes 16, .bytes 8] := rfl

section
variable (H : Hooks) (p : Zkir.Prims) (env : Env) (σ : LedgerState) (fields : List SV)
  (cfs : List SV) (idx : List (AV × SV)) (coin : ShieldedCoinInfo)
  (recipient : Either ZswapCoinPublicKey ContractAddress) (coinFs cmFs : List Fr) (cv cmv : AV)

/-- The instructions of `CoinStore.qualify depth coin recipient`. -/
theorem qualify_eq (depth : Nat) :
    CoinStore.qualify depth coin recipient = [.dup depth,
      .push false ⟨alignOf (Bytes 32), Value.toExprs (coinCommitment coin recipient)⟩, .idxStack [fieldKey 1],
      .push false ⟨alignOf ShieldedCoinInfo, Value.toExprs coin⟩, .swap 0, .concatCached 91] := rfl

/-- The evaluated instructions of `qualify`. -/
def qualifyReq (depth : Nat) (cmFs coinFs : List Fr) : List (Op Fr) :=
  [.dup depth, .push false ⟨[.bytes 32], cmFs⟩, .idxStack [⟨[.bytes 1], [Fr.ofInt 1]⟩],
   .push false ⟨[.bytes 32, .bytes 32, .bytes 16], coinFs⟩, .swap 0, .concatCached 91]

/-- **`Cell.writeCoin coin recipient`**: field `c.index` becomes the cell of the
    qualified coin (`qualifyAV`), or the request fails when the commitment has
    no index or the qualified coin is over the bound. Nothing is read. -/
theorem Cell.writeCoin_spec (c : Cell QualifiedShieldedCoinInfo)
    (hst : σ.state = .array fields) (hi : c.index < fields.length) (hb : c.index < 256) (hwf : σ.WF)
    (hctx : σ.context = .array cfs) (hidx : cfs[1]? = some (.map idx))
    (hcoin : Expr.evalList p env (Value.toExprs coin) = some coinFs)
    (hcv : AV.ofFields (alignOf ShieldedCoinInfo) coinFs = some cv)
    (hcm : Expr.evalList p env (Value.toExprs (coinCommitment coin recipient)) = some cmFs)
    (hcmv : AV.ofFields [.bytes 32] cmFs = some cmv) :
    ∃ req, (emitted (c.writeCoin coin recipient)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = (qualifyAV cv idx cmv).map fun q => ([], σ.setField c.index (.cell q)) := by
  have he : emitted (c.writeCoin coin recipient) = some ([.push false (fieldKey c.index)] ++
      CoinStore.qualify 3 coin recipient ++ [.ins false 1]) := rfl
  rw [he, qualify_eq]
  rw [evalList_eq_mapM] at hcoin hcm
  refine ⟨[.push false ⟨[.bytes 1], [Fr.ofInt c.index]⟩] ++ qualifyReq 3 cmFs coinFs ++ [.ins false 1], ?_, ?_⟩
  · simp [Exec.request, Op.mapM, Aligned.mapM, hcoin, hcm, Exec.blank, fieldKey, Expr.eval, qualifyReq,
      alignOf_bytes32, alignOf_coin]
  · have hk := ofAligned_byteKey hb
    have hk1 := ofFields_key1
    simp only [AV.ofAligned] at hk
    rw [LedgerState.WF] at hwf
    rw [alignOf_coin] at hcv
    obtain ⟨ctx, eff, st⟩ := σ
    simp only at hst hwf hctx ⊢
    subst hst hctx
    cases hq : assocGet cmv idx with
    | none =>
      vm_simp [qualifyReq, hb, hk, hk1, hwf, hi, hidx, hcv, hcmv, hq, qualifyAV, LedgerState.setField]
    | some v =>
      cases v with
      | cell w =>
        by_cases hsz : w.size + cv.size ≤ 91
        · vm_simp [qualifyReq, hb, hk, hk1, hwf, hi, hidx, hcv, hcmv, hq, qualifyAV, hsz, cellBound,
            LedgerState.setField]
        · vm_simp [qualifyReq, hb, hk, hk1, hwf, hi, hidx, hcv, hcmv, hq, qualifyAV, hsz, cellBound,
            LedgerState.setField]
      | _ => vm_simp [qualifyReq, hb, hk, hk1, hwf, hi, hidx, hcv, hcmv, hq, qualifyAV, LedgerState.setField]

/-- **`Map.insertCoin k coin recipient`** on a top-level map: the entry for
    `kv` becomes the cell of the qualified coin (replacing any entry for `kv`),
    or the request fails as for `Cell.writeCoin`. -/
theorem Map.insertCoin_spec {κ : Type} [Value κ] (mp : Map κ QualifiedShieldedCoinInfo) (m : List (AV × SV))
    (k : κ) (ks : List Fr) (kv : AV)
    (hpath : mp.path = [fieldKey mp.index]) (hst : σ.state = .array fields)
    (hf : fields[mp.index]? = some (.map m)) (hb : mp.index < 256) (hwf : σ.WF)
    (hctx : σ.context = .array cfs) (hidx : cfs[1]? = some (.map idx))
    (hk : Expr.evalList p env (Value.toExprs k) = some ks) (hkv : AV.ofFields (alignOf κ) ks = some kv)
    (hcoin : Expr.evalList p env (Value.toExprs coin) = some coinFs)
    (hcv : AV.ofFields (alignOf ShieldedCoinInfo) coinFs = some cv)
    (hcm : Expr.evalList p env (Value.toExprs (coinCommitment coin recipient)) = some cmFs)
    (hcmv : AV.ofFields [.bytes 32] cmFs = some cmv) :
    ∃ req, (emitted (mp.insertCoin k coin recipient)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ =
        (qualifyAV cv idx cmv).map fun q => ([], σ.setField mp.index (.map (assocSet kv (.cell q) m))) := by
  have he : emitted (mp.insertCoin k coin recipient) = some ([.idx false true mp.path,
      .push false ⟨alignOf κ, Value.toExprs k⟩] ++ CoinStore.qualify (3 + 2 * mp.path.length) coin recipient ++
      [.ins false 1, .ins true mp.path.length]) := rfl
  rw [he, qualify_eq, hpath]
  rw [evalList_eq_mapM] at hcoin hcm hk
  refine ⟨[.idx false true [⟨[.bytes 1], [Fr.ofInt mp.index]⟩], .push false ⟨alignOf κ, ks⟩] ++
    qualifyReq 5 cmFs coinFs ++ [.ins false 1, .ins true 1], ?_, ?_⟩
  · simp [Exec.request, Op.mapM, Aligned.mapM, hcoin, hcm, hk, Exec.blank, fieldKey, Expr.eval, qualifyReq,
      alignOf_bytes32, alignOf_coin]
  · have hkey := ofAligned_byteKey hb
    have hk1 := ofFields_key1
    simp only [AV.ofAligned] at hkey
    rw [LedgerState.WF] at hwf
    rw [alignOf_coin] at hcv
    have hi := lt_of_getElem? hf
    have hf' := getElem_of_getElem? hf
    obtain ⟨ctx, eff, st⟩ := σ
    simp only at hst hwf hctx ⊢
    subst hst hctx
    cases hq : assocGet cmv idx with
    | none =>
      vm_simp [qualifyReq, hb, hkey, hk1, hwf, hi, hf, hf', hkv, hidx, hcv, hcmv, hq, qualifyAV, LedgerState.setField]
    | some v =>
      cases v with
      | cell w =>
        by_cases hsz : w.size + cv.size ≤ 91
        · vm_simp [qualifyReq, hb, hkey, hk1, hwf, hi, hf, hf', hkv, hidx, hcv, hcmv, hq, qualifyAV, hsz, cellBound,
            LedgerState.setField]
        · vm_simp [qualifyReq, hb, hkey, hk1, hwf, hi, hf, hf', hkv, hidx, hcv, hcmv, hq, qualifyAV, hsz, cellBound,
            LedgerState.setField]
      | _ =>
        vm_simp [qualifyReq, hb, hkey, hk1, hwf, hi, hf, hf', hkv, hidx, hcv, hcmv, hq, qualifyAV,
          LedgerState.setField]

/-- **`Set.insertCoin coin recipient`** on a top-level set: the qualified coin
    is added to the set (as a key, against null), or the request fails as for
    `Cell.writeCoin`. -/
theorem Set.insertCoin_spec (st : Set QualifiedShieldedCoinInfo) (m : List (AV × SV))
    (hpath : st.path = [fieldKey st.index]) (hst : σ.state = .array fields)
    (hf : fields[st.index]? = some (.map m)) (hb : st.index < 256) (hwf : σ.WF)
    (hctx : σ.context = .array cfs) (hidx : cfs[1]? = some (.map idx))
    (hcoin : Expr.evalList p env (Value.toExprs coin) = some coinFs)
    (hcv : AV.ofFields (alignOf ShieldedCoinInfo) coinFs = some cv)
    (hcm : Expr.evalList p env (Value.toExprs (coinCommitment coin recipient)) = some cmFs)
    (hcmv : AV.ofFields [.bytes 32] cmFs = some cmv) :
    ∃ req, (emitted (st.insertCoin coin recipient)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ =
        (qualifyAV cv idx cmv).map fun q => ([], σ.setField st.index (.map (assocSet q .null m))) := by
  have he : emitted (st.insertCoin coin recipient) = some ([.idx false true st.path] ++
      CoinStore.qualify (2 + 2 * st.path.length) coin recipient ++
      [.pushNull true, .ins false 1, .ins true st.path.length]) := rfl
  rw [he, qualify_eq, hpath]
  rw [evalList_eq_mapM] at hcoin hcm
  refine ⟨[.idx false true [⟨[.bytes 1], [Fr.ofInt st.index]⟩]] ++
    qualifyReq 4 cmFs coinFs ++ [.pushNull true, .ins false 1, .ins true 1], ?_, ?_⟩
  · simp [Exec.request, Op.mapM, Aligned.mapM, hcoin, hcm, Exec.blank, fieldKey, Expr.eval, qualifyReq,
      alignOf_bytes32, alignOf_coin]
  · have hkey := ofAligned_byteKey hb
    have hk1 := ofFields_key1
    simp only [AV.ofAligned] at hkey
    rw [LedgerState.WF] at hwf
    rw [alignOf_coin] at hcv
    have hi := lt_of_getElem? hf
    have hf' := getElem_of_getElem? hf
    obtain ⟨ctx, eff, s⟩ := σ
    simp only at hst hwf hctx ⊢
    subst hst hctx
    cases hq : assocGet cmv idx with
    | none =>
      vm_simp [qualifyReq, hb, hkey, hk1, hwf, hi, hf, hf', hidx, hcv, hcmv, hq, qualifyAV, LedgerState.setField]
    | some v =>
      cases v with
      | cell w =>
        by_cases hsz : w.size + cv.size ≤ 91
        · vm_simp [qualifyReq, hb, hkey, hk1, hwf, hi, hf, hf', hidx, hcv, hcmv, hq, qualifyAV, hsz, cellBound,
            LedgerState.setField]
        · vm_simp [qualifyReq, hb, hkey, hk1, hwf, hi, hf, hf', hidx, hcv, hcmv, hq, qualifyAV, hsz, cellBound,
            LedgerState.setField]
      | _ =>
        vm_simp [qualifyReq, hb, hkey, hk1, hwf, hi, hf, hf', hidx, hcv, hcmv, hq, qualifyAV, LedgerState.setField]

set_option maxHeartbeats 1000000 in
/-- **`LedgerList.pushFrontCoin coin recipient`** on a top-level list holding
    `xs`: the list becomes `q :: xs`, `q` the qualified coin (for
    `xs.length + 1 < 2^64`), or the request fails as for `Cell.writeCoin`. -/
theorem LedgerList.pushFrontCoin_spec (l : LedgerList QualifiedShieldedCoinInfo) (xs : List AV)
    (hpath : l.path = [fieldKey l.index]) (hst : σ.state = .array fields)
    (hf : fields[l.index]? = some (listRepr xs)) (hb : l.index < 256) (hwf : σ.WF)
    (hlen : xs.length + 1 < 2 ^ 64)
    (hctx : σ.context = .array cfs) (hidx : cfs[1]? = some (.map idx))
    (hcoin : Expr.evalList p env (Value.toExprs coin) = some coinFs)
    (hcv : AV.ofFields (alignOf ShieldedCoinInfo) coinFs = some cv)
    (hcm : Expr.evalList p env (Value.toExprs (coinCommitment coin recipient)) = some cmFs)
    (hcmv : AV.ofFields [.bytes 32] cmFs = some cmv) :
    ∃ req, (emitted (l.pushFrontCoin coin recipient)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ =
        (qualifyAV cv idx cmv).map fun q => ([], σ.setField l.index (listRepr (q :: xs))) := by
  have he : emitted (l.pushFrontCoin coin recipient) = some ([.idx false true l.path, .dup 0,
      .idx false false [fieldKey 2], .addi (.const 1), .pushState true (.array [.null, .null, .null]),
      .push false (fieldKey 0)] ++ CoinStore.qualify (5 + 2 * l.path.length) coin recipient ++
      [.ins true 1, .swap 0, .push false (fieldKey 2), .swap 0, .ins true 1, .swap 0, .push false (fieldKey 1),
       .swap 0, .ins true (l.path.length + 1)]) := rfl
  rw [he, qualify_eq, hpath]
  rw [evalList_eq_mapM] at hcoin hcm
  refine ⟨[.idx false true [⟨[.bytes 1], [Fr.ofInt l.index]⟩], .dup 0, .idx false false [⟨[.bytes 1], [Fr.ofInt 2]⟩],
    .addi (Fr.ofInt 1), .pushState true (.array [.null, .null, .null]), .push false ⟨[.bytes 1], [Fr.ofInt 0]⟩] ++
    qualifyReq 7 cmFs coinFs ++ [.ins true 1, .swap 0, .push false ⟨[.bytes 1], [Fr.ofInt 2]⟩, .swap 0, .ins true 1,
      .swap 0, .push false ⟨[.bytes 1], [Fr.ofInt 1]⟩, .swap 0, .ins true 2], ?_, ?_⟩
  · simp [Exec.request, Op.mapM, Aligned.mapM, StateLit.mapM, StateLit.mapMList, hcoin, hcm, Exec.blank, fieldKey,
      Expr.eval, qualifyReq, alignOf_bytes32, alignOf_coin]
  · have hkey := ofAligned_byteKey hb
    have hk0 := ofFields_key0
    have hk1 := ofFields_key1
    have hk2 := ofFields_key2
    have h1 : (Fr.ofInt 1).val = 1 := rfl
    simp only [AV.ofAligned] at hkey
    rw [LedgerState.WF] at hwf
    rw [alignOf_coin] at hcv
    have hi := lt_of_getElem? hf
    have hf' := getElem_of_getElem? hf
    obtain ⟨ctx, eff, s⟩ := σ
    simp only at hst hwf hctx ⊢
    subst hst hctx
    cases xs with
    | nil =>
      simp only [listRepr] at hf hf' ⊢
      cases hq : assocGet cmv idx with
      | none =>
        vm_simp [qualifyReq, hb, hkey, hk0, hk1, hk2, h1, hwf, hi, hf, hf', hidx, hcv, hcmv, hq, qualifyAV, immOf,
          SV.ofLit, SV.ofLitList, AV.ofU64, List.set, LedgerState.setField]
      | some v =>
        cases v with
        | cell w =>
          by_cases hsz : w.size + cv.size ≤ 91
          · vm_simp [qualifyReq, hb, hkey, hk0, hk1, hk2, h1, hwf, hi, hf, hf', hidx, hcv, hcmv, hq, qualifyAV, hsz,
              cellBound, immOf, SV.ofLit, SV.ofLitList, AV.ofU64, List.set, LedgerState.setField]
          · vm_simp [qualifyReq, hb, hkey, hk0, hk1, hk2, h1, hwf, hi, hf, hf', hidx, hcv, hcmv, hq, qualifyAV, hsz,
              cellBound, immOf, SV.ofLit, SV.ofLitList, AV.ofU64, List.set, LedgerState.setField]
        | _ =>
          vm_simp [qualifyReq, hb, hkey, hk0, hk1, hk2, h1, hwf, hi, hf, hf', hidx, hcv, hcmv, hq, qualifyAV, immOf,
            SV.ofLit, SV.ofLitList, AV.ofU64, List.set, LedgerState.setField]
    | cons y ys =>
      simp only [listRepr, List.length_cons] at hf hf' hlen ⊢
      have hl1 : ys.length + 1 < 18446744073709551616 := by omega
      have hl2 : ys.length + 1 + 1 < 18446744073709551616 := by omega
      cases hq : assocGet cmv idx with
      | none =>
        vm_simp [qualifyReq, hl1, hl2, hlen, hb, hkey, hk0, hk1, hk2, h1, hwf, hi, hf, hf', hidx, hcv, hcmv, hq,
          qualifyAV, immOf, SV.ofLit, SV.ofLitList, AV.ofU64, List.set, LedgerState.setField]
      | some v =>
        cases v with
        | cell w =>
          by_cases hsz : w.size + cv.size ≤ 91
          · vm_simp [qualifyReq, hl1, hl2, hlen, hb, hkey, hk0, hk1, hk2, h1, hwf, hi, hf, hf', hidx, hcv, hcmv, hq,
              qualifyAV, hsz, cellBound, immOf, SV.ofLit, SV.ofLitList, AV.ofU64, List.set, LedgerState.setField]
          · vm_simp [qualifyReq, hl1, hl2, hlen, hb, hkey, hk0, hk1, hk2, h1, hwf, hi, hf, hf', hidx, hcv, hcmv, hq,
              qualifyAV, hsz, cellBound, immOf, SV.ofLit, SV.ofLitList, AV.ofU64, List.set, LedgerState.setField]
        | _ =>
          vm_simp [qualifyReq, hl1, hl2, hlen, hb, hkey, hk0, hk1, hk2, h1, hwf, hi, hf, hf', hidx, hcv, hcmv, hq,
            qualifyAV, immOf, SV.ofLit, SV.ofLitList, AV.ofU64, List.set, LedgerState.setField]

end

end Damp.Ledger
