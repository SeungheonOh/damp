/-
`Map` and `Set` (`Damp/Lang/Ledger.lean`) against the VM model, for a
top-level field (`path = [fieldKey index]`, the default) holding a map.

A map's keys are aligned values: a key `k : κ` reaches the VM as `kv`, its
field elements `ks` converted under `κ`'s alignment (`AV.ofFields`, failing
where the runtime rejects the value). A map is a list of entries with
distinct keys (`(m.map Prod.fst).Nodup`, true of every map the VM builds),
looked up with `assocGet`, updated with `assocSet` and `assocErase`. A set is
a map whose values are null.
-/
import Damp.Proofs.Ledger.Counter

namespace Damp.Ledger
open Damp.IR Damp.Impact

set_option linter.unusedSimpArgs false

/-! ## Association lists -/

section Assoc
variable {κ ν : Type} [DecidableEq κ]

theorem assocGet_assocSet_self (k : κ) (v : ν) : ∀ m : List (κ × ν), assocGet k (assocSet k v m) = some v
  | [] => by simp [assocSet, assocGet]
  | (k', v') :: rest => by
      by_cases h : k' = k
      · simp [assocSet, assocGet, h]
      · simp [assocSet, assocGet, h, assocGet_assocSet_self k v rest]

theorem assocGet_assocSet_ne {k j : κ} (v : ν) (h : j ≠ k) :
    ∀ m : List (κ × ν), assocGet j (assocSet k v m) = assocGet j m
  | [] => by simp [assocSet, assocGet, Ne.symm h]
  | (k', v') :: rest => by
      by_cases hk : k' = k
      · subst hk; simp [assocSet, assocGet, Ne.symm h]
      · by_cases hj : k' = j
        · subst hj; simp [assocSet, assocGet, hk]
        · simp [assocSet, assocGet, hk, hj, assocGet_assocSet_ne v h rest]

theorem assocGet_eq_none_of_not_mem (k : κ) : ∀ m : List (κ × ν), k ∉ m.map Prod.fst → assocGet k m = none
  | [], _ => rfl
  | (k', v') :: rest, h => by
      have h1 : k' ≠ k := fun e => h (by simp [e])
      have h2 : k ∉ rest.map Prod.fst := fun e => h (by simp at e ⊢; exact Or.inr e)
      simp [assocGet, h1, assocGet_eq_none_of_not_mem k rest h2]

theorem assocGet_assocErase_self (k : κ) :
    ∀ m : List (κ × ν), (m.map Prod.fst).Nodup → assocGet k (assocErase k m) = none
  | [], _ => rfl
  | (k', v') :: rest, h => by
      simp only [List.map_cons, List.nodup_cons] at h
      by_cases hk : k' = k
      · subst hk; simp [assocErase, assocGet_eq_none_of_not_mem k' rest h.1]
      · simp [assocErase, assocGet, hk, assocGet_assocErase_self k rest h.2]

theorem assocGet_assocErase_ne {k j : κ} (h : j ≠ k) :
    ∀ m : List (κ × ν), assocGet j (assocErase k m) = assocGet j m
  | [] => rfl
  | (k', v') :: rest => by
      by_cases hk : k' = k
      · subst hk; simp [assocErase, assocGet, Ne.symm h]
      · by_cases hj : k' = j
        · subst hj; simp [assocErase, assocGet, hk]
        · simp [assocErase, assocGet, hk, hj, assocGet_assocErase_ne h rest]

theorem length_assocSet_of_none (k : κ) (v : ν) :
    ∀ m : List (κ × ν), assocGet k m = none → (assocSet k v m).length = m.length + 1
  | [], _ => rfl
  | (k', v') :: rest, h => by
      by_cases hk : k' = k
      · simp [assocGet, hk] at h
      · simp [assocGet, hk] at h
        simp [assocSet, hk, length_assocSet_of_none k v rest h]

theorem length_assocSet_of_some (k : κ) (v : ν) :
    ∀ m : List (κ × ν), (assocGet k m).isSome → (assocSet k v m).length = m.length
  | [], h => by simp [assocGet] at h
  | (k', v') :: rest, h => by
      by_cases hk : k' = k
      · simp [assocSet, hk]
      · simp [assocGet, hk] at h
        simp [assocSet, hk, length_assocSet_of_some k v rest h]

end Assoc

/-! ## The operations -/

section
variable {κ : Type} [Value κ] (H : Hooks) (p : Zkir.Prims) (env : Env) (σ : LedgerState)
  (fields : List SV) (m : List (AV × SV)) (k : κ) (ks : List Fr) (kv : AV)

/-- What the VM does with `idx pushPath [{1: i}]; push k; <push value>; ins
    false 1; ins true 1` on a top-level map: the map with the entry set. -/
theorem insertOps_spec (i : Nat) (val : SV) (vop : Op Fr) (hrv : Op.toR vop = some (.push true val))
    (hst : σ.state = .array fields) (hf : fields[i]? = some (.map m)) (hb : i < 256) (hwf : σ.WF)
    (hkv : AV.ofFields (alignOf κ) ks = some kv) :
    ledgerOracle H [.idx false true [⟨[.bytes 1], [Fr.ofInt i]⟩], .push false ⟨alignOf κ, ks⟩, vop,
      .ins false 1, .ins true 1] σ = some ([], σ.setField i (.map (assocSet kv val m))) := by
  have hkey := ofAligned_byteKey hb
  simp only [AV.ofAligned] at hkey
  rw [LedgerState.WF] at hwf
  have hi := lt_of_getElem? hf
  have hf' := getElem_of_getElem? hf
  have hpa : popeqAligns [vop, .ins false 1, .ins true 1] = [] := by
    cases vop <;> simp_all [popeqAligns, Op.toR]
  simp only [ledgerOracle, List.mapM_cons, List.mapM_nil, hrv]
  simp [hpa, hb, hi, hf, hf', hwf, hkv, Op.toR, AV.ofAligned, hkey, query,
    LedgerState.vm, VmState.init, runR, ROp.exec, ROp.stackReq, hst, VmState.push, VmState.pop,
    VmState.popCell, VmState.pushNew, idxWalk, idxOne, insLoop, Cache.visit, CTree.visit, Cache.get, CTree.get,
    Cache.contains, CTree.contains, Cache.keyFor, insCache, assocGet, assocSet, AV.toU8, SV.asCell,
    maxStackHeight, readBack_nil, popeqAligns, CKey.push, LedgerState.setField]

theorem push_exec (storage : Bool) (val : SV) (s : VmState) :
    (ROp.push storage val).exec H s = some (s.push { val, strong := storage, key := none }, 0) := by
  simp [ROp.exec, ROp.stackReq]

variable {ν : Type}

/-- `Map.insert k v`: the map at field `m.index` gets the entry `kv ↦ cell vv`
    (replacing any entry for `kv`). Nothing is read; it never fails on a map. -/
theorem Map.insert_spec [Value ν] (mp : Map κ ν) (v : ν) (vs : List Fr) (vv : AV)
    (hpath : mp.path = [fieldKey mp.index]) (hst : σ.state = .array fields)
    (hf : fields[mp.index]? = some (.map m)) (hb : mp.index < 256) (hwf : σ.WF)
    (hk : Expr.evalList p env (Value.toExprs k) = some ks) (hkv : AV.ofFields (alignOf κ) ks = some kv)
    (hv : Expr.evalList p env (Value.toExprs v) = some vs) (hvv : AV.ofFields (alignOf ν) vs = some vv) :
    ∃ req, (emitted (mp.insert k v)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some ([], σ.setField mp.index (.map (assocSet kv (.cell vv) m))) := by
  have he : emitted (mp.insert k v) = some [.idx false true mp.path, .push false ⟨alignOf κ, Value.toExprs k⟩,
      .push true ⟨alignOf ν, Value.toExprs v⟩, .ins false 1, .ins true mp.path.length] := rfl
  rw [he, hpath]
  rw [evalList_eq_mapM] at hk hv
  refine ⟨_, ?_, insertOps_spec H σ fields m ks kv mp.index (.cell vv) (.push true ⟨alignOf ν, vs⟩)
    (by simp [Op.toR, AV.ofAligned, hvv]) hst hf hb hwf hkv⟩
  simp [Exec.request, Op.mapM, Aligned.mapM, hk, hv, Exec.blank, fieldKey, Expr.eval]

/-- `Set.insert x`: the set at field `s.index` gets `xv` (stored against null). -/
theorem Set.insert_spec (st : Set κ)
    (hpath : st.path = [fieldKey st.index]) (hst : σ.state = .array fields)
    (hf : fields[st.index]? = some (.map m)) (hb : st.index < 256) (hwf : σ.WF)
    (hk : Expr.evalList p env (Value.toExprs k) = some ks) (hkv : AV.ofFields (alignOf κ) ks = some kv) :
    ∃ req, (emitted (st.insert k)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some ([], σ.setField st.index (.map (assocSet kv .null m))) := by
  have he : emitted (st.insert k) = some [.idx false true st.path, .push false ⟨alignOf κ, Value.toExprs k⟩,
      .pushNull true, .ins false 1, .ins true st.path.length] := rfl
  rw [he, hpath]
  rw [evalList_eq_mapM] at hk
  refine ⟨_, ?_, insertOps_spec H σ fields m ks kv st.index .null (.pushNull true)
    (by simp [Op.toR]) hst hf hb hwf hkv⟩
  simp [Exec.request, Op.mapM, Aligned.mapM, hk, Exec.blank, fieldKey, Expr.eval]

/-- What the VM does with `idx pushPath [{1: i}]; push k; rem false; ins true 1`. -/
theorem removeOps_spec (i : Nat)
    (hst : σ.state = .array fields) (hf : fields[i]? = some (.map m)) (hb : i < 256) (hwf : σ.WF)
    (hkv : AV.ofFields (alignOf κ) ks = some kv) :
    ledgerOracle H [.idx false true [⟨[.bytes 1], [Fr.ofInt i]⟩], .push false ⟨alignOf κ, ks⟩, .rem false,
      .ins true 1] σ = some ([], σ.setField i (.map (assocErase kv m))) := by
  have hkey := ofAligned_byteKey hb
  simp only [AV.ofAligned] at hkey
  rw [LedgerState.WF] at hwf
  have hi := lt_of_getElem? hf
  have hf' := getElem_of_getElem? hf
  simp [hb, hi, hf, hf', hwf, hkv, ledgerOracle, Op.toR, AV.ofAligned, hkey, query,
    LedgerState.vm, VmState.init, runR, ROp.exec, ROp.stackReq, hst, VmState.push, VmState.pop,
    VmState.popCell, VmState.pushNew, idxWalk, idxOne, insLoop, Cache.visit, CTree.visit, Cache.get, CTree.get,
    Cache.contains, CTree.contains, Cache.keyFor, insCache, assocGet, assocSet, AV.toU8, SV.asCell,
    maxStackHeight, readBack_nil, popeqAligns, CKey.push, LedgerState.setField]

/-- `Map.remove k`: the entry for `kv` is removed (if there is one). -/
theorem Map.remove_spec (mp : Map κ ν)
    (hpath : mp.path = [fieldKey mp.index]) (hst : σ.state = .array fields)
    (hf : fields[mp.index]? = some (.map m)) (hb : mp.index < 256) (hwf : σ.WF)
    (hk : Expr.evalList p env (Value.toExprs k) = some ks) (hkv : AV.ofFields (alignOf κ) ks = some kv) :
    ∃ req, (emitted (mp.remove k)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some ([], σ.setField mp.index (.map (assocErase kv m))) := by
  have he : emitted (mp.remove k) = some [.idx false true mp.path, .push false ⟨alignOf κ, Value.toExprs k⟩,
      .rem false, .ins true mp.path.length] := rfl
  rw [he, hpath]
  rw [evalList_eq_mapM] at hk
  refine ⟨_, ?_, removeOps_spec H σ fields m ks kv mp.index hst hf hb hwf hkv⟩
  simp [Exec.request, Op.mapM, Aligned.mapM, hk, Exec.blank, fieldKey, Expr.eval]

/-- `Set.remove x`: `xv` is removed from the set. -/
theorem Set.remove_spec (st : Set κ)
    (hpath : st.path = [fieldKey st.index]) (hst : σ.state = .array fields)
    (hf : fields[st.index]? = some (.map m)) (hb : st.index < 256) (hwf : σ.WF)
    (hk : Expr.evalList p env (Value.toExprs k) = some ks) (hkv : AV.ofFields (alignOf κ) ks = some kv) :
    ∃ req, (emitted (st.remove k)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some ([], σ.setField st.index (.map (assocErase kv m))) := by
  have he : emitted (st.remove k) = some [.idx false true st.path, .push false ⟨alignOf κ, Value.toExprs k⟩,
      .rem false, .ins true st.path.length] := rfl
  rw [he, hpath]
  rw [evalList_eq_mapM] at hk
  refine ⟨_, ?_, removeOps_spec H σ fields m ks kv st.index hst hf hb hwf hkv⟩
  simp [Exec.request, Op.mapM, Aligned.mapM, hk, Exec.blank, fieldKey, Expr.eval]

/-- What the VM does with `dup 0; idx [{1: i}]; push k; member; popeq`. -/
theorem memberOps_spec (i : Nat)
    (hst : σ.state = .array fields) (hf : fields[i]? = some (.map m)) (hb : i < 256) (hwf : σ.WF)
    (hkv : AV.ofFields (alignOf κ) ks = some kv) :
    ledgerOracle H [.dup 0, .idx false false [⟨[.bytes 1], [Fr.ofInt i]⟩], .push false ⟨alignOf κ, ks⟩,
      .member, .popeq true [.bytes 1] []] σ = some ([Fr.ofBool (assocGet kv m).isSome], σ) := by
  have hkey := ofAligned_byteKey hb
  simp only [AV.ofAligned] at hkey
  rw [LedgerState.WF] at hwf
  have hi := lt_of_getElem? hf
  have hf' := getElem_of_getElem? hf
  simp [hb, hi, hf, hf', hwf, hkv, ledgerOracle, Op.toR, AV.ofAligned, hkey, query,
    LedgerState.vm, VmState.init, runR, ROp.exec, ROp.stackReq, hst, VmState.push, VmState.pop,
    VmState.popCell, VmState.pushNew, idxWalk, idxOne, Cache.visit, CTree.visit, assocSet, AV.toU8, SV.asCell,
    AV.ofBool, maxStackHeight, popeqAligns, CKey.push]
  have hbool := fieldsOf_bool (assocGet kv m).isSome
  cases σ; simp_all [readBack_cons, readBack_nil, assocGet]

/-- `Map.member k`: whether the map has an entry for `kv`; the ledger is unchanged. -/
theorem Map.member_spec (mp : Map κ ν)
    (hpath : mp.path = [fieldKey mp.index]) (hst : σ.state = .array fields)
    (hf : fields[mp.index]? = some (.map m)) (hb : mp.index < 256) (hwf : σ.WF)
    (hk : Expr.evalList p env (Value.toExprs k) = some ks) (hkv : AV.ofFields (alignOf κ) ks = some kv) :
    ∃ req, (emitted (mp.member k)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some ([Fr.ofBool (assocGet kv m).isSome], σ) := by
  have he : mp.member k = ledgerRead Boolean (fun es =>
      [.dup 0, .idx false false mp.path, .push false ⟨alignOf κ, Value.toExprs k⟩, .member,
       .popeq true [.bytes 1] es]) := rfl
  rw [he, emitted_ledgerRead, hpath]
  rw [evalList_eq_mapM] at hk
  refine ⟨_, ?_, memberOps_spec H σ fields m ks kv mp.index hst hf hb hwf hkv⟩
  simp [Exec.request, Op.mapM, Aligned.mapM, hk, Exec.blank, fieldKey, Expr.eval, mapM_eval_readVars]

/-- `Set.member x`: whether `xv` is in the set; the ledger is unchanged. -/
theorem Set.member_spec (st : Set κ)
    (hpath : st.path = [fieldKey st.index]) (hst : σ.state = .array fields)
    (hf : fields[st.index]? = some (.map m)) (hb : st.index < 256) (hwf : σ.WF)
    (hk : Expr.evalList p env (Value.toExprs k) = some ks) (hkv : AV.ofFields (alignOf κ) ks = some kv) :
    ∃ req, (emitted (st.member k)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some ([Fr.ofBool (assocGet kv m).isSome], σ) := by
  have he : st.member k = ledgerRead Boolean (fun es =>
      [.dup 0, .idx false false st.path, .push false ⟨alignOf κ, Value.toExprs k⟩, .member,
       .popeq true [.bytes 1] es]) := rfl
  rw [he, emitted_ledgerRead, hpath]
  rw [evalList_eq_mapM] at hk
  refine ⟨_, ?_, memberOps_spec H σ fields m ks kv st.index hst hf hb hwf hkv⟩
  simp [Exec.request, Op.mapM, Aligned.mapM, hk, Exec.blank, fieldKey, Expr.eval, mapM_eval_readVars]

/-- What the VM does with `dup 0; idx [{1: i}]; size; popeq`. -/
theorem sizeOps_spec (i : Nat)
    (hst : σ.state = .array fields) (hf : fields[i]? = some (.map m)) (hb : i < 256) (hwf : σ.WF)
    (hm : m.length < 2 ^ 64) :
    ledgerOracle H [.dup 0, .idx false false [⟨[.bytes 1], [Fr.ofInt i]⟩], .size, .popeq true [.bytes 8] []] σ =
      some ([Fr.ofNat m.length], σ) := by
  have hkey := ofAligned_byteKey hb
  simp only [AV.ofAligned] at hkey
  rw [LedgerState.WF] at hwf
  have hi := lt_of_getElem? hf
  have hf' := getElem_of_getElem? hf
  simp [hb, hi, hf, hf', hwf, ledgerOracle, Op.toR, AV.ofAligned, hkey, query,
    LedgerState.vm, VmState.init, runR, ROp.exec, ROp.stackReq, hst, VmState.push, VmState.pop,
    VmState.popCell, VmState.pushNew, idxWalk, idxOne, Cache.visit, CTree.visit, assocGet, assocSet, AV.toU8,
    SV.asCell, AV.ofU64, maxStackHeight, popeqAligns, CKey.push]
  have hu := fieldsOf_u64 m.length hm
  cases σ; simp_all [readBack_cons, readBack_nil]

omit [Value κ] in
/-- `Map.size`: the number of entries; the ledger is unchanged. -/
theorem Map.size_spec (mp : Map κ ν)
    (hpath : mp.path = [fieldKey mp.index]) (hst : σ.state = .array fields)
    (hf : fields[mp.index]? = some (.map m)) (hb : mp.index < 256) (hwf : σ.WF) (hm : m.length < 2 ^ 64) :
    ∃ req, (emitted mp.size).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some ([Fr.ofNat m.length], σ) := by
  have he : mp.size = ledgerRead Uint64 (fun es =>
      [.dup 0, .idx false false mp.path, .size, .popeq true [.bytes 8] es]) := rfl
  rw [he, emitted_ledgerRead, hpath]
  refine ⟨_, ?_, sizeOps_spec H σ fields m mp.index hst hf hb hwf hm⟩
  simp [Exec.request, Op.mapM, Aligned.mapM, Exec.blank, fieldKey, Expr.eval, mapM_eval_readVars]

omit [Value κ] in
/-- `Set.size`: the number of elements; the ledger is unchanged. -/
theorem Set.size_spec (st : Set κ)
    (hpath : st.path = [fieldKey st.index]) (hst : σ.state = .array fields)
    (hf : fields[st.index]? = some (.map m)) (hb : st.index < 256) (hwf : σ.WF) (hm : m.length < 2 ^ 64) :
    ∃ req, (emitted st.size).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some ([Fr.ofNat m.length], σ) := by
  have he : st.size = ledgerRead Uint64 (fun es =>
      [.dup 0, .idx false false st.path, .size, .popeq true [.bytes 8] es]) := rfl
  rw [he, emitted_ledgerRead, hpath]
  refine ⟨_, ?_, sizeOps_spec H σ fields m st.index hst hf hb hwf hm⟩
  simp [Exec.request, Op.mapM, Aligned.mapM, Exec.blank, fieldKey, Expr.eval, mapM_eval_readVars]

/-- `Map.lookup k` of a plain value: the field elements of the value stored
    for `kv`, read under `ν`'s alignment; the ledger is unchanged. -/
theorem Map.lookup_spec [Value ν] (mp : Map κ ν) (w : AV) (ys : List Fr)
    (hpath : mp.path = [fieldKey mp.index]) (hst : σ.state = .array fields)
    (hf : fields[mp.index]? = some (.map m)) (hb : mp.index < 256) (hwf : σ.WF)
    (hk : Expr.evalList p env (Value.toExprs k) = some ks) (hkv : AV.ofFields (alignOf κ) ks = some kv)
    (hget : assocGet kv m = some (.cell w)) (hys : fieldsOf (alignOf ν) w.atoms = some ys) :
    ∃ req, (emitted (mp.lookup k)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some (ys, σ) := by
  have he : mp.lookup k = ledgerRead ν (fun es =>
      [.dup 0, .idx false false mp.path, .idx false false [⟨alignOf κ, Value.toExprs k⟩],
       .popeq false (alignOf ν) es]) := rfl
  rw [he, emitted_ledgerRead, hpath]
  rw [evalList_eq_mapM] at hk
  refine ⟨[.dup 0, .idx false false [⟨[.bytes 1], [Fr.ofInt mp.index]⟩], .idx false false [⟨alignOf κ, ks⟩],
    .popeq false (alignOf ν) []], ?_, ?_⟩
  · simp [Exec.request, Op.mapM, Aligned.mapM, hk, Exec.blank, fieldKey, Expr.eval, mapM_eval_readVars]
  · have hkey := ofAligned_byteKey hb
    simp only [AV.ofAligned] at hkey
    rw [LedgerState.WF] at hwf
    have hi := lt_of_getElem? hf
    have hf' := getElem_of_getElem? hf
    simp [hb, hi, hf, hf', hwf, hkv, hget, ledgerOracle, Op.toR, AV.ofAligned, hkey, query,
      LedgerState.vm, VmState.init, runR, ROp.exec, ROp.stackReq, hst, VmState.push, VmState.pop,
      VmState.popCell, VmState.pushNew, idxWalk, idxOne, Cache.visit, CTree.visit, assocSet, AV.toU8,
      SV.asCell, maxStackHeight, popeqAligns, CKey.push]
    cases σ; simp_all [readBack_cons, readBack_nil, assocGet]

/-- `Map.lookup k` of a plain value fails when the map has no entry for `kv`
    (the VM indexes to null, and `popeq` needs a cell). -/
theorem Map.lookup_absent [Value ν] (mp : Map κ ν)
    (hpath : mp.path = [fieldKey mp.index]) (hst : σ.state = .array fields)
    (hf : fields[mp.index]? = some (.map m)) (hb : mp.index < 256)
    (hk : Expr.evalList p env (Value.toExprs k) = some ks) (hkv : AV.ofFields (alignOf κ) ks = some kv)
    (hget : assocGet kv m = none) :
    ∃ req, (emitted (mp.lookup k)).bind (Exec.request p env) = some req ∧ ledgerOracle H req σ = none := by
  have he : mp.lookup k = ledgerRead ν (fun es =>
      [.dup 0, .idx false false mp.path, .idx false false [⟨alignOf κ, Value.toExprs k⟩],
       .popeq false (alignOf ν) es]) := rfl
  rw [he, emitted_ledgerRead, hpath]
  rw [evalList_eq_mapM] at hk
  refine ⟨[.dup 0, .idx false false [⟨[.bytes 1], [Fr.ofInt mp.index]⟩], .idx false false [⟨alignOf κ, ks⟩],
    .popeq false (alignOf ν) []], ?_, ?_⟩
  · simp [Exec.request, Op.mapM, Aligned.mapM, hk, Exec.blank, fieldKey, Expr.eval, mapM_eval_readVars]
  · have hkey := ofAligned_byteKey hb
    simp only [AV.ofAligned] at hkey
    have hi := lt_of_getElem? hf
    have hf' := getElem_of_getElem? hf
    simp [hb, hi, hf, hf', hkv, hget, ledgerOracle, Op.toR, AV.ofAligned, hkey, query,
      LedgerState.vm, VmState.init, runR, ROp.exec, ROp.stackReq, hst, VmState.push, VmState.pop,
      VmState.popCell, VmState.pushNew, idxWalk, idxOne, Cache.visit, CTree.visit, assocSet, AV.toU8,
      SV.asCell, maxStackHeight, popeqAligns, CKey.push]

/-! ### Sequences -/

/-- Insert, then look up the same key: the value inserted comes back (for a
    single-limb value type), and other keys are unaffected (`assocGet_assocSet_ne`). -/
theorem Map.insert_lookup [Value ν] (mp : Map κ ν) (v : ν) (vs : List Fr) (vv : AV)
    (hpath : mp.path = [fieldKey mp.index]) (hst : σ.state = .array fields)
    (hf : fields[mp.index]? = some (.map m)) (hb : mp.index < 256) (hwf : σ.WF)
    (hk : Expr.evalList p env (Value.toExprs k) = some ks) (hkv : AV.ofFields (alignOf κ) ks = some kv)
    (hv : Expr.evalList p env (Value.toExprs v) = some vs) (hvv : AV.ofFields (alignOf ν) vs = some vv)
    (hsl : SingleLimb (alignOf ν)) (hlen : vs.length = (alignOf ν).length) :
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
    (fieldsOf_ofFields _ vs vv hvv hsl hlen)
  exact ⟨req₁, req₂, _, h1, h2, h3, h4⟩

end

end Damp.Ledger
