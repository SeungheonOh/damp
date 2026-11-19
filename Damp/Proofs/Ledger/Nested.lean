/-
More of `Damp/Lang/Ledger.lean` against the VM model: `Map.isEmpty`,
`Set.isEmpty`, `Map.insertDefault` (plain values and counters), and a ledger
type inside a map value: a `Counter` reached through `(← m.lookup k)`, whose
path is `[fieldKey i, k]`.

As in `Map.lean`, the map is a top-level field holding `.map m`, the key `k`
evaluates to `ks` and reaches the VM as `kv`.
-/
import Damp.Proofs.Ledger.Map

namespace Damp.Ledger
open Damp.IR Damp.Impact

set_option linter.unusedSimpArgs false

section
variable {κ : Type} [Value κ] (H : Hooks) (p : Zkir.Prims) (env : Env) (σ : LedgerState)
  (fields : List SV) (m : List (AV × SV)) (k : κ) (ks : List Fr) (kv : AV)

/-- What the VM does with `dup 0; idx [{1: i}]; size; push {8: 0}; eq; popeq`. -/
theorem isEmptyOps_spec (i : Nat)
    (hst : σ.state = .array fields) (hf : fields[i]? = some (.map m)) (hb : i < 256) (hwf : σ.WF)
    (hm : m.length < 2 ^ 64) :
    ledgerOracle H [.dup 0, .idx false false [⟨[.bytes 1], [Fr.ofInt i]⟩], .size,
      .push false ⟨[.bytes 8], [Fr.ofInt 0]⟩, .eq, .popeq true [.bytes 1] []] σ =
      some ([Fr.ofBool (decide (m.length = 0))], σ) := by
  have hkey := ofAligned_byteKey hb
  simp only [AV.ofAligned] at hkey
  rw [LedgerState.WF] at hwf
  have hi := lt_of_getElem? hf
  have hf' := getElem_of_getElem? hf
  have h0 : (Fr.ofInt 0).val = 0 := rfl
  have hz : AV.ofFields [.bytes 8] [Fr.ofInt 0] = some ⟨[.bytes 8], [0]⟩ := by
    simp [AV.ofFields, atomWidth, atomOfFields, atomFits, h0]
  have hsz : (AV.ofU64 m.length).size ≤ 64 := by
    simp only [AV.ofU64, AV.size, atomSize, alignAtomSize, flaggedIntSize, byteLen]
    split <;> split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;>
      (try omega) <;> (have := (Nat.log2_lt (n := m.length) (by omega)).2 hm; omega)
  have hsz0 : (AV.ofU64 0).size ≤ 64 := by decide
  have hsz' : (⟨[.bytes 8], [0]⟩ : AV).size ≤ 64 := hsz0
  simp [hb, hi, hf, hf', hwf, ledgerOracle, Op.toR, AV.ofAligned, hkey, hz, query,
    LedgerState.vm, VmState.init, runR, ROp.exec, ROp.stackReq, hst, VmState.push, VmState.pop,
    VmState.popCell, VmState.pushNew, idxWalk, idxOne, Cache.visit, CTree.visit, assocGet, assocSet, AV.toU8,
    SV.asCell, maxStackHeight, popeqAligns, CKey.push, hsz, hsz']
  have hbool : fieldsOf [.bytes 1] [if m = [] then 1 else 0] = some [Fr.ofBool (decide (m = []))] := by
    have := fieldsOf_bool (decide (m = []))
    simpa using this
  cases σ
  simp only at hst hwf
  subst hst
  simp [runR, ROp.exec, ROp.stackReq, VmState.popCell, VmState.pop, SV.asCell, maxStackHeight, hwf,
    readBack_cons, readBack_nil, hbool, hsz, hsz', AV.ofU64, AV.ofBool, eq_comm]

omit [Value κ] in
/-- `Map.isEmpty`: whether the map has no entry; the ledger is unchanged. -/
theorem Map.isEmpty_spec {ν : Type} (mp : Map κ ν)
    (hpath : mp.path = [fieldKey mp.index]) (hst : σ.state = .array fields)
    (hf : fields[mp.index]? = some (.map m)) (hb : mp.index < 256) (hwf : σ.WF) (hm : m.length < 2 ^ 64) :
    ∃ req, (emitted mp.isEmpty).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some ([Fr.ofBool (decide (m.length = 0))], σ) := by
  have he : mp.isEmpty = ledgerRead Boolean (fun es =>
      [.dup 0, .idx false false mp.path, .size, .push false { align := [.bytes 8], vals := [.const 0] }, .eq,
       .popeq true [.bytes 1] es]) := rfl
  rw [he, emitted_ledgerRead, hpath]
  refine ⟨_, ?_, isEmptyOps_spec H σ fields m mp.index hst hf hb hwf hm⟩
  simp [Exec.request, Op.mapM, Aligned.mapM, Exec.blank, fieldKey, Expr.eval, mapM_eval_readVars]

omit [Value κ] in
/-- `Set.isEmpty`: whether the set has no element; the ledger is unchanged. -/
theorem Set.isEmpty_spec (st : Set κ)
    (hpath : st.path = [fieldKey st.index]) (hst : σ.state = .array fields)
    (hf : fields[st.index]? = some (.map m)) (hb : st.index < 256) (hwf : σ.WF) (hm : m.length < 2 ^ 64) :
    ∃ req, (emitted st.isEmpty).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some ([Fr.ofBool (decide (m.length = 0))], σ) := by
  have he : st.isEmpty = ledgerRead Boolean (fun es =>
      [.dup 0, .idx false false st.path, .size, .push false { align := [.bytes 8], vals := [.const 0] }, .eq,
       .popeq true [.bytes 1] es]) := rfl
  rw [he, emitted_ledgerRead, hpath]
  refine ⟨_, ?_, isEmptyOps_spec H σ fields m st.index hst hf hb hwf hm⟩
  simp [Exec.request, Op.mapM, Aligned.mapM, Exec.blank, fieldKey, Expr.eval, mapM_eval_readVars]

/-- `Map.insertDefault k` for a map of plain values: the entry `kv ↦` the
    type's zero value (its field elements `zs`, stored as `z`). -/
theorem Map.insertDefault_spec {ν : Type} [Value ν] (mp : Map κ ν) (zs : List Fr) (z : AV)
    (hpath : mp.path = [fieldKey mp.index]) (hst : σ.state = .array fields)
    (hf : fields[mp.index]? = some (.map m)) (hb : mp.index < 256) (hwf : σ.WF)
    (hk : Expr.evalList p env (Value.toExprs k) = some ks) (hkv : AV.ofFields (alignOf κ) ks = some kv)
    (hz : Expr.evalList p env (Value.toExprs (Value.zero ν)) = some zs)
    (hzv : AV.ofFields (alignOf ν) zs = some z) :
    ∃ req, (emitted (mp.insertDefault k)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some ([], σ.setField mp.index (.map (assocSet kv (.cell z) m))) := by
  have he : emitted (mp.insertDefault k) = some [.idx false true mp.path, .push false ⟨alignOf κ, Value.toExprs k⟩,
      .pushState true (.cell ⟨alignOf ν, Value.toExprs (Value.zero ν)⟩), .ins false 1, .ins true mp.path.length] :=
    rfl
  rw [he, hpath]
  rw [evalList_eq_mapM] at hk hz
  refine ⟨_, ?_, insertOps_spec H σ fields m ks kv mp.index (.cell z) (.pushState true (.cell ⟨alignOf ν, zs⟩))
    (by simp [Op.toR, SV.ofLit, AV.ofAligned, hzv]) hst hf hb hwf hkv⟩
  simp [Exec.request, Op.mapM, Aligned.mapM, StateLit.mapM, hk, hz, Exec.blank, fieldKey, Expr.eval]

/-- `Map.insertDefault k` for a map of counters: the entry `kv ↦` a counter at 0. -/
theorem Map.insertDefault_counter_spec (mp : Map κ Counter)
    (hpath : mp.path = [fieldKey mp.index]) (hst : σ.state = .array fields)
    (hf : fields[mp.index]? = some (.map m)) (hb : mp.index < 256) (hwf : σ.WF)
    (hk : Expr.evalList p env (Value.toExprs k) = some ks) (hkv : AV.ofFields (alignOf κ) ks = some kv) :
    ∃ req, (emitted (mp.insertDefault k)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some ([], σ.setField mp.index (.map (assocSet kv (.cell (AV.ofU64 0)) m))) := by
  have he : emitted (mp.insertDefault k) = some [.idx false true mp.path, .push false ⟨alignOf κ, Value.toExprs k⟩,
      .pushState true Counter.initial, .ins false 1, .ins true mp.path.length] := rfl
  rw [he, hpath]
  rw [evalList_eq_mapM] at hk
  refine ⟨_, ?_, insertOps_spec H σ fields m ks kv mp.index (.cell (AV.ofU64 0))
    (.pushState true (.cell ⟨[.bytes 8], [Fr.ofInt 0]⟩))
    (by simp [Op.toR, SV.ofLit, AV.ofAligned, AV.ofFields, atomWidth, atomOfFields, atomFits, AV.ofU64]; rfl)
    hst hf hb hwf hkv⟩
  simp [Counter.initial, Exec.request, Op.mapM, Aligned.mapM, StateLit.mapM, hk, Exec.blank, fieldKey,
    Expr.eval]
  rfl

/-! ## A counter inside a map -/

/-- The counter `(← mp.lookup k)` names, inside a map of counters. -/
theorem Map.lookup_counter_run (mp : Map κ Counter) (s : Build) :
    (mp.lookup k).run s = ({ index := mp.index, path := mp.path ++ [⟨alignOf κ, Value.toExprs k⟩] }, s) := rfl

/-- `(← mp.lookup k).increment amount`: the counter stored for `kv` (holding
    `n`) becomes `n + k`, or the request fails on overflow; the map keeps its
    other entries, and nothing else changes. -/
theorem Map.counter_increment_spec (mp : Map κ Counter) (a : List Zkir.AlignAtom) (n : Nat)
    (amount : Uint16) (j : Fr)
    (hpath : mp.path = [fieldKey mp.index]) (hst : σ.state = .array fields)
    (hf : fields[mp.index]? = some (.map m)) (hb : mp.index < 256) (hwf : σ.WF)
    (hk : Expr.evalList p env (Value.toExprs k) = some ks) (hkv : AV.ofFields (alignOf κ) ks = some kv)
    (hget : assocGet kv m = some (.cell ⟨a, [n]⟩)) (hn : n < 2 ^ 64)
    (hj : Expr.eval p env amount.expr = some j) (hj32 : j.val < 2 ^ 32) :
    ∃ req, (emitted ((((mp.lookup k).run {}).1 : Counter).increment amount)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ =
        if n + j.val < 2 ^ 64 then
          some ([], σ.setField mp.index (.map (assocSet kv (.cell (AV.ofU64 (n + j.val))) m)))
        else none := by
  have he : emitted ((((mp.lookup k).run {}).1 : Counter).increment amount) =
      some [.idx false true (mp.path ++ [⟨alignOf κ, Value.toExprs k⟩]), .addi amount.expr,
        .ins true (mp.path ++ [(⟨alignOf κ, Value.toExprs k⟩ : Aligned Expr)]).length] := rfl
  rw [he, hpath]
  rw [evalList_eq_mapM] at hk
  refine ⟨[.idx false true [⟨[.bytes 1], [Fr.ofInt mp.index]⟩, ⟨alignOf κ, ks⟩], .addi j, .ins true 2], ?_, ?_⟩
  · simp [Exec.request, Op.mapM, Aligned.mapM, hk, hj, Exec.blank, fieldKey, Expr.eval]
  · have hkey := ofAligned_byteKey hb
    simp only [AV.ofAligned] at hkey
    rw [LedgerState.WF] at hwf
    have hi := lt_of_getElem? hf
    have hf' := getElem_of_getElem? hf
    by_cases hov : n + j.val < 2 ^ 64
    · simp [hov, hb, hi, hf, hf', hwf, hn, hj32, hkv, hget, immOf, ledgerOracle, Op.toR, AV.ofAligned, hkey, query,
        LedgerState.vm, VmState.init, runR, ROp.exec, ROp.stackReq, hst, VmState.push, VmState.pop,
        VmState.popU64, VmState.popCell, VmState.pushNew, idxWalk, idxOne, insLoop, Cache.visit, CTree.visit,
        Cache.get, CTree.get, Cache.contains, CTree.contains, Cache.keyFor, insCache, assocGet, assocSet,
        AV.toU8, AV.toU64, AV.ofU64, SV.asCell, maxStackHeight, readBack_nil, popeqAligns, CKey.push,
        LedgerState.setField]
    · simp [hov, hb, hi, hf, hf', hwf, hn, hj32, hkv, hget, immOf, ledgerOracle, Op.toR, AV.ofAligned, hkey, query,
        LedgerState.vm, VmState.init, runR, ROp.exec, ROp.stackReq, hst, VmState.push, VmState.pop,
        VmState.popU64, VmState.popCell, VmState.pushNew, idxWalk, idxOne, insLoop, Cache.visit, CTree.visit,
        Cache.get, CTree.get, Cache.contains, CTree.contains, Cache.keyFor, insCache, assocGet, assocSet,
        AV.toU8, AV.toU64, AV.ofU64, SV.asCell, maxStackHeight, readBack_nil, popeqAligns, CKey.push,
        LedgerState.setField]

/-- `(← mp.lookup k).read`: the value of the counter stored for `kv`; the
    ledger is unchanged. -/
theorem Map.counter_read_spec (mp : Map κ Counter) (a : List Zkir.AlignAtom) (n : Nat)
    (hpath : mp.path = [fieldKey mp.index]) (hst : σ.state = .array fields)
    (hf : fields[mp.index]? = some (.map m)) (hb : mp.index < 256) (hwf : σ.WF)
    (hk : Expr.evalList p env (Value.toExprs k) = some ks) (hkv : AV.ofFields (alignOf κ) ks = some kv)
    (hget : assocGet kv m = some (.cell ⟨a, [n]⟩)) (hn : n < 2 ^ 64) :
    ∃ req, (emitted (((mp.lookup k).run {}).1 : Counter).read).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some ([Fr.ofNat n], σ) := by
  have he : (((mp.lookup k).run {}).1 : Counter).read = ledgerRead Uint64 (fun es =>
      [.dup 0, .idx false false (mp.path ++ [(⟨alignOf κ, Value.toExprs k⟩ : Aligned Expr)]),
       .popeq true [.bytes 8] es]) := rfl
  rw [he, emitted_ledgerRead, hpath]
  rw [evalList_eq_mapM] at hk
  refine ⟨[.dup 0, .idx false false [⟨[.bytes 1], [Fr.ofInt mp.index]⟩, ⟨alignOf κ, ks⟩], .popeq true [.bytes 8] []],
    ?_, ?_⟩
  · simp [Exec.request, Op.mapM, Aligned.mapM, hk, Exec.blank, fieldKey, Expr.eval, mapM_eval_readVars]
  · have hkey := ofAligned_byteKey hb
    simp only [AV.ofAligned] at hkey
    rw [LedgerState.WF] at hwf
    have hi := lt_of_getElem? hf
    have hf' := getElem_of_getElem? hf
    simp [hb, hi, hf, hf', hwf, hkv, hget, ledgerOracle, Op.toR, AV.ofAligned, hkey, query, LedgerState.vm,
      VmState.init, runR, ROp.exec, ROp.stackReq, hst, VmState.push, VmState.pop, VmState.popCell, idxWalk, idxOne,
      Cache.visit, CTree.visit, assocGet, assocSet, AV.toU8, SV.asCell, maxStackHeight, popeqAligns, CKey.push]
    cases σ; simp_all [readBack_cons, readBack_nil, fieldsOf_u64]

end

end Damp.Ledger
