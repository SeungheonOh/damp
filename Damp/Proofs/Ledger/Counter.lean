/-
`Counter` (`Damp/Lang/Ledger.lean`) against the VM model, for a top-level
counter (`c.path = [fieldKey c.index]`, the default path).

A counter's field holds a cell with one atom `n < 2^64` (the VM reads it as a
`u64`; it does not look at the cell's alignment, which Damp sets to
`[bytes 8]`). The VM's arithmetic is `u64` with overflow an error
(`checked_add`/`checked_sub` in `vm.rs`), and the result is stored aligned
`[bytes 8]`. An increment or decrement amount reaches the VM as a `u32`
immediate, so it is assumed below `2^32` (a `Uint16` is).
-/
import Damp.Proofs.Ledger.Cell

namespace Damp.Ledger
open Damp.IR Damp.Impact

set_option linter.unusedSimpArgs false

section
variable (H : Hooks) (c : Counter) (p : Zkir.Prims) (env : Env) (σ : LedgerState) (fields : List SV)
  (a : List Zkir.AlignAtom) (n : Nat)

theorem fieldsOf_u64 (hn : n < 2 ^ 64) : fieldsOf [.bytes 8] [n] = some [Fr.ofNat n] := by
  have hm : n < Fr.modulus := Nat.lt_trans hn modulus_gt_2_64
  simp [fieldsOf, fieldsOfAtom, hm, Fr.ofNat, Nat.mod_eq_of_lt hm]

theorem fieldsOf_bool (b : Bool) : fieldsOf [.bytes 1] [if b then 1 else 0] = some [Fr.ofBool b] := by
  cases b
  · simp only [fieldsOf, fieldsOfAtom]; simp; exact ⟨by decide, Fr.ext rfl⟩
  · simp only [fieldsOf, fieldsOfAtom]; simp; exact ⟨by decide, Fr.ext rfl⟩

theorem lt_of_getElem? {l : List SV} {i : Nat} {x : SV} (h : l[i]? = some x) : i < l.length := by
  rcases Nat.lt_or_ge i l.length with h' | h'
  · exact h'
  · simp [List.getElem?_eq_none h'] at h

theorem getElem_of_getElem? {l : List SV} {i : Nat} {x : SV} (h : l[i]? = some x) :
    l[i]'(lt_of_getElem? h) = x := by
  rw [List.getElem?_eq_getElem (lt_of_getElem? h)] at h
  exact Option.some.inj h

/-- `Counter.increment`: the counter becomes `n + k`, stored as a `u64`, or the
    request fails if that overflows 64 bits. Nothing is read. -/
theorem Counter.increment_spec (amount : Uint16) (k : Fr)
    (hpath : c.path = [fieldKey c.index]) (hst : σ.state = .array fields)
    (hf : fields[c.index]? = some (.cell ⟨a, [n]⟩)) (hn : n < 2 ^ 64) (hb : c.index < 256) (hwf : σ.WF)
    (hk : Expr.eval p env amount.expr = some k) (hk32 : k.val < 2 ^ 32) :
    ∃ req, (emitted (c.increment amount)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ =
        if n + k.val < 2 ^ 64 then some ([], σ.setField c.index (.cell (AV.ofU64 (n + k.val)))) else none := by
  have he : emitted (c.increment amount) = some [.idx false true c.path, .addi amount.expr, .ins true c.path.length] := rfl
  rw [he, hpath]
  refine ⟨[.idx false true [⟨[.bytes 1], [Fr.ofInt c.index]⟩], .addi k, .ins true 1], ?_, ?_⟩
  · simp [Exec.request, Op.mapM, Aligned.mapM, hk, Exec.blank, fieldKey, Expr.eval]
  · have hkey := ofAligned_byteKey hb
    simp only [AV.ofAligned] at hkey
    rw [LedgerState.WF] at hwf
    have hi := lt_of_getElem? hf
    have hf' := getElem_of_getElem? hf
    by_cases hov : n + k.val < 2 ^ 64
    · simp [hov, hb, hi, hf, hf', hwf, hn, hk32, immOf, ledgerOracle, Op.toR, AV.ofAligned, hkey, query,
        LedgerState.vm, VmState.init, runR, ROp.exec, ROp.stackReq, hst, VmState.push, VmState.pop,
        VmState.popU64, VmState.popCell, VmState.pushNew, idxWalk, idxOne, insLoop, Cache.visit, CTree.visit,
        Cache.get, CTree.get, Cache.contains, CTree.contains, Cache.keyFor, insCache, assocGet, assocSet,
        AV.toU8, AV.toU64, AV.ofU64, SV.asCell, maxStackHeight, readBack_nil, popeqAligns, CKey.push,
        LedgerState.setField]
    · simp [hov, hb, hi, hf, hf', hwf, hn, hk32, immOf, ledgerOracle, Op.toR, AV.ofAligned, hkey, query,
        LedgerState.vm, VmState.init, runR, ROp.exec, ROp.stackReq, hst, VmState.push, VmState.pop,
        VmState.popU64, VmState.popCell, VmState.pushNew, idxWalk, idxOne, insLoop, Cache.visit, CTree.visit,
        Cache.get, CTree.get, Cache.contains, CTree.contains, Cache.keyFor, insCache, assocGet, assocSet,
        AV.toU8, AV.toU64, AV.ofU64, SV.asCell, maxStackHeight, readBack_nil, popeqAligns, CKey.push,
        LedgerState.setField]

/-- `Counter.decrement`: the counter becomes `n - k`, or the request fails if
    `k > n` (the VM's `subi` does not go below zero). Nothing is read. -/
theorem Counter.decrement_spec (amount : Uint16) (k : Fr)
    (hpath : c.path = [fieldKey c.index]) (hst : σ.state = .array fields)
    (hf : fields[c.index]? = some (.cell ⟨a, [n]⟩)) (hn : n < 2 ^ 64) (hb : c.index < 256) (hwf : σ.WF)
    (hk : Expr.eval p env amount.expr = some k) (hk32 : k.val < 2 ^ 32) :
    ∃ req, (emitted (c.decrement amount)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ =
        if k.val ≤ n then some ([], σ.setField c.index (.cell (AV.ofU64 (n - k.val)))) else none := by
  have he : emitted (c.decrement amount) = some [.idx false true c.path, .subi amount.expr, .ins true c.path.length] := rfl
  rw [he, hpath]
  refine ⟨[.idx false true [⟨[.bytes 1], [Fr.ofInt c.index]⟩], .subi k, .ins true 1], ?_, ?_⟩
  · simp [Exec.request, Op.mapM, Aligned.mapM, hk, Exec.blank, fieldKey, Expr.eval]
  · have hkey := ofAligned_byteKey hb
    simp only [AV.ofAligned] at hkey
    rw [LedgerState.WF] at hwf
    have hi := lt_of_getElem? hf
    have hf' := getElem_of_getElem? hf
    by_cases hle : k.val ≤ n
    · simp [hle, hb, hi, hf, hf', hwf, hn, hk32, immOf, ledgerOracle, Op.toR, AV.ofAligned, hkey, query,
        LedgerState.vm, VmState.init, runR, ROp.exec, ROp.stackReq, hst, VmState.push, VmState.pop,
        VmState.popU64, VmState.popCell, VmState.pushNew, idxWalk, idxOne, insLoop, Cache.visit, CTree.visit,
        Cache.get, CTree.get, Cache.contains, CTree.contains, Cache.keyFor, insCache, assocGet, assocSet,
        AV.toU8, AV.toU64, AV.ofU64, SV.asCell, maxStackHeight, readBack_nil, popeqAligns, CKey.push,
        LedgerState.setField]
    · simp [hle, hb, hi, hf, hf', hwf, hn, hk32, immOf, ledgerOracle, Op.toR, AV.ofAligned, hkey, query,
        LedgerState.vm, VmState.init, runR, ROp.exec, ROp.stackReq, hst, VmState.push, VmState.pop,
        VmState.popU64, VmState.popCell, VmState.pushNew, idxWalk, idxOne, insLoop, Cache.visit, CTree.visit,
        Cache.get, CTree.get, Cache.contains, CTree.contains, Cache.keyFor, insCache, assocGet, assocSet,
        AV.toU8, AV.toU64, AV.ofU64, SV.asCell, maxStackHeight, readBack_nil, popeqAligns, CKey.push,
        LedgerState.setField]

/-- `Counter.read`: the counter's value, as one field element; the ledger is unchanged. -/
theorem Counter.read_spec
    (hpath : c.path = [fieldKey c.index]) (hst : σ.state = .array fields)
    (hf : fields[c.index]? = some (.cell ⟨a, [n]⟩)) (hn : n < 2 ^ 64) (hb : c.index < 256) (hwf : σ.WF) :
    ∃ req, (emitted c.read).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some ([Fr.ofNat n], σ) := by
  have he : c.read = ledgerRead Uint64 (fun es =>
      [.dup 0, .idx false false c.path, .popeq true [.bytes 8] es]) := rfl
  rw [he, emitted_ledgerRead, hpath]
  refine ⟨[.dup 0, .idx false false [⟨[.bytes 1], [Fr.ofInt c.index]⟩], .popeq true [.bytes 8] []], ?_, ?_⟩
  · simp [Exec.request, Op.mapM, Aligned.mapM, Exec.blank, fieldKey, Expr.eval, mapM_eval_readVars]
  · have hkey := ofAligned_byteKey hb
    simp only [AV.ofAligned] at hkey
    rw [LedgerState.WF] at hwf
    have hi := lt_of_getElem? hf
    have hf' := getElem_of_getElem? hf
    simp [hb, hi, hf, hwf, ledgerOracle, Op.toR, AV.ofAligned, hkey, query, LedgerState.vm, VmState.init,
      runR, ROp.exec, ROp.stackReq, hst, VmState.push, VmState.pop, VmState.popCell, idxWalk, idxOne,
      Cache.visit, CTree.visit, assocGet, assocSet, AV.toU8, SV.asCell, maxStackHeight, popeqAligns, CKey.push]
    cases σ; simp_all [readBack_cons, readBack_nil, fieldsOf_u64]

/-- `Counter.lessThan t`: whether the counter is below `t`, as a field
    element (0 or 1); the ledger is unchanged. The threshold is a `Uint64`, so
    below `2^64`. -/
theorem Counter.lessThan_spec (threshold : Uint64) (t : Fr)
    (hpath : c.path = [fieldKey c.index]) (hst : σ.state = .array fields)
    (hf : fields[c.index]? = some (.cell ⟨a, [n]⟩)) (hn : n < 2 ^ 64) (hb : c.index < 256) (hwf : σ.WF)
    (ht : Expr.eval p env threshold.expr = some t) (ht64 : t.val < 2 ^ 64) :
    ∃ req, (emitted (c.lessThan threshold)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some ([Fr.ofBool (decide (n < t.val))], σ) := by
  have he : c.lessThan threshold = ledgerRead Boolean (fun es =>
      [.dup 0, .idx false false c.path, .push false ⟨[.bytes 8], [threshold.expr]⟩, .lt,
       .popeq true [.bytes 1] es]) := rfl
  rw [he, emitted_ledgerRead, hpath]
  refine ⟨[.dup 0, .idx false false [⟨[.bytes 1], [Fr.ofInt c.index]⟩], .push false ⟨[.bytes 8], [t]⟩, .lt,
    .popeq true [.bytes 1] []], ?_, ?_⟩
  · simp [Exec.request, Op.mapM, Aligned.mapM, Exec.blank, fieldKey, Expr.eval, mapM_eval_readVars, ht]
  · have hkey := ofAligned_byteKey hb
    simp only [AV.ofAligned] at hkey
    rw [LedgerState.WF] at hwf
    have hi := lt_of_getElem? hf
    have hf' := getElem_of_getElem? hf
    have hval : (Fr.ofInt (c.index : Int)).val = c.index := Fr.ofInt_natCast_val (Nat.lt_trans hb (by decide))
    simp [hval, hb, hi, hf, hf', hwf, hn, ht64, ledgerOracle, Op.toR, AV.ofAligned, AV.ofFields, atomWidth, atomOfFields,
      atomFits, hkey, query, LedgerState.vm, VmState.init,
      runR, ROp.exec, ROp.stackReq, hst, VmState.push, VmState.pop, VmState.popCell, VmState.popU64,
      VmState.pushNew, idxWalk, idxOne, Cache.visit, CTree.visit, assocGet, assocSet, AV.toU8, AV.toU64,
      AV.ofBool, SV.asCell, maxStackHeight, popeqAligns, CKey.push]
    have hbool := fieldsOf_bool (decide (n < t.val))
    simp only [decide_eq_true_eq] at hbool
    cases σ; simp_all [readBack_cons, readBack_nil]

/-- `Counter.resetToDefault`: the counter becomes 0 (a `[bytes 8]` cell),
    whatever the field held. -/
theorem Counter.resetToDefault_spec
    (hpath : c.path = [fieldKey c.index]) (hst : σ.state = .array fields)
    (hi : c.index < fields.length) (hb : c.index < 256) (hwf : σ.WF) :
    ∃ req, (emitted c.resetToDefault).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some ([], σ.setField c.index (.cell (AV.ofU64 0))) := by
  have he : emitted c.resetToDefault = some (resetOps c.path Counter.initial) := rfl
  rw [he, hpath]
  refine ⟨[.push false ⟨[.bytes 1], [Fr.ofInt c.index]⟩, .pushState true (.cell ⟨[.bytes 8], [0]⟩),
    .ins false 1], ?_, ?_⟩
  · simp [resetOps, insCached, Counter.initial, Exec.request, Op.mapM, StateLit.mapM, Aligned.mapM,
      Exec.blank, fieldKey, Expr.eval]
    rfl
  · have hkey := ofAligned_byteKey hb
    simp only [AV.ofAligned] at hkey
    rw [LedgerState.WF] at hwf
    have hval : (Fr.ofInt (c.index : Int)).val = c.index := Fr.ofInt_natCast_val (Nat.lt_trans hb (by decide))
    simp [hval, hb, hi, hwf, ledgerOracle, Op.toR, SV.ofLit, AV.ofAligned, AV.ofFields, atomWidth, atomOfFields,
      atomFits, hkey, query, LedgerState.vm, VmState.init, runR, ROp.exec, ROp.stackReq, hst, VmState.push,
      VmState.pop, insLoop, Cache.get, Cache.keyFor, insCache, AV.toU8, SV.asCell, maxStackHeight,
      readBack_nil, popeqAligns, LedgerState.setField, CTree.get, Cache.contains, CKey.push, AV.ofU64,
      Fr.val_zero]

/-- Increment by `k`, then read: the read returns `n + k` (when that does not
    overflow 64 bits). -/
theorem Counter.increment_read (amount : Uint16) (k : Fr)
    (hpath : c.path = [fieldKey c.index]) (hst : σ.state = .array fields)
    (hf : fields[c.index]? = some (.cell ⟨a, [n]⟩)) (hn : n < 2 ^ 64) (hb : c.index < 256) (hwf : σ.WF)
    (hk : Expr.eval p env amount.expr = some k) (hk32 : k.val < 2 ^ 32) (hov : n + k.val < 2 ^ 64)
    (env' : Env) :
    ∃ req₁ req₂ σ₁, (emitted (c.increment amount)).bind (Exec.request p env) = some req₁ ∧
      ledgerOracle H req₁ σ = some ([], σ₁) ∧
      (emitted c.read).bind (Exec.request p env') = some req₂ ∧
      ledgerOracle H req₂ σ₁ = some ([Fr.ofNat (n + k.val)], σ₁) := by
  obtain ⟨req₁, h1, h2⟩ := Counter.increment_spec H c p env σ fields a n amount k hpath hst hf hn hb hwf hk hk32
  simp only [hov, ite_true] at h2
  have hi := lt_of_getElem? hf
  have hst' : (σ.setField c.index (.cell (AV.ofU64 (n + k.val)))).state =
      .array (fields.set c.index (.cell (AV.ofU64 (n + k.val)))) := by
    simp [LedgerState.setField, hst]
  have hwf' : (σ.setField c.index (.cell (AV.ofU64 (n + k.val)))).WF := by
    simpa [LedgerState.WF, LedgerState.setField, hst] using hwf
  obtain ⟨req₂, h3, h4⟩ := Counter.read_spec H c p env' (σ.setField c.index (.cell (AV.ofU64 (n + k.val))))
    (fields.set c.index (.cell (AV.ofU64 (n + k.val)))) [.bytes 8] (n + k.val) hpath hst'
    (by simp [hi, AV.ofU64]) hov hb hwf'
  exact ⟨req₁, req₂, _, h1, h2, h3, h4⟩

end

end Damp.Ledger
