/-
More of `Damp/Lang/Ledger.lean` against the VM model, beyond `Nested.lean`
and `MerkleSpec.lean`:

* a `Set` inside a `Map` (`(← mp.lookup k)`, path `[fieldKey i, k]`, the entry
  for `kv` holding `.map m₂`): `Map.set_insert_spec`, `Map.set_remove_spec`,
  `Map.set_member_spec`, `Map.set_size_spec`;
* `MerkleTree.insertHashIndex` (and `insertIndex x i`, which is
  `insertHashIndex (leafHash x) i` by definition): the leaf at index `i`, and
  the first free index raised to `i + 1` if it was below
  (`MerkleTree.insertHashIndex_spec`); out of range, the request fails
  (`MerkleTree.insertHashIndex_full`).

As in the other files, the top-level field `i` is below 256, the state is
well formed, and keys evaluate to `ks` and reach the VM as `kv`.
-/
import Damp.Proofs.Ledger.Nested
import Damp.Proofs.Ledger.MerkleSpec

namespace Damp.Ledger
open Damp.IR Damp.Impact

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

section
variable {κ : Type} [Value κ] (H : Hooks) (p : Zkir.Prims) (env : Env) (σ : LedgerState)
  (fields : List SV) (m : List (AV × SV)) (k : κ) (ks : List Fr) (kv : AV)

/-! ## A set inside a map -/

/-- The set `(← mp.lookup k)` names. -/
theorem Map.lookup_set_run {α : Type} [Value α] (mp : Map κ (Set α)) (s : Build) :
    (mp.lookup k).run s = ({ index := mp.index, path := mp.path ++ [⟨alignOf κ, Value.toExprs k⟩] }, s) := rfl

section MapSet
variable {α : Type} [Value α] (m₂ : List (AV × SV)) (x : α) (xs : List Fr) (xv : AV)

/-- `(← mp.lookup k).insert x`: the set stored for `kv` gets `xv` (against
    null); the outer map keeps its other entries. -/
theorem Map.set_insert_spec (mp : Map κ (Set α))
    (hpath : mp.path = [fieldKey mp.index]) (hst : σ.state = .array fields)
    (hf : fields[mp.index]? = some (.map m)) (hb : mp.index < 256) (hwf : σ.WF)
    (hk : Expr.evalList p env (Value.toExprs k) = some ks) (hkv : AV.ofFields (alignOf κ) ks = some kv)
    (hget : assocGet kv m = some (.map m₂))
    (hx : Expr.evalList p env (Value.toExprs x) = some xs) (hxv : AV.ofFields (alignOf α) xs = some xv) :
    ∃ req, (emitted ((((mp.lookup k).run {}).1 : Set α).insert x)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ =
        some ([], σ.setField mp.index (.map (assocSet kv (.map (assocSet xv .null m₂)) m))) := by
  have he : emitted ((((mp.lookup k).run {}).1 : Set α).insert x) =
      some [.idx false true (mp.path ++ [⟨alignOf κ, Value.toExprs k⟩]), .push false ⟨alignOf α, Value.toExprs x⟩,
        .pushNull true, .ins false 1,
        .ins true (mp.path ++ [(⟨alignOf κ, Value.toExprs k⟩ : Aligned Expr)]).length] := rfl
  rw [he, hpath]
  rw [evalList_eq_mapM] at hk hx
  refine ⟨[.idx false true [⟨[.bytes 1], [Fr.ofInt mp.index]⟩, ⟨alignOf κ, ks⟩], .push false ⟨alignOf α, xs⟩,
    .pushNull true, .ins false 1, .ins true 2], ?_, ?_⟩
  · simp [Exec.request, Op.mapM, Aligned.mapM, hk, hx, Exec.blank, fieldKey, Expr.eval]
  · have hkey := ofAligned_byteKey hb
    simp only [AV.ofAligned] at hkey
    rw [LedgerState.WF] at hwf
    have hi := lt_of_getElem? hf
    have hf' := getElem_of_getElem? hf
    vm_simp [hb, hkey, hkv, hxv, hget, hwf, hst, hi, hf, hf', LedgerState.setField]

/-- `(← mp.lookup k).remove x`: `xv` is removed from the set stored for `kv`. -/
theorem Map.set_remove_spec (mp : Map κ (Set α))
    (hpath : mp.path = [fieldKey mp.index]) (hst : σ.state = .array fields)
    (hf : fields[mp.index]? = some (.map m)) (hb : mp.index < 256) (hwf : σ.WF)
    (hk : Expr.evalList p env (Value.toExprs k) = some ks) (hkv : AV.ofFields (alignOf κ) ks = some kv)
    (hget : assocGet kv m = some (.map m₂))
    (hx : Expr.evalList p env (Value.toExprs x) = some xs) (hxv : AV.ofFields (alignOf α) xs = some xv) :
    ∃ req, (emitted ((((mp.lookup k).run {}).1 : Set α).remove x)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ =
        some ([], σ.setField mp.index (.map (assocSet kv (.map (assocErase xv m₂)) m))) := by
  have he : emitted ((((mp.lookup k).run {}).1 : Set α).remove x) =
      some [.idx false true (mp.path ++ [⟨alignOf κ, Value.toExprs k⟩]), .push false ⟨alignOf α, Value.toExprs x⟩,
        .rem false, .ins true (mp.path ++ [(⟨alignOf κ, Value.toExprs k⟩ : Aligned Expr)]).length] := rfl
  rw [he, hpath]
  rw [evalList_eq_mapM] at hk hx
  refine ⟨[.idx false true [⟨[.bytes 1], [Fr.ofInt mp.index]⟩, ⟨alignOf κ, ks⟩], .push false ⟨alignOf α, xs⟩,
    .rem false, .ins true 2], ?_, ?_⟩
  · simp [Exec.request, Op.mapM, Aligned.mapM, hk, hx, Exec.blank, fieldKey, Expr.eval]
  · have hkey := ofAligned_byteKey hb
    simp only [AV.ofAligned] at hkey
    rw [LedgerState.WF] at hwf
    have hi := lt_of_getElem? hf
    have hf' := getElem_of_getElem? hf
    vm_simp [hb, hkey, hkv, hxv, hget, hwf, hst, hi, hf, hf', LedgerState.setField]

/-- `(← mp.lookup k).member x`: whether the set stored for `kv` holds `xv`;
    the ledger is unchanged. -/
theorem Map.set_member_spec (mp : Map κ (Set α))
    (hpath : mp.path = [fieldKey mp.index]) (hst : σ.state = .array fields)
    (hf : fields[mp.index]? = some (.map m)) (hb : mp.index < 256) (hwf : σ.WF)
    (hk : Expr.evalList p env (Value.toExprs k) = some ks) (hkv : AV.ofFields (alignOf κ) ks = some kv)
    (hget : assocGet kv m = some (.map m₂))
    (hx : Expr.evalList p env (Value.toExprs x) = some xs) (hxv : AV.ofFields (alignOf α) xs = some xv) :
    ∃ req, (emitted ((((mp.lookup k).run {}).1 : Set α).member x)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some ([Fr.ofBool (assocGet xv m₂).isSome], σ) := by
  have he : (((mp.lookup k).run {}).1 : Set α).member x = ledgerRead Boolean (fun es =>
      [.dup 0, .idx false false (mp.path ++ [⟨alignOf κ, Value.toExprs k⟩]), .push false ⟨alignOf α, Value.toExprs x⟩,
       .member, .popeq true [.bytes 1] es]) := rfl
  rw [he, emitted_ledgerRead, hpath]
  rw [evalList_eq_mapM] at hk hx
  refine ⟨[.dup 0, .idx false false [⟨[.bytes 1], [Fr.ofInt mp.index]⟩, ⟨alignOf κ, ks⟩],
    .push false ⟨alignOf α, xs⟩, .member, .popeq true [.bytes 1] []], ?_, ?_⟩
  · simp [Exec.request, Op.mapM, Aligned.mapM, hk, hx, Exec.blank, fieldKey, Expr.eval, mapM_eval_readVars]
  · have hkey := ofAligned_byteKey hb
    simp only [AV.ofAligned] at hkey
    rw [LedgerState.WF] at hwf
    have hi := lt_of_getElem? hf
    have hf' := getElem_of_getElem? hf
    obtain ⟨ctx, eff, st⟩ := σ
    simp only at hst hwf ⊢
    subst hst
    have hbool := fieldsOf_bool (assocGet xv m₂).isSome
    vm_simp [hb, hkey, hkv, hxv, hget, hwf, hi, hf, hf', readBack_cons, AV.ofBool, hbool]

omit [Value α] in
/-- `(← mp.lookup k).size`: the number of elements of the set stored for
    `kv`; the ledger is unchanged. -/
theorem Map.set_size_spec {α : Type} [Value α] (mp : Map κ (Set α))
    (hpath : mp.path = [fieldKey mp.index]) (hst : σ.state = .array fields)
    (hf : fields[mp.index]? = some (.map m)) (hb : mp.index < 256) (hwf : σ.WF)
    (hk : Expr.evalList p env (Value.toExprs k) = some ks) (hkv : AV.ofFields (alignOf κ) ks = some kv)
    (hget : assocGet kv m = some (.map m₂)) (hm₂ : m₂.length < 2 ^ 64) :
    ∃ req, (emitted (((mp.lookup k).run {}).1 : Set α).size).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some ([Fr.ofNat m₂.length], σ) := by
  have he : (((mp.lookup k).run {}).1 : Set α).size = ledgerRead Uint64 (fun es =>
      [.dup 0, .idx false false (mp.path ++ [⟨alignOf κ, Value.toExprs k⟩]), .size, .popeq true [.bytes 8] es]) := rfl
  rw [he, emitted_ledgerRead, hpath]
  rw [evalList_eq_mapM] at hk
  refine ⟨[.dup 0, .idx false false [⟨[.bytes 1], [Fr.ofInt mp.index]⟩, ⟨alignOf κ, ks⟩], .size,
    .popeq true [.bytes 8] []], ?_, ?_⟩
  · simp [Exec.request, Op.mapM, Aligned.mapM, hk, Exec.blank, fieldKey, Expr.eval, mapM_eval_readVars]
  · have hkey := ofAligned_byteKey hb
    simp only [AV.ofAligned] at hkey
    rw [LedgerState.WF] at hwf
    have hi := lt_of_getElem? hf
    have hf' := getElem_of_getElem? hf
    obtain ⟨ctx, eff, st⟩ := σ
    simp only at hst hwf ⊢
    subst hst
    vm_simp [hb, hkey, hkv, hget, hwf, hi, hf, hf', readBack_cons, AV.ofU64, fieldsOf_u64 _ hm₂]

end MapSet

/-! ## `MerkleTree.insertHashIndex` -/

variable {α : Type} [Value α] {d : Nat}

theorem ofFields_u64_fr (j : Fr) (hj : j.val < 2 ^ 64) : AV.ofFields [.bytes 8] [j] = some ⟨[.bytes 8], [j.val]⟩ := by
  have : ¬ (8 > 31) := by decide
  simp [AV.ofFields, atomWidth, atomOfFields, atomFits, this, hj]

/-- **`insertHashIndex h i`** (and `insertIndex x i`, which is
    `insertHashIndex (leafHash x) i`): the hash `x` the VM stores for `h`
    becomes the leaf at index `j` (what `i` evaluates to; `j < 2^d`, and
    `j + 1 < 2^64` for the VM's `addi`), and the first free index `ff` becomes
    `j + 1` if it was below, else stays as it was. -/
theorem MerkleTree.insertHashIndex_spec (t : MerkleTree d α) (h : Bytes 32) (hs : List Fr) (x : Nat)
    (i : Uint64) (j : Fr) (leaves : List (Nat × Nat)) (a : List Zkir.AlignAtom) (ff : Nat)
    (hpath : t.path = [fieldKey t.index]) (hst : σ.state = .array fields)
    (hf : fields[t.index]? = some (.array [.bmt d leaves, .cell ⟨a, [ff]⟩])) (hb : t.index < 256) (hwf : σ.WF)
    (hff : ff < 2 ^ 64) (hj : Expr.eval p env i.expr = some j) (hjd : ¬ (d < 64 ∧ 2 ^ d ≤ j.val))
    (hj64 : j.val + 1 < 2 ^ 64)
    (hh : Expr.evalList p env (Value.toExprs h) = some hs) (hx : AV.ofFields [.bytes 32] hs = some ⟨[.bytes 32], [x]⟩) :
    ∃ req, (emitted (t.insertHashIndex h i)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some ([], σ.setField t.index
        (.array [.bmt d (assocSet j.val x leaves),
          if ff < j.val + 1 then .cell (AV.ofU64 (j.val + 1)) else .cell ⟨a, [ff]⟩])) := by
  have he : emitted (t.insertHashIndex h i) = some [.idx false true t.path, .idx false true [fieldKey 0],
      .push false ⟨[.bytes 8], [i.expr]⟩, .push true ⟨alignOf (Bytes 32), Value.toExprs h⟩, .ins false 2,
      .idx false true [fieldKey 1], .push false ⟨[.bytes 8], [i.expr]⟩, .addi (.const 1), .dup 1, .dup 1, .lt,
      .branch 2, .pop, .jmp 2, .swap 0, .pop, .ins false 1, .ins true t.path.length] := rfl
  rw [he, hpath]
  rw [evalList_eq_mapM] at hh
  refine ⟨[.idx false true [⟨[.bytes 1], [Fr.ofInt t.index]⟩], .idx false true [⟨[.bytes 1], [Fr.ofInt 0]⟩],
      .push false ⟨[.bytes 8], [j]⟩, .push true ⟨[.bytes 32], hs⟩, .ins false 2,
      .idx false true [⟨[.bytes 1], [Fr.ofInt 1]⟩], .push false ⟨[.bytes 8], [j]⟩, .addi (Fr.ofInt 1),
      .dup 1, .dup 1, .lt, .branch 2, .pop, .jmp 2, .swap 0, .pop, .ins false 1, .ins true 1], ?_, ?_⟩
  · simp [Exec.request, Op.mapM, Aligned.mapM, hh, hj, Exec.blank, fieldKey, Expr.eval]
    rfl
  · have hk := ofAligned_byteKey hb
    have hk0 := ofFields_key0
    have hk1 := ofFields_key1
    simp only [AV.ofAligned] at hk
    rw [LedgerState.WF] at hwf
    have hi := lt_of_getElem? hf
    have hf' := getElem_of_getElem? hf
    have hx256 := lt_of_ofFields_bytes32 hx
    have hjj : j.val < 2 ^ 64 := by omega
    have hjv := ofFields_u64_fr j hjj
    by_cases hlt : ff < j.val + 1
    · vm_simp [hb, hk, hk0, hk1, hx, hjv, hwf, hst, hi, hf, hf', immOf, frOfInt_val_one, hff, hjj, hj64, hjd,
        AV.toHash, hx256, AV.ofU64, AV.ofBool, hlt, List.set, LedgerState.setField]
    · vm_simp [hb, hk, hk0, hk1, hx, hjv, hwf, hst, hi, hf, hf', immOf, frOfInt_val_one, hff, hjj, hj64, hjd,
        AV.toHash, hx256, AV.ofU64, AV.ofBool, hlt, List.set, LedgerState.setField]

/-- `insertHashIndex h i` out of range (`d < 64`, `2^d ≤ j`): the request fails. -/
theorem MerkleTree.insertHashIndex_full (t : MerkleTree d α) (h : Bytes 32) (hs : List Fr) (x : Nat)
    (i : Uint64) (j : Fr) (leaves : List (Nat × Nat)) (a : List Zkir.AlignAtom) (ff : Nat)
    (hpath : t.path = [fieldKey t.index]) (hst : σ.state = .array fields)
    (hf : fields[t.index]? = some (.array [.bmt d leaves, .cell ⟨a, [ff]⟩])) (hb : t.index < 256)
    (hj : Expr.eval p env i.expr = some j) (hj64 : j.val < 2 ^ 64) (hd : d < 64) (hjd : 2 ^ d ≤ j.val)
    (hh : Expr.evalList p env (Value.toExprs h) = some hs) (hx : AV.ofFields [.bytes 32] hs = some ⟨[.bytes 32], [x]⟩) :
    ∃ req, (emitted (t.insertHashIndex h i)).bind (Exec.request p env) = some req ∧ ledgerOracle H req σ = none := by
  have he : emitted (t.insertHashIndex h i) = some [.idx false true t.path, .idx false true [fieldKey 0],
      .push false ⟨[.bytes 8], [i.expr]⟩, .push true ⟨alignOf (Bytes 32), Value.toExprs h⟩, .ins false 2,
      .idx false true [fieldKey 1], .push false ⟨[.bytes 8], [i.expr]⟩, .addi (.const 1), .dup 1, .dup 1, .lt,
      .branch 2, .pop, .jmp 2, .swap 0, .pop, .ins false 1, .ins true t.path.length] := rfl
  rw [he, hpath]
  rw [evalList_eq_mapM] at hh
  refine ⟨[.idx false true [⟨[.bytes 1], [Fr.ofInt t.index]⟩], .idx false true [⟨[.bytes 1], [Fr.ofInt 0]⟩],
      .push false ⟨[.bytes 8], [j]⟩, .push true ⟨[.bytes 32], hs⟩, .ins false 2,
      .idx false true [⟨[.bytes 1], [Fr.ofInt 1]⟩], .push false ⟨[.bytes 8], [j]⟩, .addi (Fr.ofInt 1),
      .dup 1, .dup 1, .lt, .branch 2, .pop, .jmp 2, .swap 0, .pop, .ins false 1, .ins true 1], ?_, ?_⟩
  · simp [Exec.request, Op.mapM, Aligned.mapM, hh, hj, Exec.blank, fieldKey, Expr.eval]
    rfl
  · have hk := ofAligned_byteKey hb
    have hk0 := ofFields_key0
    have hk1 := ofFields_key1
    simp only [AV.ofAligned] at hk
    have hi := lt_of_getElem? hf
    have hf' := getElem_of_getElem? hf
    have hjv := ofFields_u64_fr j hj64
    vm_simp [hb, hk, hk0, hk1, hx, hjv, hst, hi, hf, hf', immOf, frOfInt_val_one, hj64, hd, hjd, AV.toHash]

/-! ## Two levels down: a counter in a map in a map -/

section Deep
variable {κ₂ : Type} [Value κ₂] (m₂ : List (AV × SV)) (k₂ : κ₂) (ks₂ : List Fr) (kv₂ : AV)

/-- The counter `(← (← mp.lookup k).lookup k₂)` names: path `[fieldKey i, k, k₂]`. -/
theorem Map.lookup_lookup_counter_run (mp : Map κ (Map κ₂ Counter)) :
    ((((mp.lookup k).run {}).1 : Map κ₂ Counter).lookup k₂).run {} =
      ({ index := mp.index, path := mp.path ++ [⟨alignOf κ, Value.toExprs k⟩] ++ [⟨alignOf κ₂, Value.toExprs k₂⟩] }, {}) :=
  rfl

/-- `(← (← mp.lookup k).lookup k₂).increment amount`, a path of length 3: the
    counter stored for `kv₂` in the map stored for `kv` (holding `n`) becomes
    `n + j`, or the request fails on overflow; both maps keep their other
    entries. -/
theorem Map.map_counter_increment_spec (mp : Map κ (Map κ₂ Counter)) (a : List Zkir.AlignAtom) (n : Nat)
    (amount : Uint16) (j : Fr)
    (hpath : mp.path = [fieldKey mp.index]) (hst : σ.state = .array fields)
    (hf : fields[mp.index]? = some (.map m)) (hb : mp.index < 256) (hwf : σ.WF)
    (hk : Expr.evalList p env (Value.toExprs k) = some ks) (hkv : AV.ofFields (alignOf κ) ks = some kv)
    (hget : assocGet kv m = some (.map m₂))
    (hk₂ : Expr.evalList p env (Value.toExprs k₂) = some ks₂) (hkv₂ : AV.ofFields (alignOf κ₂) ks₂ = some kv₂)
    (hget₂ : assocGet kv₂ m₂ = some (.cell ⟨a, [n]⟩)) (hn : n < 2 ^ 64)
    (hj : Expr.eval p env amount.expr = some j) (hj32 : j.val < 2 ^ 32) :
    ∃ req, (emitted ((((((mp.lookup k).run {}).1 : Map κ₂ Counter).lookup k₂).run {}).1.increment amount)).bind
        (Exec.request p env) = some req ∧
      ledgerOracle H req σ =
        if n + j.val < 2 ^ 64 then
          some ([], σ.setField mp.index
            (.map (assocSet kv (.map (assocSet kv₂ (.cell (AV.ofU64 (n + j.val))) m₂)) m)))
        else none := by
  have he : emitted ((((((mp.lookup k).run {}).1 : Map κ₂ Counter).lookup k₂).run {}).1.increment amount) =
      some [.idx false true (mp.path ++ [⟨alignOf κ, Value.toExprs k⟩] ++ [⟨alignOf κ₂, Value.toExprs k₂⟩]),
        .addi amount.expr,
        .ins true (mp.path ++ [(⟨alignOf κ, Value.toExprs k⟩ : Aligned Expr)] ++
          [(⟨alignOf κ₂, Value.toExprs k₂⟩ : Aligned Expr)]).length] :=
    rfl
  rw [he, hpath]
  rw [evalList_eq_mapM] at hk hk₂
  refine ⟨[.idx false true [⟨[.bytes 1], [Fr.ofInt mp.index]⟩, ⟨alignOf κ, ks⟩, ⟨alignOf κ₂, ks₂⟩], .addi j,
    .ins true 3], ?_, ?_⟩
  · simp [Exec.request, Op.mapM, Aligned.mapM, hk, hk₂, hj, Exec.blank, fieldKey, Expr.eval]
  · have hkey := ofAligned_byteKey hb
    simp only [AV.ofAligned] at hkey
    rw [LedgerState.WF] at hwf
    have hi := lt_of_getElem? hf
    have hf' := getElem_of_getElem? hf
    by_cases hov : n + j.val < 2 ^ 64
    · vm_simp [hov, hb, hkey, hkv, hkv₂, hget, hget₂, hwf, hst, hi, hf, hf', hn, hj32, immOf, AV.ofU64,
        LedgerState.setField]
    · vm_simp [hov, hb, hkey, hkv, hkv₂, hget, hget₂, hwf, hst, hi, hf, hf', hn, hj32, immOf, AV.ofU64,
        LedgerState.setField]

end Deep

end

end Damp.Ledger
