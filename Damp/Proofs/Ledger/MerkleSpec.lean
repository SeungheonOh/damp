/-
`MerkleTree` and `HistoricMerkleTree` (`Damp/Lang/Ledger.lean`) against the VM
model, for a top-level tree (`t.path = [fieldKey t.index]`, the default path).

A `MerkleTree d α` field holds `[tree, firstFree]`: a bounded Merkle tree of
height `d` (`.bmt d leaves`, its leaves as (index, 32-byte hash) pairs) and
the first free index, a `u64` cell. A `HistoricMerkleTree d α` also holds the
map of past roots (`[tree, firstFree, pastRoots]`, the roots as keys, null
values).

What is assumed about the hash. The VM model does not compute tree roots
itself: `root` asks the hook `H.root` (`Hooks`), so every theorem here holds
for any root function, stated with the value `H.root d leaves` it gives (and
that it is a cell of at most 64 serialized bytes, as a `[field]` cell is,
where `eq` compares it). Nothing is assumed about the hash (no collision
resistance): `checkRoot` is equality of roots, and what that says about the
leaves is not part of these theorems. With the real root (`merkleHooks`,
`Damp/Ledger/Merkle.lean`: the Poseidon `transientHash` of `Damp/Crypto`,
checked against the runtime by `test/semantics.sh`, over the leaf hashes
degraded to field elements) the `_merkle` corollaries state the results with
`merkleRootAt`. Leaves are stored as the 32-byte hashes they are given
(`insertHash`); `insert x` is `insertHash (leafHash x)` by definition.
-/
import Damp.Proofs.Ledger.Counter
import Damp.Ledger.Merkle

namespace Damp.Ledger
open Damp.IR Damp.Impact

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-! ## Facts about sizes and keys -/

theorem byteLen_le_32 {x : Nat} (hx : x < 2 ^ 256) : byteLen x ≤ 32 := by
  unfold byteLen
  split
  · omega
  · have : x.log2 < 256 := (Nat.log2_lt (by omega)).2 hx
    omega

/-- A `[field]` cell is at most 64 serialized bytes: `eq` compares it. -/
theorem fieldCell_size (y : Nat) (hy : y < 2 ^ 256) : (⟨[.field], [y]⟩ : AV).size ≤ 64 := by
  have h := byteLen_le_32 hy
  simp only [AV.size, atomSize, alignAtomSize, flaggedIntSize]
  repeat' split
  all_goals omega

theorem fr_lt_2_256 (y : Fr) : y.val < 2 ^ 256 := Nat.lt_trans y.isLt (by decide)

theorem ofFields_field (y : Fr) : AV.ofFields [.field] [y] = some ⟨[.field], [y.val]⟩ := by
  have h := byteLen_le_32 (fr_lt_2_256 y)
  simp [AV.ofFields, atomWidth, atomOfFields, atomFits]
  omega

theorem lt_of_ofFields_bytes32 {hs : List Fr} {x : Nat}
    (h : AV.ofFields [.bytes 32] hs = some ⟨[.bytes 32], [x]⟩) : x < 2 ^ 256 := by
  simp only [AV.ofFields] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i h2
      simp at h
      rw [h] at h2
      simpa [atomFits] using h2

theorem frOfInt_pow (d : Nat) (hd : d < 64) : (Fr.ofInt ((2 : Int) ^ d)).val = 2 ^ d := by
  have h1 : 2 ^ d < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hd
  have hm : 2 ^ d < Fr.modulus := Nat.lt_trans h1 modulus_gt_2_64
  have : ((2 : Int) ^ d) = ((2 ^ d : Nat) : Int) := by simp
  rw [this]; exact Fr.ofInt_natCast_val hm

/-- A `u64` operand `2^d` for `d < 64`. -/
theorem ofFields_pow (d : Nat) (hd : d < 64) :
    AV.ofFields [.bytes 8] [Fr.ofInt ((2 : Int) ^ d)] = some ⟨[.bytes 8], [2 ^ d]⟩ := by
  have h1 : 2 ^ d < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hd
  have hv := frOfInt_pow d hd
  have : ¬ (8 > 31) := by decide
  simp only [AV.ofFields, atomWidth, atomOfFields, atomFits]
  simp [this, hv, h1]

theorem digest_toExprs (r : MerkleTreeDigest) : Value.toExprs r = [r.field.expr] := rfl
theorem digest_align : (Value.shape MerkleTreeDigest).tys.map Ty.align = [.field] := rfl

section
variable {α : Type} [Value α] {d : Nat} (H : Hooks) (p : Zkir.Prims) (env : Env) (σ : LedgerState)
  (fields : List SV)

/-! ## `MerkleTree` -/

/-- `insertHash h` (and `insert x`, which is `insertHash (leafHash x)`): the
    hash `x` the VM stores for `h` becomes the leaf at the first free index
    `ff`, which advances by one. It needs a free index (`ff < 2^d`). -/
theorem MerkleTree.insertHash_spec (t : MerkleTree d α) (h : Bytes 32) (hs : List Fr) (x : Nat)
    (leaves : List (Nat × Nat)) (a : List Zkir.AlignAtom) (ff : Nat)
    (hpath : t.path = [fieldKey t.index]) (hst : σ.state = .array fields)
    (hf : fields[t.index]? = some (.array [.bmt d leaves, .cell ⟨a, [ff]⟩])) (hb : t.index < 256) (hwf : σ.WF)
    (hfree : ff < 2 ^ d) (hff : ff + 1 < 2 ^ 64)
    (hh : Expr.evalList p env (Value.toExprs h) = some hs) (hx : AV.ofFields [.bytes 32] hs = some ⟨[.bytes 32], [x]⟩) :
    ∃ req, (emitted (t.insertHash h)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some ([], σ.setField t.index
        (.array [.bmt d (assocSet ff x leaves), .cell (AV.ofU64 (ff + 1))])) := by
  have he : emitted (t.insertHash h) = some (MerkleTreeOps.insertAt t.path h [.ins true (t.path.length + 1)]) := rfl
  rw [he, hpath]
  rw [evalList_eq_mapM] at hh
  refine ⟨[.idx false true [⟨[.bytes 1], [Fr.ofInt t.index]⟩], .idx false true [⟨[.bytes 1], [Fr.ofInt 0]⟩],
      .dup 2, .idx false false [⟨[.bytes 1], [Fr.ofInt 1]⟩], .push true ⟨[.bytes 32], hs⟩, .ins false 1, .ins true 1,
      .idx false true [⟨[.bytes 1], [Fr.ofInt 1]⟩], .addi (Fr.ofInt 1), .ins true 2], ?_, ?_⟩
  · simp [MerkleTreeOps.insertAt, Exec.request, Op.mapM, Aligned.mapM, hh, Exec.blank, fieldKey, Expr.eval,
      alignedOf, alignOf, Value.tys, Shape.tys, Ty.align]
    rfl
  · have hk := ofAligned_byteKey hb
    have hk0 := ofFields_key0
    have hk1 := ofFields_key1
    simp only [AV.ofAligned] at hk
    rw [LedgerState.WF] at hwf
    have hi := lt_of_getElem? hf
    have hf' := getElem_of_getElem? hf
    have hx256 := lt_of_ofFields_bytes32 hx
    have hff64 : ff < 2 ^ 64 := by omega
    have hrange : ¬ (d < 64 ∧ 2 ^ d ≤ ff) := by omega
    vm_simp [hb, hk, hk0, hk1, hx, hwf, hst, hi, hf, hf', immOf, frOfInt_val_one, hff, hff64, hrange, AV.toHash,
      hx256, AV.ofU64, List.set, LedgerState.setField]

/-- `insertHash` on a full tree (no free index) fails. -/
theorem MerkleTree.insertHash_full (t : MerkleTree d α) (h : Bytes 32) (hs : List Fr) (x : Nat)
    (leaves : List (Nat × Nat)) (a : List Zkir.AlignAtom) (ff : Nat)
    (hpath : t.path = [fieldKey t.index]) (hst : σ.state = .array fields)
    (hf : fields[t.index]? = some (.array [.bmt d leaves, .cell ⟨a, [ff]⟩])) (hb : t.index < 256)
    (hd : d < 64) (hfull : 2 ^ d ≤ ff) (hff : ff < 2 ^ 64)
    (hh : Expr.evalList p env (Value.toExprs h) = some hs) (hx : AV.ofFields [.bytes 32] hs = some ⟨[.bytes 32], [x]⟩) :
    ∃ req, (emitted (t.insertHash h)).bind (Exec.request p env) = some req ∧ ledgerOracle H req σ = none := by
  have he : emitted (t.insertHash h) = some (MerkleTreeOps.insertAt t.path h [.ins true (t.path.length + 1)]) := rfl
  rw [he, hpath]
  rw [evalList_eq_mapM] at hh
  refine ⟨[.idx false true [⟨[.bytes 1], [Fr.ofInt t.index]⟩], .idx false true [⟨[.bytes 1], [Fr.ofInt 0]⟩],
      .dup 2, .idx false false [⟨[.bytes 1], [Fr.ofInt 1]⟩], .push true ⟨[.bytes 32], hs⟩, .ins false 1, .ins true 1,
      .idx false true [⟨[.bytes 1], [Fr.ofInt 1]⟩], .addi (Fr.ofInt 1), .ins true 2], ?_, ?_⟩
  · simp [MerkleTreeOps.insertAt, Exec.request, Op.mapM, Aligned.mapM, hh, Exec.blank, fieldKey, Expr.eval,
      alignedOf, alignOf, Value.tys, Shape.tys, Ty.align]
    rfl
  · have hk := ofAligned_byteKey hb
    have hk0 := ofFields_key0
    have hk1 := ofFields_key1
    simp only [AV.ofAligned] at hk
    have hi := lt_of_getElem? hf
    have hf' := getElem_of_getElem? hf
    have hrange : d < 64 ∧ 2 ^ d ≤ ff := ⟨hd, hfull⟩
    vm_simp [hb, hk, hk0, hk1, hx, hst, hi, hf, hf', immOf, frOfInt_val_one, hff, hd, hfull, AV.toHash]

/-- `isFull`: whether the first free index has reached `2^d` (for a depth
    `d < 64`, whose `2^d` the VM compares as a `u64`). The ledger is unchanged. -/
theorem MerkleTree.isFull_spec (t : MerkleTree d α) (tree : SV) (a : List Zkir.AlignAtom) (ff : Nat)
    (hpath : t.path = [fieldKey t.index]) (hst : σ.state = .array fields)
    (hf : fields[t.index]? = some (.array [tree, .cell ⟨a, [ff]⟩])) (hb : t.index < 256) (hwf : σ.WF)
    (hd : d < 64) (hff : ff < 2 ^ 64) :
    ∃ req, (emitted t.isFull).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some ([Fr.ofBool (decide (2 ^ d ≤ ff))], σ) := by
  have he : t.isFull = ledgerRead Boolean (fun es => [.dup 0, .idx false false t.path, .idx false false [fieldKey 1],
      .push false ⟨[.bytes 8], [.const (2 ^ d)]⟩, .lt, .neg, .popeq true [.bytes 1] es]) := rfl
  rw [he, emitted_ledgerRead, hpath]
  refine ⟨[.dup 0, .idx false false [⟨[.bytes 1], [Fr.ofInt t.index]⟩], .idx false false [⟨[.bytes 1], [Fr.ofInt 1]⟩],
      .push false ⟨[.bytes 8], [Fr.ofInt ((2 : Int) ^ d)]⟩, .lt, .neg, .popeq true [.bytes 1] []], ?_, ?_⟩
  · simp [Exec.request, Op.mapM, Aligned.mapM, Exec.blank, fieldKey, Expr.eval,
      mapM_eval_readVars]
  · have hk := ofAligned_byteKey hb
    have hk1 := ofFields_key1
    simp only [AV.ofAligned] at hk
    rw [LedgerState.WF] at hwf
    have hi := lt_of_getElem? hf
    have hf' := getElem_of_getElem? hf
    obtain ⟨ctx, eff, st⟩ := σ
    simp only at hst hwf ⊢
    subst hst
    have hpow := ofFields_pow d hd
    have hpow64 : 2 ^ d < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hd
    have hb0 := fieldsOf_bool false
    have hb1 := fieldsOf_bool true
    simp only [ite_true, ite_false, Bool.false_eq_true] at hb0 hb1
    by_cases hc : ff < 2 ^ d
    · have h' : ¬ 2 ^ d ≤ ff := by omega
      vm_simp [hb, hk, hk1, hpow, hpow64, hwf, hi, hf, hf', hff, readBack_cons, AV.ofBool, AV.toBool, hc, h', hb0]
    · have h' : 2 ^ d ≤ ff := by omega
      vm_simp [hb, hk, hk1, hpow, hpow64, hwf, hi, hf, hf', hff, readBack_cons, AV.ofBool, AV.toBool, hc, h', hb1]

/-- `checkRoot r`: whether the root of the tree (`ρ`, what the root hook
    gives for its leaves) is the digest `r`, as a `[field]` cell; the ledger
    is unchanged. -/
theorem MerkleTree.checkRoot_spec (t : MerkleTree d α) (r : MerkleTreeDigest) (rv : Fr) (ρ : AV)
    (leaves : List (Nat × Nat)) (ffv : SV)
    (hpath : t.path = [fieldKey t.index]) (hst : σ.state = .array fields)
    (hf : fields[t.index]? = some (.array [.bmt d leaves, ffv])) (hb : t.index < 256) (hwf : σ.WF)
    (hr : Expr.eval p env r.field.expr = some rv) (hρ : H.root d leaves = some ρ) (hρs : ρ.size ≤ 64) :
    ∃ req, (emitted (t.checkRoot r)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some ([Fr.ofBool (decide (⟨[.field], [rv.val]⟩ = ρ))], σ) := by
  have he : t.checkRoot r = ledgerRead Boolean (fun es => [.dup 0, .idx false false t.path,
      .idx false false [fieldKey 0], .root, .push false (alignedOf r), .eq, .popeq true [.bytes 1] es]) := rfl
  rw [he, emitted_ledgerRead, hpath]
  refine ⟨[.dup 0, .idx false false [⟨[.bytes 1], [Fr.ofInt t.index]⟩], .idx false false [⟨[.bytes 1], [Fr.ofInt 0]⟩],
      .root, .push false ⟨[.field], [rv]⟩, .eq, .popeq true [.bytes 1] []], ?_, ?_⟩
  · simp [Exec.request, Op.mapM, Aligned.mapM, Exec.blank, fieldKey, Expr.eval, mapM_eval_readVars, alignedOf,
      alignOf, Value.tys, Shape.tys, Shape.tysList, Ty.align, hr, digest_toExprs r, digest_align]
  · have hk := ofAligned_byteKey hb
    have hk0 := ofFields_key0
    simp only [AV.ofAligned] at hk
    rw [LedgerState.WF] at hwf
    have hi := lt_of_getElem? hf
    have hf' := getElem_of_getElem? hf
    obtain ⟨ctx, eff, st⟩ := σ
    simp only at hst hwf ⊢
    subst hst
    have hrs := fieldCell_size rv.val (fr_lt_2_256 rv)
    have hbool := fieldsOf_bool (decide ((⟨[.field], [rv.val]⟩ : AV) = ρ))
    simp only [decide_eq_true_eq] at hbool
    vm_simp [hb, hk, hk0, ofFields_field, hρ, hρs, hrs, hwf, hi, hf, hf', readBack_cons, AV.ofBool, hbool]

/-- `checkRoot r` with the real root (`merkleHooks`): whether `r` is the
    Poseidon root of the leaves (`merkleRootAt`). -/
theorem MerkleTree.checkRoot_merkle (t : MerkleTree d α) (r : MerkleTreeDigest) (rv : Fr)
    (leaves : List (Nat × Nat)) (ffv : SV)
    (hpath : t.path = [fieldKey t.index]) (hst : σ.state = .array fields)
    (hf : fields[t.index]? = some (.array [.bmt d leaves, ffv])) (hb : t.index < 256) (hwf : σ.WF)
    (hr : Expr.eval p env r.field.expr = some rv) :
    ∃ req, (emitted (t.checkRoot r)).bind (Exec.request p env) = some req ∧
      ledgerOracle merkleHooks req σ = some ([Fr.ofBool (decide (rv = merkleRootAt leaves d 0))], σ) := by
  obtain ⟨req, h1, h2⟩ := MerkleTree.checkRoot_spec merkleHooks p env σ fields t r rv
    ⟨[.field], [(merkleRootAt leaves d 0).val]⟩ leaves ffv hpath hst hf hb hwf hr rfl
    (fieldCell_size _ (fr_lt_2_256 _))
  refine ⟨req, h1, ?_⟩
  rw [h2]
  have : ((⟨[.field], [rv.val]⟩ : AV) = ⟨[.field], [(merkleRootAt leaves d 0).val]⟩) ↔ rv = merkleRootAt leaves d 0 := by
    constructor
    · intro h; simp at h; exact Fr.ext h
    · intro h; rw [h]
  simp only [this]

/-! ## `HistoricMerkleTree` -/

/-- `insertHash h` on a historic tree: as for `MerkleTree`, and the new root
    (`ρ'`, the root of the new leaves) is added to the past roots. -/
theorem HistoricMerkleTree.insertHash_spec (t : HistoricMerkleTree d α) (h : Bytes 32) (hs : List Fr) (x : Nat)
    (leaves : List (Nat × Nat)) (a : List Zkir.AlignAtom) (ff : Nat) (past : List (AV × SV)) (ρ' : AV)
    (hpath : t.path = [fieldKey t.index]) (hst : σ.state = .array fields)
    (hf : fields[t.index]? = some (.array [.bmt d leaves, .cell ⟨a, [ff]⟩, .map past])) (hb : t.index < 256)
    (hwf : σ.WF) (hfree : ff < 2 ^ d) (hff : ff + 1 < 2 ^ 64)
    (hh : Expr.evalList p env (Value.toExprs h) = some hs) (hx : AV.ofFields [.bytes 32] hs = some ⟨[.bytes 32], [x]⟩)
    (hρ : H.root d (assocSet ff x leaves) = some ρ') :
    ∃ req, (emitted (t.insertHash h)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some ([], σ.setField t.index
        (.array [.bmt d (assocSet ff x leaves), .cell (AV.ofU64 (ff + 1)), .map (assocSet ρ' .null past)])) := by
  have he : emitted (t.insertHash h) = some (MerkleTreeOps.insertAt t.path h
      ([.ins true 1] ++ MerkleTreeOps.recordRoot ++ [.ins true (t.path.length + 1)])) := rfl
  rw [he, hpath]
  rw [evalList_eq_mapM] at hh
  refine ⟨[.idx false true [⟨[.bytes 1], [Fr.ofInt t.index]⟩], .idx false true [⟨[.bytes 1], [Fr.ofInt 0]⟩],
      .dup 2, .idx false false [⟨[.bytes 1], [Fr.ofInt 1]⟩], .push true ⟨[.bytes 32], hs⟩, .ins false 1, .ins true 1,
      .idx false true [⟨[.bytes 1], [Fr.ofInt 1]⟩], .addi (Fr.ofInt 1), .ins true 1,
      .idx false true [⟨[.bytes 1], [Fr.ofInt 2]⟩], .dup 2, .idx false false [⟨[.bytes 1], [Fr.ofInt 0]⟩], .root,
      .pushNull true, .ins false 1, .ins true 2], ?_, ?_⟩
  · simp [MerkleTreeOps.insertAt, MerkleTreeOps.recordRoot, Exec.request, Op.mapM, Aligned.mapM, hh, Exec.blank,
      fieldKey, Expr.eval, alignedOf, alignOf, Value.tys, Shape.tys, Ty.align]
    rfl
  · have hk := ofAligned_byteKey hb
    have hk0 := ofFields_key0
    have hk1 := ofFields_key1
    have hk2 := ofFields_key2
    simp only [AV.ofAligned] at hk
    rw [LedgerState.WF] at hwf
    have hi := lt_of_getElem? hf
    have hf' := getElem_of_getElem? hf
    have hx256 := lt_of_ofFields_bytes32 hx
    have hff64 : ff < 2 ^ 64 := by omega
    have hrange : ¬ (d < 64 ∧ 2 ^ d ≤ ff) := by omega
    vm_simp [hb, hk, hk0, hk1, hk2, hx, hwf, hst, hi, hf, hf', immOf, frOfInt_val_one, hff, hff64, hrange,
      AV.toHash, hx256, AV.ofU64, hρ, List.set, LedgerState.setField]

/-- `checkRoot r` on a historic tree: whether `r` (as a `[field]` cell) is
    among the remembered roots; the ledger is unchanged. -/
theorem HistoricMerkleTree.checkRoot_spec (t : HistoricMerkleTree d α) (r : MerkleTreeDigest) (rv : Fr)
    (tree ffv : SV) (past : List (AV × SV))
    (hpath : t.path = [fieldKey t.index]) (hst : σ.state = .array fields)
    (hf : fields[t.index]? = some (.array [tree, ffv, .map past])) (hb : t.index < 256) (hwf : σ.WF)
    (hr : Expr.eval p env r.field.expr = some rv) :
    ∃ req, (emitted (t.checkRoot r)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some ([Fr.ofBool (assocGet ⟨[.field], [rv.val]⟩ past).isSome], σ) := by
  have he : t.checkRoot r = ledgerRead Boolean (fun es => [.dup 0, .idx false false t.path,
      .idx false false [fieldKey 2], .push false (alignedOf r), .member, .popeq true [.bytes 1] es]) := rfl
  rw [he, emitted_ledgerRead, hpath]
  refine ⟨[.dup 0, .idx false false [⟨[.bytes 1], [Fr.ofInt t.index]⟩], .idx false false [⟨[.bytes 1], [Fr.ofInt 2]⟩],
      .push false ⟨[.field], [rv]⟩, .member, .popeq true [.bytes 1] []], ?_, ?_⟩
  · simp [Exec.request, Op.mapM, Aligned.mapM, Exec.blank, fieldKey, Expr.eval, mapM_eval_readVars, alignedOf,
      alignOf, Value.tys, Shape.tys, Shape.tysList, Ty.align, hr, digest_toExprs r, digest_align]
  · have hk := ofAligned_byteKey hb
    have hk2 := ofFields_key2
    simp only [AV.ofAligned] at hk
    rw [LedgerState.WF] at hwf
    have hi := lt_of_getElem? hf
    have hf' := getElem_of_getElem? hf
    obtain ⟨ctx, eff, st⟩ := σ
    simp only at hst hwf ⊢
    subst hst
    have hbool := fieldsOf_bool (assocGet (⟨[.field], [rv.val]⟩ : AV) past).isSome
    vm_simp [hb, hk, hk2, ofFields_field, hwf, hi, hf, hf', readBack_cons, AV.ofBool, hbool]

/-- `resetHistory`: the past roots become exactly the current root `ρ`. -/
theorem HistoricMerkleTree.resetHistory_spec (t : HistoricMerkleTree d α) (leaves : List (Nat × Nat))
    (ffv pastv : SV) (ρ : AV)
    (hpath : t.path = [fieldKey t.index]) (hst : σ.state = .array fields)
    (hf : fields[t.index]? = some (.array [.bmt d leaves, ffv, pastv])) (hb : t.index < 256) (hwf : σ.WF)
    (hρ : H.root d leaves = some ρ) :
    ∃ req, (emitted t.resetHistory).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some ([], σ.setField t.index (.array [.bmt d leaves, ffv, .map [(ρ, .null)]])) := by
  have he : emitted t.resetHistory = some [.idx false true t.path, .push false (fieldKey 2), .pushState true .emptyMap,
      .dup 2, .idx false false [fieldKey 0], .root, .pushNull true, .ins true (t.path.length + 2)] := rfl
  rw [he, hpath]
  refine ⟨[.idx false true [⟨[.bytes 1], [Fr.ofInt t.index]⟩], .push false ⟨[.bytes 1], [Fr.ofInt 2]⟩,
      .pushState true .emptyMap, .dup 2, .idx false false [⟨[.bytes 1], [Fr.ofInt 0]⟩], .root, .pushNull true,
      .ins true 3], ?_, ?_⟩
  · simp [Exec.request, Op.mapM, Aligned.mapM, StateLit.mapM, Exec.blank, fieldKey, Expr.eval]
  · have hk := ofAligned_byteKey hb
    have hk0 := ofFields_key0
    have hk2 := ofFields_key2
    simp only [AV.ofAligned] at hk
    rw [LedgerState.WF] at hwf
    have hi := lt_of_getElem? hf
    have hf' := getElem_of_getElem? hf
    vm_simp [hb, hk, hk0, hk2, hwf, hst, hi, hf, hf', hρ, SV.ofLit, List.set, LedgerState.setField]

end

end Damp.Ledger
