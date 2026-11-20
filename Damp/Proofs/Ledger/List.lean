/-
`LedgerList` (`Damp/Lang/Ledger.lean`) against the VM model, for a top-level
list (`l.path = [fieldKey l.index]`, the default path).

A list is stored as a linked structure of arrays `[head, tail, length]`: the
empty list is `[null, null, 0]` (`LedgerList.initial`), and `pushFront x` on a
list `L` stores `[x, L, length + 1]`. `listRepr xs` is the state value of the
list of (stored) elements `xs`, and the theorems say what each operation does
to it: the operations behave as a stack.

`head`'s `concat` is bounded by the runtime's `maxAlignedSize` of the element
type: the stored head must not be larger (`w.size ≤ maxAlignedSize (alignOf α)`,
true of every value of type `α`; a hypothesis here).
-/
import Damp.Proofs.Ledger.Counter

namespace Damp.Ledger
open Damp.IR Damp.Impact

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-- The state value of a list holding `xs` (first element first). -/
def listRepr : List AV → SV
  | [] => .array [.null, .null, .cell (AV.ofU64 0)]
  | x :: xs => .array [.cell x, listRepr xs, .cell (AV.ofU64 (xs.length + 1))]

theorem alignOf_maybe (α : Type) [Value α] : alignOf (Maybe α) = .bytes 1 :: alignOf α := by
  show (Shape.tysList [.prim .bool, Value.shape α]).map Ty.align = .bytes 1 :: ((Value.shape α).tys).map Ty.align
  simp [Shape.tysList, Shape.tys, Ty.align]

theorem aV_one_size : (⟨[.bytes 1], [1]⟩ : AV).size = 2 := by decide

section
variable {α : Type} [Value α] (H : Hooks) (p : Zkir.Prims) (env : Env) (σ : LedgerState)
  (fields : List SV) (l : LedgerList α)

/-- `pushFront x`: the list `xs` becomes `xv :: xs`, `xv` the stored `x`.
    Nothing is read; it fails only if the length overflows 64 bits. -/
theorem LedgerList.pushFront_spec (x : α) (vs : List Fr) (xv : AV) (xs : List AV)
    (hpath : l.path = [fieldKey l.index]) (hst : σ.state = .array fields)
    (hf : fields[l.index]? = some (listRepr xs)) (hb : l.index < 256) (hwf : σ.WF)
    (hlen : xs.length + 1 < 2 ^ 64)
    (hx : Expr.evalList p env (Value.toExprs x) = some vs) (hv : AV.ofFields (alignOf α) vs = some xv) :
    ∃ req, (emitted (l.pushFront x)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some ([], σ.setField l.index (listRepr (xv :: xs))) := by
  have he : emitted (l.pushFront x) = some [.idx false true l.path, .dup 0, .idx false false [fieldKey 2],
      .addi (.const 1), .pushState true (.array [.cell (alignedOf x), .null, .null]), .swap 0,
      .push false (fieldKey 2), .swap 0, .ins true 1, .swap 0, .push false (fieldKey 1), .swap 0,
      .ins true (l.path.length + 1)] := rfl
  rw [he, hpath]
  rw [evalList_eq_mapM] at hx
  refine ⟨[.idx false true [⟨[.bytes 1], [Fr.ofInt l.index]⟩], .dup 0, .idx false false [⟨[.bytes 1], [Fr.ofInt 2]⟩],
      .addi (Fr.ofInt 1), .pushState true (.array [.cell ⟨alignOf α, vs⟩, .null, .null]), .swap 0,
      .push false ⟨[.bytes 1], [Fr.ofInt 2]⟩, .swap 0, .ins true 1, .swap 0, .push false ⟨[.bytes 1], [Fr.ofInt 1]⟩,
      .swap 0, .ins true 2], ?_, ?_⟩
  · simp [Exec.request, Op.mapM, Aligned.mapM, StateLit.mapM, StateLit.mapMList, hx, Exec.blank, fieldKey, Expr.eval,
      alignedOf]
  · have hk := ofAligned_byteKey hb
    have hk1 := ofFields_key1
    have hk2 := ofFields_key2
    simp only [AV.ofAligned] at hk
    rw [LedgerState.WF] at hwf
    have hi := lt_of_getElem? hf
    have hf' := getElem_of_getElem? hf
    have h1 : (Fr.ofInt 1).val = 1 := rfl
    cases xs with
    | nil =>
      simp only [listRepr] at hf hf' ⊢
      vm_simp [hb, hk, hk1, hk2, h1, hwf, hst, hi, hf, hf', hv, immOf, SV.ofLit, SV.ofLitList, AV.ofU64, List.set,
        LedgerState.setField]
    | cons y ys =>
      simp only [listRepr, List.length_cons] at hf hf' hlen ⊢
      have hl1 : ys.length + 1 < 18446744073709551616 := by omega
      have hl2 : ys.length + 1 + 1 < 18446744073709551616 := by omega
      vm_simp [hl1, hl2, hb, hk, hk1, hk2, h1, hwf, hst, hi, hf, hf', hv, immOf, SV.ofLit, SV.ofLitList, AV.ofU64, List.set,
        LedgerState.setField, hlen]

/-- `popFront` on a non-empty list: the list `y :: ys` becomes `ys`. -/
theorem LedgerList.popFront_spec (y : AV) (ys : List AV)
    (hpath : l.path = [fieldKey l.index]) (hst : σ.state = .array fields)
    (hf : fields[l.index]? = some (listRepr (y :: ys))) (hb : l.index < 256) (hwf : σ.WF) :
    ∃ req, (emitted l.popFront).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some ([], σ.setField l.index (listRepr ys)) := by
  have he : emitted l.popFront = some [.idx false true l.path, .idx false false [fieldKey 1],
      .ins true l.path.length] := rfl
  rw [he, hpath]
  refine ⟨[.idx false true [⟨[.bytes 1], [Fr.ofInt l.index]⟩], .idx false false [⟨[.bytes 1], [Fr.ofInt 1]⟩],
      .ins true 1], ?_, ?_⟩
  · simp [Exec.request, Op.mapM, Aligned.mapM, Exec.blank, fieldKey, Expr.eval]
  · have hk := ofAligned_byteKey hb
    have hk1 := ofFields_key1
    simp only [AV.ofAligned] at hk
    rw [LedgerState.WF] at hwf
    have hi := lt_of_getElem? hf
    have hf' := getElem_of_getElem? hf
    simp only [listRepr] at hf hf' ⊢
    vm_simp [hb, hk, hk1, hwf, hst, hi, hf, hf', LedgerState.setField]

/-- `popFront` on the empty list replaces it by null (its tail): the list
    field no longer holds a list. Compact's `popFront` of an empty list is the
    same program. -/
theorem LedgerList.popFront_nil
    (hpath : l.path = [fieldKey l.index]) (hst : σ.state = .array fields)
    (hf : fields[l.index]? = some (listRepr [])) (hb : l.index < 256) (hwf : σ.WF) :
    ∃ req, (emitted l.popFront).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some ([], σ.setField l.index .null) := by
  have he : emitted l.popFront = some [.idx false true l.path, .idx false false [fieldKey 1],
      .ins true l.path.length] := rfl
  rw [he, hpath]
  refine ⟨[.idx false true [⟨[.bytes 1], [Fr.ofInt l.index]⟩], .idx false false [⟨[.bytes 1], [Fr.ofInt 1]⟩],
      .ins true 1], ?_, ?_⟩
  · simp [Exec.request, Op.mapM, Aligned.mapM, Exec.blank, fieldKey, Expr.eval]
  · have hk := ofAligned_byteKey hb
    have hk1 := ofFields_key1
    simp only [AV.ofAligned] at hk
    rw [LedgerState.WF] at hwf
    have hi := lt_of_getElem? hf
    have hf' := getElem_of_getElem? hf
    simp only [listRepr] at hf hf' ⊢
    vm_simp [hb, hk, hk1, hwf, hst, hi, hf, hf', LedgerState.setField]

/-- `length`: the number of elements; the ledger is unchanged. -/
theorem LedgerList.length_spec (xs : List AV)
    (hpath : l.path = [fieldKey l.index]) (hst : σ.state = .array fields)
    (hf : fields[l.index]? = some (listRepr xs)) (hb : l.index < 256) (hwf : σ.WF)
    (hlen : xs.length < 2 ^ 64) :
    ∃ req, (emitted l.length).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some ([Fr.ofNat xs.length], σ) := by
  have he : l.length = ledgerRead Uint64 (fun es =>
      [.dup 0, .idx false false l.path, .idx false false [fieldKey 2], .popeq true [.bytes 8] es]) := rfl
  rw [he, emitted_ledgerRead, hpath]
  refine ⟨[.dup 0, .idx false false [⟨[.bytes 1], [Fr.ofInt l.index]⟩], .idx false false [⟨[.bytes 1], [Fr.ofInt 2]⟩],
      .popeq true [.bytes 8] []], ?_, ?_⟩
  · simp [Exec.request, Op.mapM, Aligned.mapM, Exec.blank, fieldKey, Expr.eval, mapM_eval_readVars]
  · have hk := ofAligned_byteKey hb
    have hk2 := ofFields_key2
    simp only [AV.ofAligned] at hk
    rw [LedgerState.WF] at hwf
    have hi := lt_of_getElem? hf
    have hf' := getElem_of_getElem? hf
    obtain ⟨ctx, eff, st⟩ := σ
    simp only at hst hwf ⊢
    subst hst
    cases xs with
    | nil =>
      simp only [listRepr] at hf hf' ⊢
      vm_simp [hb, hk, hk2, hwf, hi, hf, hf', readBack_cons, fieldsOf_u64, AV.ofU64]
    | cons y ys =>
      simp only [listRepr, List.length_cons] at hf hf' hlen ⊢
      vm_simp [hb, hk, hk2, hwf, hi, hf, hf', readBack_cons, fieldsOf_u64 _ hlen, AV.ofU64]

/-- `isEmpty`: whether the list has no element (its tail is null); the
    ledger is unchanged. -/
theorem LedgerList.isEmpty_spec (xs : List AV)
    (hpath : l.path = [fieldKey l.index]) (hst : σ.state = .array fields)
    (hf : fields[l.index]? = some (listRepr xs)) (hb : l.index < 256) (hwf : σ.WF) :
    ∃ req, (emitted l.isEmpty).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some ([Fr.ofBool (decide (xs = []))], σ) := by
  have he : l.isEmpty = ledgerRead Boolean (fun es =>
      [.dup 0, .idx false false l.path, .idx false false [fieldKey 1], .type, .push false (fieldKey 1), .eq,
       .popeq true [.bytes 1] es]) := rfl
  rw [he, emitted_ledgerRead, hpath]
  refine ⟨[.dup 0, .idx false false [⟨[.bytes 1], [Fr.ofInt l.index]⟩], .idx false false [⟨[.bytes 1], [Fr.ofInt 1]⟩],
      .type, .push false ⟨[.bytes 1], [Fr.ofInt 1]⟩, .eq, .popeq true [.bytes 1] []], ?_, ?_⟩
  · simp [Exec.request, Op.mapM, Aligned.mapM, Exec.blank, fieldKey, Expr.eval, mapM_eval_readVars]
  · have hk := ofAligned_byteKey hb
    have hk1 := ofFields_key1
    simp only [AV.ofAligned] at hk
    rw [LedgerState.WF] at hwf
    have hi := lt_of_getElem? hf
    have hf' := getElem_of_getElem? hf
    obtain ⟨ctx, eff, st⟩ := σ
    simp only at hst hwf ⊢
    subst hst
    have hs1 : (⟨[.bytes 1], [1]⟩ : AV).size ≤ 64 := by decide
    have hs27 : (⟨[.bytes 1], [27]⟩ : AV).size ≤ 64 := by decide
    have hb1 := fieldsOf_bool true
    have hb0 := fieldsOf_bool false
    simp only [ite_true, ite_false, Bool.false_eq_true] at hb1 hb0
    cases xs with
    | nil =>
      simp only [listRepr] at hf hf' ⊢
      vm_simp [hb, hk, hk1, hwf, hi, hf, hf', readBack_cons, typeTag, AV.ofU8, AV.ofBool, hs1, hb1]
    | cons y ys =>
      simp only [listRepr] at hf hf' ⊢
      cases ys <;>
      vm_simp [hb, hk, hk1, hwf, hi, hf, hf', readBack_cons, typeTag, AV.ofU8, AV.ofBool, hs1, hs27, hb0, listRepr]

/-- `resetToDefault`: the list becomes empty. -/
theorem LedgerList.resetToDefault_spec
    (hpath : l.path = [fieldKey l.index]) (hst : σ.state = .array fields)
    (hi : l.index < fields.length) (hb : l.index < 256) (hwf : σ.WF) :
    ∃ req, (emitted l.resetToDefault).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some ([], σ.setField l.index (listRepr [])) := by
  have he : emitted l.resetToDefault = some (resetOps l.path LedgerList.initial) := rfl
  rw [he, hpath]
  refine ⟨[.push false ⟨[.bytes 1], [Fr.ofInt l.index]⟩,
    .pushState true (.array [.null, .null, .cell ⟨[.bytes 8], [0]⟩]), .ins false 1], ?_, ?_⟩
  · simp [resetOps, insCached, LedgerList.initial, Exec.request, Op.mapM, StateLit.mapM, StateLit.mapMList,
      Aligned.mapM, Exec.blank, fieldKey, Expr.eval]
    rfl
  · have hk := ofAligned_byteKey hb
    simp only [AV.ofAligned] at hk
    rw [LedgerState.WF] at hwf
    have hz : AV.ofFields [.bytes 8] [0] = some (AV.ofU64 0) := by decide
    vm_simp [hb, hk, hz, hwf, hst, hi, SV.ofLit, SV.ofLitList, listRepr, LedgerState.setField]

/-- The request `head` sends, with the operands of `none` (`zs`) evaluated. -/
def headReq (i : Nat) (α : Type) [Value α] (zs : List Fr) : List (Op Fr) :=
  [.dup 0, .idx false false [⟨[.bytes 1], [Fr.ofInt i]⟩], .idx false false [⟨[.bytes 1], [Fr.ofInt 0]⟩],
   .dup 0, .type, .push false ⟨[.bytes 1], [Fr.ofInt 1]⟩, .eq, .branch 4, .push false ⟨[.bytes 1], [Fr.ofInt 1]⟩,
   .swap 0, .concat (2 + maxAlignedSize (alignOf α)), .jmp 2, .pop, .push false ⟨alignOf (Maybe α), zs⟩,
   .popeq true (alignOf (Maybe α)) []]

theorem LedgerList.head_req (zs : List Fr) (hpath : l.path = [fieldKey l.index])
    (hz : Expr.evalList p env (Value.toExprs (Maybe.none : Maybe α)) = some zs) :
    (emitted l.head).bind (Exec.request p env) = some (headReq l.index α zs) := by
  have he : l.head = ledgerRead (Maybe α) (fun es => [.dup 0, .idx false false l.path, .idx false false [fieldKey 0],
      .dup 0, .type, .push false (fieldKey 1), .eq, .branch 4, .push false (fieldKey 1), .swap 0,
      .concat (2 + maxAlignedSize (alignOf α)), .jmp 2, .pop, .push false (alignedOf (Maybe.none : Maybe α)),
      .popeq true (alignOf (Maybe α)) es]) := rfl
  rw [he, emitted_ledgerRead, hpath]
  rw [evalList_eq_mapM] at hz
  simp [Exec.request, Op.mapM, Aligned.mapM, Exec.blank, fieldKey, Expr.eval, mapM_eval_readVars, alignedOf, hz,
    headReq]

/-- `head` of the empty list: `none`, i.e. the field elements of
    `Maybe.none` (`zs`, stored as `z`, read back as `ys`; for a single-limb
    element type `ys = zs`). The ledger is unchanged. -/
theorem LedgerList.head_nil (zs ys : List Fr) (z : AV)
    (hpath : l.path = [fieldKey l.index]) (hst : σ.state = .array fields)
    (hf : fields[l.index]? = some (listRepr [])) (hb : l.index < 256) (hwf : σ.WF)
    (hz : Expr.evalList p env (Value.toExprs (Maybe.none : Maybe α)) = some zs)
    (hzv : AV.ofFields (alignOf (Maybe α)) zs = some z) (hys : fieldsOf (alignOf (Maybe α)) z.atoms = some ys) :
    ∃ req, (emitted l.head).bind (Exec.request p env) = some req ∧ ledgerOracle H req σ = some (ys, σ) := by
  refine ⟨_, LedgerList.head_req p env l zs hpath hz, ?_⟩
  have hk := ofAligned_byteKey hb
  have hk0 := ofFields_key0
  have hk1 := ofFields_key1
  simp only [AV.ofAligned] at hk
  rw [LedgerState.WF] at hwf
  have hi := lt_of_getElem? hf
  have hf' := getElem_of_getElem? hf
  obtain ⟨ctx, eff, st⟩ := σ
  simp only at hst hwf ⊢
  subst hst
  have hs1 : (⟨[.bytes 1], [1]⟩ : AV).size ≤ 64 := by decide
  simp only [listRepr] at hf hf' ⊢
  vm_simp [headReq, hb, hk, hk0, hk1, hzv, hwf, hi, hf, hf', readBack_cons, typeTag, AV.ofU8, AV.ofBool, hs1, hys]

/-- `head` of a non-empty list `y :: ys`: `some y`, i.e. the flag 1 and the
    field elements of `y` (read under `α`'s alignment as `vs`). The runtime
    bounds the `concat` that builds the result by `maxAlignedSize` of `α`'s
    alignment, which `y` must respect (`hsz`, true of a value of type `α`).
    The ledger is unchanged. -/
theorem LedgerList.head_cons (zs vs : List Fr) (z y : AV) (ys : List AV)
    (hpath : l.path = [fieldKey l.index]) (hst : σ.state = .array fields)
    (hf : fields[l.index]? = some (listRepr (y :: ys))) (hb : l.index < 256) (hwf : σ.WF)
    (hz : Expr.evalList p env (Value.toExprs (Maybe.none : Maybe α)) = some zs)
    (hzv : AV.ofFields (alignOf (Maybe α)) zs = some z)
    (hsz : y.size ≤ maxAlignedSize (alignOf α)) (hmax : 2 + maxAlignedSize (alignOf α) ≤ cellBound)
    (hvs : fieldsOf (alignOf α) y.atoms = some vs) :
    ∃ req, (emitted l.head).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = some (Fr.ofBool true :: vs, σ) := by
  refine ⟨_, LedgerList.head_req p env l zs hpath hz, ?_⟩
  have hk := ofAligned_byteKey hb
  have hk0 := ofFields_key0
  have hk1 := ofFields_key1
  simp only [AV.ofAligned] at hk
  rw [LedgerState.WF] at hwf
  have hi := lt_of_getElem? hf
  have hf' := getElem_of_getElem? hf
  obtain ⟨ctx, eff, st⟩ := σ
  simp only at hst hwf ⊢
  subst hst
  have hs0 : (⟨[.bytes 1], [0]⟩ : AV).size ≤ 64 := by decide
  have hs1 : (⟨[.bytes 1], [1]⟩ : AV).size ≤ 64 := by decide
  have hsz' : y.size + (⟨[.bytes 1], [1]⟩ : AV).size ≤ 2 + maxAlignedSize (alignOf α) := by
    rw [aV_one_size]; omega
  have hmax' : ¬ (2 + maxAlignedSize (alignOf α) > cellBound) := by omega
  have hrb : fieldsOf (alignOf (Maybe α)) (1 :: y.atoms) = some (Fr.ofBool true :: vs) := by
    rw [alignOf_maybe]
    have := fieldsOf_bool true
    simp only [ite_true] at this
    simp only [fieldsOf] at this ⊢
    cases h1 : fieldsOfAtom (.bytes 1) 1 with
    | none => simp [h1] at this
    | some f => simp [h1] at this; simp [this, hvs]
  simp only [listRepr] at hf hf' ⊢
  vm_simp [headReq, hb, hk, hk0, hk1, hzv, hwf, hi, hf, hf', readBack_cons, typeTag, AV.ofU8, AV.ofBool, hs0, hs1,
    hsz', hmax', hrb]

end

end Damp.Ledger
