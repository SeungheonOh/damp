/-
Kernel reads (`Damp/Lang/Ledger.lean`) against the VM model: the contract's
own address (`Kernel.self`) and the block-time comparisons (`blockTimeLt`,
`blockTimeGt`, `blockTimeGte`, `blockTimeLte`).

They read the call context, the bottom of the VM stack, which
`QueryContext::to_vm_stack` (`onchain-runtime/src/context.rs`) builds as an
array: 0 the contract's address (a `[bytes 32]` cell), 1 the communication
commitment indices, 2 the block time in seconds (`tblock`, a `u64` cell), 3
its error bound, 4 the parent block hash, 5 the balance, 6 the caller, 7 the
last block time. The theorems assume only what they read: `σ.context` is an
array whose entry 0 (or 2) is the cell given. The context is weak and fully
cached, so the cached `idx` the kernel uses always hits.
-/
import Damp.Proofs.Ledger.Counter

namespace Damp.Ledger
open Damp.IR Damp.Impact

set_option linter.unusedSimpArgs false

section
variable (H : Hooks) (p : Zkir.Prims) (env : Env) (σ : LedgerState)

/-- `Kernel.self`: the field elements of the address in the call context, read
    as 32 bytes (two limbs); the ledger is unchanged. -/
theorem Kernel.self_spec (cfs : List SV) (w : AV) (ys : List Fr)
    (hctx : σ.context = .array cfs) (hc : cfs[0]? = some (.cell w)) (hwf : σ.WF)
    (hys : fieldsOf [.bytes 32] w.atoms = some ys) :
    ∃ req, (emitted Kernel.self).bind (Exec.request p env) = some req ∧ ledgerOracle H req σ = some (ys, σ) := by
  have he : Kernel.self = ledgerRead ContractAddress (fun es =>
      [.dup 2, .idx true false [fieldKey 0], .popeq true [.bytes 32] es]) := rfl
  rw [he, emitted_ledgerRead]
  refine ⟨[.dup 2, .idx true false [⟨[.bytes 1], [Fr.ofInt 0]⟩], .popeq true [.bytes 32] []], ?_, ?_⟩
  · simp [Exec.request, Op.mapM, Aligned.mapM, Exec.blank, fieldKey, Expr.eval, mapM_eval_readVars]
  · have hk : AV.ofFields [.bytes 1] [Fr.ofInt 0] = some ⟨[.bytes 1], [0]⟩ :=
      ofAligned_byteKey (i := 0) (by decide)
    rw [LedgerState.WF] at hwf
    obtain ⟨ctx, eff, st⟩ := σ
    simp only at hctx hwf ⊢
    subst hctx
    have hi := lt_of_getElem? hc
    have hc' := getElem_of_getElem? hc
    vm_simp [hk, hwf, hi, hc, hc', readBack_cons, hys]

/-- The VM reading the block time `τ` and comparing it with `t`, as in
    `blockTimeLt`. -/
theorem blockTimeLt_spec (t : Uint64) (tv : Fr) (cfs : List SV) (a : List Zkir.AlignAtom) (τ : Nat)
    (hctx : σ.context = .array cfs) (hc : cfs[2]? = some (.cell ⟨a, [τ]⟩)) (hτ : τ < 2 ^ 64) (hwf : σ.WF)
    (ht : Expr.eval p env t.expr = some tv) :
    ∃ req, (emitted (blockTimeLt t)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = if tv.val < 2 ^ 64 then some ([Fr.ofBool (decide (τ < tv.val))], σ) else none := by
  have he : blockTimeLt t = ledgerRead Boolean (fun es =>
      [.dup 2, .idx true false [fieldKey 2], .push false ⟨[.bytes 8], [t.expr]⟩, .lt, .popeq true [.bytes 1] es]) := rfl
  rw [he, emitted_ledgerRead]
  refine ⟨[.dup 2, .idx true false [⟨[.bytes 1], [Fr.ofInt 2]⟩], .push false ⟨[.bytes 8], [tv]⟩, .lt,
    .popeq true [.bytes 1] []], ?_, ?_⟩
  · simp [Exec.request, Op.mapM, Aligned.mapM, Exec.blank, fieldKey, Expr.eval, mapM_eval_readVars, ht]
  · have hk : AV.ofFields [.bytes 1] [Fr.ofInt 2] = some ⟨[.bytes 1], [2]⟩ :=
      ofAligned_byteKey (i := 2) (by decide)
    rw [LedgerState.WF] at hwf
    obtain ⟨ctx, eff, st⟩ := σ
    simp only at hctx hwf ⊢
    subst hctx
    have hi := lt_of_getElem? hc
    have hc' := getElem_of_getElem? hc
    by_cases ht64 : tv.val < 2 ^ 64
    · have hbool := fieldsOf_bool (decide (τ < tv.val))
      simp only [decide_eq_true_eq] at hbool
      have htv : AV.ofFields [.bytes 8] [tv] = some ⟨[.bytes 8], [tv.val]⟩ := by
        simp [AV.ofFields, atomWidth, atomOfFields, atomFits, ht64]
      vm_simp [hk, htv, hwf, hi, hc, hc', hτ, ht64, AV.ofBool, readBack_cons, hbool]
    · rw [ledgerOracle_of_toR_none H (o := .push false ⟨[.bytes 8], [tv]⟩) (by simp)
        (by simp [Op.toR, AV.ofAligned, AV.ofFields, atomWidth, atomOfFields, atomFits, ht64])]
      simp [ht64]

/-- `blockTimeGt t`: whether `t` is below the block time `τ`. -/
theorem blockTimeGt_spec (t : Uint64) (tv : Fr) (cfs : List SV) (a : List Zkir.AlignAtom) (τ : Nat)
    (hctx : σ.context = .array cfs) (hc : cfs[2]? = some (.cell ⟨a, [τ]⟩)) (hτ : τ < 2 ^ 64) (hwf : σ.WF)
    (ht : Expr.eval p env t.expr = some tv) :
    ∃ req, (emitted (blockTimeGt t)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = if tv.val < 2 ^ 64 then some ([Fr.ofBool (decide (tv.val < τ))], σ) else none := by
  have he : blockTimeGt t = ledgerRead Boolean (fun es =>
      [.push false ⟨[.bytes 8], [t.expr]⟩, .dup 3, .idx true false [fieldKey 2], .lt, .popeq true [.bytes 1] es]) := rfl
  rw [he, emitted_ledgerRead]
  refine ⟨[.push false ⟨[.bytes 8], [tv]⟩, .dup 3, .idx true false [⟨[.bytes 1], [Fr.ofInt 2]⟩], .lt,
    .popeq true [.bytes 1] []], ?_, ?_⟩
  · simp [Exec.request, Op.mapM, Aligned.mapM, Exec.blank, fieldKey, Expr.eval, mapM_eval_readVars, ht]
  · have hk : AV.ofFields [.bytes 1] [Fr.ofInt 2] = some ⟨[.bytes 1], [2]⟩ :=
      ofAligned_byteKey (i := 2) (by decide)
    rw [LedgerState.WF] at hwf
    obtain ⟨ctx, eff, st⟩ := σ
    simp only at hctx hwf ⊢
    subst hctx
    have hi := lt_of_getElem? hc
    have hc' := getElem_of_getElem? hc
    by_cases ht64 : tv.val < 2 ^ 64
    · have hbool := fieldsOf_bool (decide (tv.val < τ))
      simp only [decide_eq_true_eq] at hbool
      have htv : AV.ofFields [.bytes 8] [tv] = some ⟨[.bytes 8], [tv.val]⟩ := by
        simp [AV.ofFields, atomWidth, atomOfFields, atomFits, ht64]
      vm_simp [hk, htv, hwf, hi, hc, hc', hτ, ht64, AV.ofBool, readBack_cons, hbool]
    · rw [ledgerOracle_of_toR_none H (o := .push false ⟨[.bytes 8], [tv]⟩) (by simp)
        (by simp [Op.toR, AV.ofAligned, AV.ofFields, atomWidth, atomOfFields, atomFits, ht64])]
      simp [ht64]

/-- `blockTimeGte t` sends the request of `blockTimeLt t` (and negates the answer in the circuit). -/
theorem emitted_blockTimeGte (t : Uint64) : emitted (blockTimeGte t) = emitted (blockTimeLt t) := rfl

/-- `blockTimeLte t` sends the request of `blockTimeGt t` (and negates the answer in the circuit). -/
theorem emitted_blockTimeLte (t : Uint64) : emitted (blockTimeLte t) = emitted (blockTimeGt t) := rfl

end

/-! ## The effects' typed decoding: an `Either` with both sides set

`claimUnshieldedCoinSpend` (effects slot 8) keys its entry by
`(TokenType, PublicAddress)`, written by Damp as `(Either<Bytes<32>,
Bytes<32>>, Either<ContractAddress, UserAddress>)`: six atoms. The runtime's
`PublicAddress` decoding needs the side not chosen to be empty, so an
`Either` with both sides non-zero is rejected at the end of the query, and
with it the whole request (`executor/test/either-both.mjs`; the differential
test covers such keys). -/

theorem effectEntry_spend_both_sides (al : List Zkir.AlignAtom) (t h z b a u : Nat) (v : SV)
    (ha : a ≠ 0) (hu : u ≠ 0) : effectEntry 8 ⟨al, [t, h, z, b, a, u]⟩ v = none := by
  have : publicAddressOk [b, a, u] = false := by
    simp [publicAddressOk, ha, hu]
  cases hv : effectValue 8 v <;>
    simp [effectEntry, effectKey, hv, spendKeyOk, this]

theorem effectMap_none_of_mem (slot : Nat) {k : AV} {v : SV} (hkv : effectEntry slot k v = none) :
    ∀ m : List (AV × SV), (k, v) ∈ m → effectMap slot m = none
  | [], h => by simp at h
  | (k', v') :: rest, h => by
      rcases List.mem_cons.1 h with h | h
      · cases h
        cases hr : effectMap slot rest <;> simp [effectMap, hr, hkv]
      · simp [effectMap, effectMap_none_of_mem slot hkv rest h]

/-- Effects whose unshielded-spends map (slot 8) holds an entry keyed by a
    `PublicAddress` with both sides set do not decode: a query leaving them
    fails (`query` returns `none`). -/
theorem decodeEffects_spend_both_sides (e₀ e₁ e₂ e₃ e₄ e₅ e₆ e₇ : SV) (m₈ : List (AV × SV))
    (al : List Zkir.AlignAtom) (t h z b a u : Nat) (v : SV) (ha : a ≠ 0) (hu : u ≠ 0)
    (hmem : (⟨al, [t, h, z, b, a, u]⟩, v) ∈ m₈) :
    decodeEffects (.array [e₀, e₁, e₂, e₃, e₄, e₅, e₆, e₇, .map m₈]) = none := by
  have h8 := effectMap_none_of_mem 8 (effectEntry_spend_both_sides al t h z b a u v ha hu) m₈ hmem
  have hl : ∀ (f : SV × Nat → Option SV) (xs : List (SV × Nat)) (y : SV × Nat), f y = none →
      (xs ++ [y]).mapM f = none := by
    intro f xs y hy
    induction xs with
    | nil => simp [hy]
    | cons x xs ih => cases hx : f x <;> simp [List.mapM_cons, hx, ih]
  have hz : [e₀, e₁, e₂, e₃, e₄, e₅, e₆, e₇, SV.map m₈].zipIdx =
      [e₀, e₁, e₂, e₃, e₄, e₅, e₆, e₇].zipIdx ++ [(SV.map m₈, 8)] := rfl
  simp only [decodeEffects, List.length_cons, List.length_nil, Nat.reduceAdd, ↓reduceIte]
  rw [hz, hl _ _ _ (by simp [h8])]
  rfl

end Damp.Ledger
