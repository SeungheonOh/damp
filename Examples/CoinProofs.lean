import Damp
import Damp.Proofs.Ledger.CoinsRuns
import Damp.Proofs.Ledger.Executor
import Examples.Tokens
import Examples.TokenProofs

/-!
A contract-level theorem about a circuit that sends shielded coins and stores
a coin with its Merkle-tree index, in the style of `Examples/TokenProofs.lean`:
`spend_shipped` (`Examples/Tokens.lean`, `tokens.spend`):

```
circuit spend (to : Recipient) (value : Uint128) : Unit := do
  const r ← sendShielded (← held.read) (disclose to) (disclose value)
  last.write r.sent
  if% r.change.isSome then do held.writeCoin r.change.value (← toSelf)
```

It reads the held coin (a `QualifiedShieldedCoinInfo`, field 6), sends `value`
of it (`sendShielded_runs`), stores the coin sent (field 1), and, when there
is change, stores the change coin qualified with its Merkle-tree index
(`Cell.writeCoin_runs`, under the guard `r.change.isSome`), reading
`kernel.self()` under that guard. Stated for any successful build (any level,
with or without `--ledger-opt`) via `build_correct`, ending with the shipped
ZKIR accepting the proof data.

Nothing is assumed about hashes. The commitment index of the change coin is
looked up in the call context (slot 1, `idx`) the call starts with: the theorem
is stated for witnesses that see only the private state (`oracles H
(liftWitness w)`, `Damp/Executor/Isolated.lean`), `createZswapOutput`
included, so the index the real runtime inserts when `createZswapOutput`
commits (`QueryContext.insertCommitment`, which `WitnessesOK` lets a witness
oracle do: `CtxSlotWriter 1`) is, to the theorem, part of the starting context. The call completes exactly when the
inputs pass their range checks, `value` is at most the held coin's value, and,
when there is change, the change coin's commitment has an index and the
qualified coin fits the VM's 91-byte bound (`qualifyAV`).
-/
namespace Examples.CoinProofs
open Damp Damp.IR Damp.Ledger Examples.TokenProofs

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-! ## Reading structures off their field elements -/

/-- A qualified coin read off six expressions, meaning `n ++ c ++ [v, i]`. -/
theorem qcoin_parts {p : Zkir.Prims} {e : Env} {q : QualifiedShieldedCoinInfo} (hq : Value.Shaped q)
    {n c : List Fr} {v i : Fr} (hn : n.length = 2) (hc : c.length = 2) (h : Value.Is p e q (n ++ c ++ [v, i])) :
    QCoinIs p e q n c v i ∧ q.nonce.limbs.length = 2 := by
  have hlens : q.nonce.limbs.length = 2 ∧ q.color.limbs.length = 2 := by
    obtain ⟨es, hl, rfl⟩ := hq
    rw [Value.width_qcoin] at hl
    match es, hl with
    | [_, _, _, _, _, _], _ => exact ⟨rfl, rfl⟩
  unfold Value.Is at h
  have e1 : Value.toExprs q =
      q.nonce.limbs ++ (q.color.limbs ++ ([q.value.expr] ++ ([q.mt_index.expr] ++ []))) := rfl
  rw [e1, List.append_assoc] at h
  obtain ⟨us, vs, huv, hu, hv⟩ := evalList_append_inv h
  have h1 := List.append_inj huv.symm (by rw [Damp.evalList_length hu, hlens.1, hn])
  rw [h1.1] at hu; rw [h1.2] at hv
  obtain ⟨us', vs', huv', hu', hv'⟩ := evalList_append_inv hv
  have h2 := List.append_inj huv'.symm (by rw [Damp.evalList_length hu', hlens.2, hc])
  rw [h2.1] at hu'; rw [h2.2] at hv'
  simp only [List.cons_append, List.nil_append, List.append_nil] at hv'
  obtain ⟨x, xs, hx, hxs, he⟩ := evalList_cons.1 hv'
  simp only [List.cons.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨y, ys, hy, hys, he'⟩ := evalList_cons.1 hxs
  simp only [List.cons.injEq] at he'
  obtain ⟨rfl, rfl⟩ := he'
  exact ⟨⟨hu, hu', hx, hy⟩, hlens.1⟩

theorem sendResult_value_len {r : ShieldedSendResult} (h : Value.Shaped r) :
    (Value.toExprs r.change.value).length = 5 := by
  obtain ⟨es, hl, rfl⟩ := h
  rw [Value.width_sendResult, Value.width_maybe, Value.width_coin] at hl
  match es, hl with
  | [_, _, _, _, _, _, _, _, _, _, _], _ => rfl

/-- The parts of a `ShieldedSendResult` meaning `b :: cs ++ os`. -/
theorem sendResult_parts {p : Zkir.Prims} {e : Env} {r : ShieldedSendResult} (hr : Value.Shaped r)
    {b : Fr} {cs os : List Fr} (hcs : cs.length = 5) (h : Value.Is p e r (b :: cs ++ os)) :
    r.change.isSome.expr.eval p e = some b ∧ Value.Is p e r.change.value cs ∧ Value.Is p e r.sent os := by
  have hl := sendResult_value_len hr
  unfold Value.Is at h ⊢
  have e1 : Value.toExprs r = r.change.isSome.expr :: (Value.toExprs r.change.value ++ (Value.toExprs r.sent ++ [])) :=
    rfl
  rw [e1, List.append_nil, List.cons_append] at h
  obtain ⟨x, xs, hx, hxs, he⟩ := evalList_cons.1 h
  simp only [List.cons.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨us, vs, huv, hu, hv⟩ := evalList_append_inv hxs
  have hlu : us.length = cs.length := by rw [Damp.evalList_length hu, hl, hcs]
  have h1 := List.append_inj huv.symm hlu
  rw [h1.1] at hu; rw [h1.2] at hv
  exact ⟨hx, hu, hv⟩

/-! ## Effects after `sendShielded` stay well formed -/

theorem sendSEffects_wf (H : Hooks) {σ : LedgerState} {es : List SV} {m0 m1 m2 : List (AV × SV)} {x y z : Nat}
    {nf cm cm₂ : List Fr} (selfR hasChange : Bool) (hwf : σ.WF) (heff : σ.effects = .array es)
    (hm0 : es[0]? = some (.map m0)) (hm1 : es[1]? = some (.map m1)) (hm2 : es[2]? = some (.map m2))
    (hx : AV.ofFields [.bytes 32] nf = some (hkey x)) (hy : AV.ofFields [.bytes 32] cm = some (hkey y))
    (hz : AV.ofFields [.bytes 32] cm₂ = some (hkey z)) :
    ({ σ with effects := .array (sendSEffects es m0 m1 m2 x y z selfR hasChange) } : LedgerState).WF := by
  let L : List SV → LedgerState := fun es' => { σ with effects := .array es' }
  let es₁ := es.set 0 (.map (assocSet (hkey x) .null m0))
  let es₈ := es₁.set 2 (.map (assocSet (hkey y) .null m2))
  let m1' := if selfR then assocSet (hkey y) .null m1 else m1
  let es₉ := if selfR then es₈.set 1 (.map m1') else es₈
  let esA := es₉.set 2 (.map (assocSet (hkey z) .null (assocSet (hkey y) .null m2)))
  have hm2₁ : es₁[2]? = some (.map m2) := by simp [es₁, List.getElem?_set_ne, hm2]
  have hm1₈ : es₈[1]? = some (.map m1) := by simp [es₈, es₁, List.getElem?_set_ne, hm1]
  have hm2₉ : es₉[2]? = some (.map (assocSet (hkey y) .null m2)) := by
    have : es₈[2]? = some (.map (assocSet (hkey y) .null m2)) := List.getElem?_set_self (by
      have := lt_of_getElem? hm2; simpa [es₁] using this)
    cases hs : selfR <;> simp [es₉, hs, List.getElem?_set_ne, this]
  have hm1₉ : es₉[1]? = some (.map m1') := by
    cases hs : selfR
    · simpa [es₉, m1', hs] using hm1₈
    · simp only [es₉, m1', hs, ite_true]; exact List.getElem?_set_self (lt_of_getElem? hm1₈)
  have hm1A : esA[1]? = some (.map m1') := by simp [esA, List.getElem?_set_ne, hm1₉]
  have hwf₁ : (L es₁).WF := claimed_wf H (by decide) hx hwf heff hm0
  have hwf₈ : (L es₈).WF := claimed_wf H (σ := L es₁) (by decide) hy hwf₁ rfl hm2₁
  have hwf₉ : (L es₉).WF := by
    cases hs : selfR
    · simpa [es₉, hs] using hwf₈
    · have := claimed_wf H (σ := L es₈) (by decide) hy hwf₈ rfl hm1₈
      simpa [es₉, m1', hs] using this
  have hwfA : (L esA).WF := claimed_wf H (σ := L es₉) (by decide) hz hwf₉ rfl hm2₉
  have hwfB := claimed_wf H (σ := L esA) (by decide) hz hwfA rfl hm1A
  cases hc : hasChange
  · simpa [sendSEffects, hc, L, es₉, es₈, es₁, m1'] using hwf₉
  · simpa [sendSEffects, hc, L, esA, es₉, es₈, es₁, m1'] using hwfB


/-! ## `tokens.spend` -/

section Spend
open Examples.Tokens
variable {ω : Type} (p : Zkir.Prims) (H : Hooks) (w : String → List Fr → ω → Option (List Fr × ω))

theorem grows_sendShielded (input : QualifiedShieldedCoinInfo) (recipient : Recipient) (value : Uint128) :
    Grows (sendShielded input recipient value) := by
  unfold sendShielded
  exact Grows.bind (Grows.valM (by rw [Kernel.self_eq]; exact Grows.ledgerRead _ _) _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.valM (Grows.sub _ _) _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.when_ _ (Grows.ledgerOp _ _)) fun _ => Grows.cond _ (Grows.pure' _) (Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _)

/-- `toSelf` (`right (kernel.self())`) under a guard meaning `gb`. -/
theorem toSelf_runs {s : Build} {st : Exec.State ω LedgerState} {gb : Bool} (hg : GuardIs p s st.runState gb)
    (cfs : List SV) (wa : AV) (selfFs : List Fr) (hctx : st.ledger.context = .array cfs)
    (hc0 : cfs[0]? = some (.cell wa)) (hself : fieldsOf [.bytes 32] wa.atoms = some selfFs) (hwf : st.ledger.WF) :
    XRuns p (oracles H (Damp.Exec.liftWitness w)) toSelf s st True
      (fun r e w' l => w' = st.private_ ∧ l = st.ledger ∧
        Value.Is p e r (Fr.ofBool false :: [0, 0] ++ selfOr gb selfFs) ∧
        (Value.toExprs r.left).length = 2 ∧ (Value.toExprs r.right).length = 2) := by
  unfold toSelf
  refine (XRuns.seq (ok₂ := True) (self_runs H p w hg cfs wa selfFs hctx hc0 hself hwf) (fun _ => Grows.pure' _)
    fun a s₁ st₁ hn₁ hgd₁ ha₁ hQ₁ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hP, hL, -, hsh⟩ := hQ₁.holds
  exact XRuns.pure fun e he => ⟨hP, hL, right_self_is p (hQ₁ e he).2.2.1, rfl, ContractAddress.shaped_len hsh⟩

/-- The ledger after `spend` before the change is stored: `sendShielded`'s
    effects (`sendSEffects`) and `last` (field 1) holding the coin sent, as `outv`. -/
def spendLedger (σ : LedgerState) (es : List SV) (m0 m1 m2 : List (AV × SV)) (x y z : Nat) (selfR hasChange : Bool)
    (outv : AV) : LedgerState :=
  ({ σ with effects := .array (sendSEffects es m0 m1 m2 x y z selfR hasChange) } : LedgerState).setField 1 (.cell outv)

theorem zeros_coin : AV.ofFields (alignOf ShieldedCoinInfo) (List.replicate 5 0) =
    some ⟨[.bytes 32, .bytes 32, .bytes 16], [0, 0, 0]⟩ := by
  simp [alignOf_coin, AV.ofFields, atomWidth, atomOfFields, atomFits, List.replicate]; decide

/-- **The body of `tokens.spend`.** The held coin (field 6) is read back as
    `n ++ c ++ [v, i]`; `to` means `Fr.ofBool u :: rl ++ rr` and `value` the
    number `k`; the hashes are as in `sendShielded_runs`; the coin sent
    (`outFs`) is stored as `outv`, the change coin (`chFs`) as `chv`, and the
    all-zero coin's commitment to the zero address (what the guarded-off
    `writeCoin` computes when there is no change) is `cmvZ`. The call
    completes exactly when `k ≤ v` and, if there is change, its commitment `z`
    has an index in the context (`idx`) and the qualified coin fits
    (`qualifyAV`). -/
theorem spend_runs (to : Recipient) (value : Uint128) (env : Env) (ω₀ : ω) (σ : LedgerState)
    (u : Bool) (rl rr : List Fr) (hrl : rl.length = 2) (hrr : rr.length = 2)
    (hto : Stable 6 env (fun e => Value.Is p e (disclose to) (Fr.ofBool u :: rl ++ rr)))
    (hsh : (Value.toExprs (disclose to).left).length = 2 ∧ (Value.toExprs (disclose to).right).length = 2)
    (k : Nat) (hval : Stable 6 env (fun e => Uint.Means p e (disclose value) k))
    (fields : List SV) (hst : σ.state = .array fields) (hfl : 6 < fields.length)
    (hw : AV) (hf6 : fields[6]? = some (.cell hw))
    (n c : List Fr) (v i : Fr) (hnl : n.length = 2) (hcl : c.length = 2) (hv : v.val < 2 ^ 128)
    (hread : fieldsOf (alignOf QualifiedShieldedCoinInfo) hw.atoms = some (n ++ c ++ [v, i]))
    (cfs : List SV) (wa : AV) (selfFs : List Fr) (hctx : σ.context = .array cfs)
    (hc0 : cfs[0]? = some (.cell wa)) (hself : fieldsOf [.bytes 32] wa.atoms = some selfFs)
    (idx : List (AV × SV)) (hidx : cfs[1]? = some (.map idx)) (hwf : σ.WF)
    (es : List SV) (m0 m1 m2 : List (AV × SV)) (heff : σ.effects = .array es)
    (hm0 : es[0]? = some (.map m0)) (hm1 : es[1]? = some (.map m1)) (hm2 : es[2]? = some (.map m2))
    (nf : List Fr) (x : Nat) (hnf : phashFs p coinPreimageAlign (cnPre (n ++ c ++ [v]) selfFs) = some nf)
    (hx : AV.ofFields [.bytes 32] nf = some (hkey x))
    (cm : List Fr) (y : Nat)
    (hcm : phashFs p coinPreimageAlign (ccPre (derivedNonceFs p "midnight:kernel:nonce_evolve" n ++ c ++
      [Fr.ofNat k]) u rl rr) = some cm)
    (hy : AV.ofFields [.bytes 32] cm = some (hkey y))
    (cm₂ : List Fr) (z : Nat)
    (hcm₂ : phashFs p coinPreimageAlign (ccPre (derivedNonceFs p "midnight:kernel:nonce_evolve/2" n ++ c ++
      [Fr.ofNat (v.val - k)]) false [0, 0] selfFs) = some cm₂)
    (hz : AV.ofFields [.bytes 32] cm₂ = some (hkey z))
    (ω₁ ω₂ ω₃ : ω)
    (hw₁ : w "createZswapInput" (n ++ c ++ [v, i]) ω₀ = some ([], ω₁))
    (hw₂ : w "createZswapOutput" ((derivedNonceFs p "midnight:kernel:nonce_evolve" n ++ c ++ [Fr.ofNat k]) ++
      (Fr.ofBool u :: rl ++ rr)) ω₁ = some ([], ω₂))
    (hw₃ : v.val - k ≠ 0 → w "createZswapOutput" ((derivedNonceFs p "midnight:kernel:nonce_evolve/2" n ++ c ++
      [Fr.ofNat (v.val - k)]) ++ (Fr.ofBool false :: [0, 0] ++ selfFs)) ω₂ = some ([], ω₃))
    (outv : AV) (houtv : AV.ofFields (alignOf ShieldedCoinInfo)
      (derivedNonceFs p "midnight:kernel:nonce_evolve" n ++ c ++ [Fr.ofNat k]) = some outv)
    (chv : AV) (hchv : AV.ofFields (alignOf ShieldedCoinInfo)
      (derivedNonceFs p "midnight:kernel:nonce_evolve/2" n ++ c ++ [Fr.ofNat (v.val - k)]) = some chv)
    (cmZ : List Fr) (cmvZ : AV)
    (hcmZ : phashFs p coinPreimageAlign (ccPre (List.replicate 5 0) false [0, 0] [0, 0]) = some cmZ)
    (hcmvZ : AV.ofFields [.bytes 32] cmZ = some cmvZ) :
    XRuns p (oracles H (Damp.Exec.liftWitness w)) (spend to value) { next := 6 } (Exec.State.start env ω₀ σ)
      (k ≤ v.val ∧ (v.val - k ≠ 0 → (qualifyAV chv idx (hkey z)).isSome = true))
      (fun r e w' l => Value.Is p e r [] ∧ w' = (if v.val - k = 0 then ω₂ else ω₃) ∧
        (if v.val - k = 0 then
          l = spendLedger σ es m0 m1 m2 x y z (!u && decide (rr = selfFs)) false outv
         else ∃ q, qualifyAV chv idx (hkey z) = some q ∧
          l = (spendLedger σ es m0 m1 m2 x y z (!u && decide (rr = selfFs)) true outv).setField 6 (.cell q))) := by
  have hsl := fieldsOf_bytes32_length hself
  let outFs := derivedNonceFs p "midnight:kernel:nonce_evolve" n ++ c ++ [Fr.ofNat k]
  let chFs := derivedNonceFs p "midnight:kernel:nonce_evolve/2" n ++ c ++ [Fr.ofNat (v.val - k)]
  let cb := !decide (v.val - k = 0)
  let selfR := !u && decide (rr = selfFs)
  let L₁ : LedgerState := { σ with effects := .array (sendSEffects es m0 m1 m2 x y z selfR cb) }
  have hwf₁ : L₁.WF := sendSEffects_wf H selfR cb hwf heff hm0 hm1 hm2 hx hy hz
  have hst₁ : L₁.state = .array fields := hst
  unfold spend
  -- 1. `(← held.read)`
  have h1 := ((XRuns.ledgerRead (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (s := { next := 6 })
    (st := Exec.State.start env ω₀ σ) (α := QualifiedShieldedCoinInfo) roundTrip_qcoin
    (mk := fun es => [.dup 0, .idx false false [fieldKey 6], .popeq false (alignOf QualifiedShieldedCoinInfo) es])
    (ReadOps.popeq_last [.dup 0, .idx false false [fieldKey 6]] false _) (by decide) (guardIs_top rfl)
    (res := some (n ++ c ++ [v, i], σ)) (fun e _ => read_req' (Cell.read_spec H held p e σ fields hw _ hst hf6
      (by decide) hwf hread))).addResult (ledgerRead_shaped _ _ _)).conseq (ok' := True)
    ⟨fun _ => trivial, fun _ => ⟨_, _, rfl, by simp [hnl, hcl, Value.width_qcoin]⟩⟩
    (Q' := fun r e w' l => w' = ω₀ ∧ l = σ ∧ Value.Is p e r (n ++ c ++ [v, i]) ∧ Value.Shaped r)
    (fun r e w' l ⟨⟨hw', ys, hy', hi⟩, hsh'⟩ => by
      simp only [Option.some.injEq, Prod.mk.injEq] at hy'; obtain ⟨rfl, rfl⟩ := hy'; exact ⟨hw', rfl, hi, hsh'⟩)
  refine (XRuns.seq (ok₂ := k ≤ v.val ∧ (v.val - k ≠ 0 → (qualifyAV chv idx (hkey z)).isSome = true)) h1
    (fun _ => Grows.bind (Grows.valM (grows_sendShielded _ _ _) _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ =>
      Grows.when_ _ (Grows.bind (Grows.bind (Grows.ledgerRead _ _) fun _ => Grows.pure' _) fun _ =>
        Grows.ledgerOp _ _))
    fun q s₁ st₁ hn₁ hgd₁ ha₁ hQ₁ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hP₁, hL₁, -, hshq⟩ := hQ₁.holds
  have hg₁ : GuardIs p s₁ st₁.runState true := guardIs_top (by rw [hgd₁])
  have hin : Stable s₁.next st₁.env (fun e => QCoinIs p e q n c v i) :=
    hQ₁.imp fun e h => (qcoin_parts hshq hnl hcl h.2.2.1).1
  have hqnl : q.nonce.limbs.length = 2 := (qcoin_parts hshq hnl hcl (hQ₁.holds.2.2.1)).2
  -- 2. `const r ← sendShielded q (disclose to) (disclose value)`
  have hS := sendShielded_runs H p w q (disclose to) (disclose value) hg₁ n c v i hqnl hcl hv hin k
    (hval.later ha₁ hn₁) u rl rr hrl hrr hsh (hto.later ha₁ hn₁) cfs wa selfFs (by rw [hL₁]; exact hctx) hc0 hself
    (by rw [hL₁]; exact hwf) es m0 m1 m2 (by rw [hL₁]; exact heff) hm0 hm1 hm2 nf x hnf hx cm y hcm hy cm₂ z hcm₂ hz
    ω₁ ω₂ ω₃ (by rw [hP₁]; exact hw₁) hw₂ hw₃
  let resFs := Fr.ofBool cb :: (if cb then chFs else List.replicate 5 0) ++ outFs
  have hres : ∀ e (r : ShieldedSendResult), Value.Is p e r (if v.val - k = 0
          then (Fr.ofBool false :: List.replicate (Value.width ShieldedCoinInfo) 0) ++
            (derivedNonceFs p "midnight:kernel:nonce_evolve" n ++ c ++ [Fr.ofNat k])
          else (Fr.ofBool true :: (derivedNonceFs p "midnight:kernel:nonce_evolve/2" n ++ c ++
            [Fr.ofNat (v.val - k)])) ++ (derivedNonceFs p "midnight:kernel:nonce_evolve" n ++ c ++ [Fr.ofNat k])) →
      Value.Is p e r resFs := by
    intro e r h
    by_cases h0 : v.val - k = 0
    · simpa [resFs, cb, h0, outFs, Value.width_coin] using h
    · simpa [resFs, cb, h0, outFs, chFs] using h
  have hresl : resFs.length = Value.width ShieldedSendResult := by
    rw [Value.width_sendResult, Value.width_maybe, Value.width_coin]
    cases hcb : cb <;> simp [resFs, hcb, outFs, chFs, derivedNonceFs, hcl]
  have h2 : XRuns p (oracles H (Damp.Exec.liftWitness w)) (valM (sendShielded q (disclose to) (disclose value)) "r") s₁ st₁ (k ≤ v.val)
      (fun r e w' l => Value.Is p e r resFs ∧ Value.Shaped r ∧ w' = (if v.val - k = 0 then ω₂ else ω₃) ∧ l = L₁) := by
    unfold valM
    refine (XRuns.seq (ok₂ := True) hS (fun _ => Grows.val _ _) fun r0 s₂ st₂ hn₂ hgd₂ ha₂ hQ₂ => ?_).conseq
      (by simp) fun _ _ _ _ h => h
    obtain ⟨hr0, hP₂, hL₂⟩ := hQ₂.holds
    have hlen : (Value.toExprs r0).length = Value.width ShieldedSendResult := by
      rw [← Damp.evalList_length (hres _ _ hr0), hresl]
    refine ((XRuns.val (p := p) (O := oracles H (Damp.Exec.liftWitness w)) roundTrip_sendResult "r" hlen
      (hQ₂.imp fun e h => hres e r0 h.1)).addResult (val_shaped r0 "r" s₂ hlen)).conseq Iff.rfl ?_
    intro r e w' l ⟨⟨h1, h2, h3⟩, h4⟩
    refine ⟨h1, h4, h2.trans hP₂, h3.trans ?_⟩
    rw [hL₂, hL₁]
  refine (XRuns.seq (ok₂ := v.val - k ≠ 0 → (qualifyAV chv idx (hkey z)).isSome = true) h2
    (fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ =>
      Grows.when_ _ (Grows.bind (Grows.bind (Grows.ledgerRead _ _) fun _ => Grows.pure' _) fun _ =>
        Grows.ledgerOp _ _))
    fun r s₂ st₂ hn₂ hgd₂ ha₂ hQ₂ => ?_).conseq Iff.rfl fun _ _ _ _ h => h
  obtain ⟨-, hshr, hP₂, hL₂⟩ := hQ₂.holds
  have hg₂ : GuardIs p s₂ st₂.runState true := guardIs_top (by rw [hgd₂, hgd₁])
  have hcsl : (if cb then chFs else List.replicate 5 0).length = 5 := by
    cases cb <;> simp [chFs, derivedNonceFs, hcl]
  have hparts : Stable s₂.next st₂.env (fun e => r.change.isSome.expr.eval p e = some (Fr.ofBool cb) ∧
      Value.Is p e r.change.value (if cb then chFs else List.replicate 5 0) ∧ Value.Is p e r.sent outFs) :=
    hQ₂.imp fun e h => sendResult_parts hshr hcsl h.1
  -- 3. `last.write r.sent`
  let L₂ : LedgerState := L₁.setField 1 (.cell outv)
  have hreq3 : ∀ e, Agree s₂.next st₂.env e → ∃ req, Exec.request p e
      [.push false (fieldKey last.index), .push true (alignedOf r.sent), .ins false 1] = some req ∧
      (oracles H (Damp.Exec.liftWitness w)).ledger req st₂.ledger = some ([], L₂) := by
    intro e he
    rw [hL₂]
    exact op_req' (Cell.write_spec H last p e L₁ fields r.sent outFs outv hst₁ (by show 1 < fields.length; omega) (by decide) hwf₁
      (hparts e he).2.2 houtv)
  refine (XRuns.seq (ok₂ := v.val - k ≠ 0 → (qualifyAV chv idx (hkey z)).isSome = true)
    (XRuns.ledgerOp (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (s := s₂) (st := st₂) (by simp) hg₂ hreq3)
    (fun _ => Grows.when_ _ (Grows.bind (Grows.bind (Grows.ledgerRead _ _) fun _ => Grows.pure' _) fun _ =>
        Grows.ledgerOp _ _))
    fun _ s₃ st₃ hn₃ hgd₃ ha₃ hQ₃ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hP₃, hL₃⟩ := hQ₃.holds
  simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hL₃
  have hg₃ : GuardIs p s₃ st₃.runState true := guardIs_top (by rw [hgd₃, hgd₂, hgd₁])
  have hparts₃ := hparts.later ha₃ hn₃
  have hwf₂ : L₂.WF := setField_WF hst₁ hwf₁ 1 _
  have hst₂ : L₂.state = .array (fields.set 1 (.cell outv)) := by simp [L₂, LedgerState.setField, hst₁]
  have hctx₂ : L₂.context = .array cfs := by simp [L₂, L₁, LedgerState.setField, hst, hctx]
  -- the change coin, its commitment, as `writeCoin` computes them under its guard
  have hcvB : AV.ofFields (alignOf ShieldedCoinInfo) (if cb then chFs else List.replicate 5 0) =
      some (if cb then chv else ⟨[.bytes 32, .bytes 32, .bytes 16], [0, 0, 0]⟩) := by
    cases cb
    · exact zeros_coin
    · exact hchv
  have hcmB : phashFs p coinPreimageAlign (ccPre (if cb then chFs else List.replicate 5 0) false [0, 0]
      (selfOr cb selfFs)) = some (if cb then cm₂ else cmZ) := by
    cases cb
    · exact hcmZ
    · exact hcm₂
  have hcmvB : AV.ofFields [.bytes 32] (if cb then cm₂ else cmZ) = some (if cb then hkey z else cmvZ) := by
    cases cb
    · exact hcmvZ
    · exact hz
  -- 4. `if% r.change.isSome then held.writeCoin r.change.value (← toSelf)`
  refine (XRuns.when_ (gb := true) (cb := cb) hg₃ (hparts₃.imp fun e h => h.1)
    (Grows.bind (Grows.bind (Grows.ledgerRead _ _) fun _ => Grows.pure' _) fun _ => Grows.ledgerOp _ _)
    (ok := cb = true → (qualifyAV (if cb then chv else ⟨[.bytes 32, .bytes 32, .bytes 16], [0, 0, 0]⟩) idx
      (if cb then hkey z else cmvZ)).isSome = true)
    (Q := fun _ _ w' l => w' = st₃.private_ ∧
      (if cb then ∃ q, qualifyAV chv idx (hkey z) = some q ∧ l = L₂.setField 6 (.cell q) else l = L₂))
    fun s' st' ctx => ?_).conseq ?_ ?_
  · obtain ⟨hn', ha', hP', hL', hg'⟩ := ctx
    simp only [Bool.true_and] at hg'
    have hLs' : st'.ledger = L₂ := by rw [hL', hL₃]
    refine (XRuns.seq (ok₂ := cb = true → (qualifyAV (if cb then chv else ⟨[.bytes 32, .bytes 32, .bytes 16],
        [0, 0, 0]⟩) idx (if cb then hkey z else cmvZ)).isSome = true)
      (toSelf_runs p H w hg' cfs wa selfFs (by rw [hLs']; exact hctx₂) hc0 hself (by rw [hLs']; exact hwf₂))
      (fun _ => Grows.ledgerOp _ _) fun a s'' st'' hn'' hgd'' ha'' hQ'' => ?_).conseq (by simp)
      fun _ _ _ _ h => h
    obtain ⟨hP'', hL'', -, hla, hra⟩ := hQ''.holds
    have hLs'' : st''.ledger = L₂ := by rw [hL'', hLs']
    have hg'' := GuardIs.later hg' ha'' hn'' hgd''
    have hcoin'' : Stable s''.next st''.env (fun e => Value.Is p e r.change.value
        (if cb then chFs else List.replicate 5 0)) :=
      ((hparts₃.transfer ha').mono hn' |>.later ha'' hn'').imp fun e h => h.2.1
    have h := Cell.writeCoin_runs H p w r.change.value a (coinFs := if cb then chFs else List.replicate 5 0)
      (cv := if cb then chv else ⟨[.bytes 32, .bytes 32, .bytes 16], [0, 0, 0]⟩) (u := false) (rl := [0, 0])
      (rr := selfOr cb selfFs) (cm := if cb then cm₂ else cmZ) (cmv := if cb then hkey z else cmvZ)
      (fields := fields.set 1 (.cell outv)) (cfs := cfs) (idx := idx) held hg'' hcoin'' hcvB rfl ⟨hla, hra⟩
      (hQ''.imp fun e h => h.2.2.1) hcmB hcmvB (by rw [hLs'']; exact hst₂) (by show 6 < _; simp; omega) (by decide)
      (by rw [hLs'']; exact hwf₂) (by rw [hLs'']; exact hctx₂) hidx
    refine h.conseq Iff.rfl fun _ _ w' l h' => ⟨h'.1.trans (hP''.trans hP'), ?_⟩
    have h2 := h'.2
    rw [hLs''] at h2
    cases hcb : cb
    · simp only [hcb, Bool.false_eq_true, ite_false] at h2 ⊢; exact h2
    · simp only [hcb, ite_true] at h2 ⊢; exact h2
  · cases hcb : cb
    · have h0 : v.val - k = 0 := by simpa [cb] using hcb
      simp [h0]
    · have h0 : v.val - k ≠ 0 := by simpa [cb] using hcb
      simp [h0]
  · intro _ e w' l ⟨hw', hl'⟩
    refine ⟨rfl, ?_, ?_⟩
    · rw [hw', hP₃, hP₂]
    · have hL2 : L₂ = spendLedger σ es m0 m1 m2 x y z (!u && decide (rr = selfFs)) cb outv := rfl
      by_cases h0 : v.val - k = 0
      · have hcb : cb = false := by simp [cb, h0]
        simp only [hcb, Bool.false_eq_true, ite_false, h0, ite_true] at hl' ⊢
        rw [hl', hL2, hcb]
      · have hcb : cb = true := by simp [cb, h0]
        simp only [hcb, ite_true, h0, ite_false] at hl' ⊢
        obtain ⟨q', hq', hl''⟩ := hl'
        exact ⟨q', hq', by rw [hl'', hL2, hcb]⟩

theorem spend_ranges : CircuitFnSpec.ranges (Recipient → Uint128 → CircuitM Unit) =
    Value.ranges Recipient ++ Value.ranges Uint128 := by
  show Value.ranges Recipient ++ (Value.ranges Uint128 ++ []) = _; rw [List.append_nil]

/-- The outcome of `spend`, as `spend_runs` states it. -/
def SpendOutcome (σ : LedgerState) (es : List SV) (m0 m1 m2 : List (AV × SV)) (x y z : Nat) (selfR : Bool)
    (outv chv : AV) (idx : List (AV × SV)) (v k : Nat) (ω₂ ω₃ : ω) (w' : ω) (l : LedgerState) : Prop :=
  w' = (if v - k = 0 then ω₂ else ω₃) ∧
    (if v - k = 0 then l = spendLedger σ es m0 m1 m2 x y z selfR false outv
     else ∃ q, qualifyAV chv idx (hkey z) = some q ∧ l = (spendLedger σ es m0 m1 m2 x y z selfR true outv).setField 6
       (.cell q))

/-- `tokens.spend` before optimization, through `mkCircuit_exec_of_XRuns`, on
    the inputs `to = (u, rl, rr)` and `value = kv`. -/
theorem spend_exec (ω₀ : ω) (σ : LedgerState)
    (u : Bool) (rl rr : List Fr) (hrl : rl.length = 2) (hrr : rr.length = 2) (kv : Fr) (hk128 : kv.val < 2 ^ 128)
    (fields : List SV) (hst : σ.state = .array fields) (hfl : 6 < fields.length)
    (hw : AV) (hf6 : fields[6]? = some (.cell hw))
    (n c : List Fr) (v i : Fr) (hnl : n.length = 2) (hcl : c.length = 2) (hv : v.val < 2 ^ 128)
    (hread : fieldsOf (alignOf QualifiedShieldedCoinInfo) hw.atoms = some (n ++ c ++ [v, i]))
    (cfs : List SV) (wa : AV) (selfFs : List Fr) (hctx : σ.context = .array cfs)
    (hc0 : cfs[0]? = some (.cell wa)) (hself : fieldsOf [.bytes 32] wa.atoms = some selfFs)
    (idx : List (AV × SV)) (hidx : cfs[1]? = some (.map idx)) (hwf : σ.WF)
    (es : List SV) (m0 m1 m2 : List (AV × SV)) (heff : σ.effects = .array es)
    (hm0 : es[0]? = some (.map m0)) (hm1 : es[1]? = some (.map m1)) (hm2 : es[2]? = some (.map m2))
    (nf : List Fr) (x : Nat) (hnf : phashFs p coinPreimageAlign (cnPre (n ++ c ++ [v]) selfFs) = some nf)
    (hx : AV.ofFields [.bytes 32] nf = some (hkey x))
    (cm : List Fr) (y : Nat)
    (hcm : phashFs p coinPreimageAlign (ccPre (derivedNonceFs p "midnight:kernel:nonce_evolve" n ++ c ++
      [Fr.ofNat kv.val]) u rl rr) = some cm)
    (hy : AV.ofFields [.bytes 32] cm = some (hkey y))
    (cm₂ : List Fr) (z : Nat)
    (hcm₂ : phashFs p coinPreimageAlign (ccPre (derivedNonceFs p "midnight:kernel:nonce_evolve/2" n ++ c ++
      [Fr.ofNat (v.val - kv.val)]) false [0, 0] selfFs) = some cm₂)
    (hz : AV.ofFields [.bytes 32] cm₂ = some (hkey z))
    (ω₁ ω₂ ω₃ : ω)
    (hw₁ : w "createZswapInput" (n ++ c ++ [v, i]) ω₀ = some ([], ω₁))
    (hw₂ : w "createZswapOutput" ((derivedNonceFs p "midnight:kernel:nonce_evolve" n ++ c ++ [Fr.ofNat kv.val]) ++
      (Fr.ofBool u :: rl ++ rr)) ω₁ = some ([], ω₂))
    (hw₃ : v.val - kv.val ≠ 0 → w "createZswapOutput" ((derivedNonceFs p "midnight:kernel:nonce_evolve/2" n ++ c ++
      [Fr.ofNat (v.val - kv.val)]) ++ (Fr.ofBool false :: [0, 0] ++ selfFs)) ω₂ = some ([], ω₃))
    (outv : AV) (houtv : AV.ofFields (alignOf ShieldedCoinInfo)
      (derivedNonceFs p "midnight:kernel:nonce_evolve" n ++ c ++ [Fr.ofNat kv.val]) = some outv)
    (chv : AV) (hchv : AV.ofFields (alignOf ShieldedCoinInfo)
      (derivedNonceFs p "midnight:kernel:nonce_evolve/2" n ++ c ++ [Fr.ofNat (v.val - kv.val)]) = some chv)
    (cmZ : List Fr) (cmvZ : AV)
    (hcmZ : phashFs p coinPreimageAlign (ccPre (List.replicate 5 0) false [0, 0] [0, 0]) = some cmZ)
    (hcmvZ : AV.ofFields [.bytes 32] cmZ = some cmvZ) :
    let xs := (Fr.ofBool u :: rl ++ rr) ++ [kv]
    ((Exec.run p (oracles H (Damp.Exec.liftWitness w)) spend.circuit xs ω₀ σ).isSome = true ↔
      rangesHold (Value.ranges Recipient ++ Value.ranges Uint128) xs = true ∧
        kv.val ≤ v.val ∧ (v.val - kv.val ≠ 0 → (qualifyAV chv idx (hkey z)).isSome = true)) ∧
    ∀ r, Exec.run p (oracles H (Damp.Exec.liftWitness w)) spend.circuit xs ω₀ σ = some r →
      r.outputs = [] ∧ SpendOutcome σ es m0 m1 m2 x y z (!u && decide (rr = selfFs)) outv chv idx v.val kv.val
        ω₂ ω₃ r.private_ r.ledger := by
  intro xs
  show ((Exec.run p (oracles H (Damp.Exec.liftWitness w)) (mkCircuit "spend" ["to", "value"] spend) xs ω₀ σ).isSome = true ↔ _) ∧ ∀ r,
    Exec.run p (oracles H (Damp.Exec.liftWitness w)) (mkCircuit "spend" ["to", "value"] spend) xs ω₀ σ = some r → _
  have hxl : xs.length = 6 := by simp [xs, hrl, hrr]
  by_cases hin : rangesHold (Value.ranges Recipient ++ Value.ranges Uint128) xs = true
  · let env : Env := fun v => xs.getD v 0
    have hto : Stable 6 env (fun e => Value.Is p e (disclose (Value.ofExprs (argVars 0 5) : Recipient))
        (Fr.ofBool u :: rl ++ rr)) := by
      intro e he
      refine disclose_is (roundTrip_either roundTrip_zswapKey roundTrip_contractAddress) rfl ?_
      have h := arg_is (p := p) (roundTrip_either roundTrip_zswapKey roundTrip_contractAddress) e 0
      have hm : (List.range' 0 (Value.width Recipient)).map e = Fr.ofBool u :: rl ++ rr := by
        have hW : Value.width Recipient = 5 := rfl
        rw [hW]
        have : (List.range' 0 5).map env = Fr.ofBool u :: rl ++ rr := by
          rw [range'_map_getD xs 0 5 (by omega)]
          show List.take 5 (List.drop 0 ((Fr.ofBool u :: rl ++ rr) ++ [kv])) = _
          match rl, hrl, rr, hrr with
          | [_, _], _, [_, _], _ => rfl
        rw [← this]
        exact List.map_congr_left fun v hv => (he v (by have := List.mem_range'_1.1 hv; omega)).symm
      rwa [hm] at h
    have hval : Stable 6 env (fun e => Uint.Means p e (disclose (Value.ofExprs [.var 5] : Uint128)) kv.val) := by
      intro e he
      refine uint128_means p ?_ hk128
      have h5 : e 5 = kv := by
        rw [← he 5 (by decide)]
        simp [env, xs, List.getD_eq_getElem?_getD, hrl, hrr]
      simp [disclose, Value.toExprs, Value.ofExprs, Uint.capped_eval uint128_bound, Expr.eval, h5]
    obtain ⟨h1, h2⟩ := mkCircuit_exec_of_XRuns (p := p) (O := oracles H (Damp.Exec.liftWitness w)) "spend" ["to", "value"] spend
      (xs := xs) (w := ω₀) (l := σ) (outs := [])
      (ok := kv.val ≤ v.val ∧ (v.val - kv.val ≠ 0 → (qualifyAV chv idx (hkey z)).isSome = true))
      (P := SpendOutcome σ es m0 m1 m2 x y z (!u && decide (rr = selfFs)) outv chv idx v.val kv.val ω₂ ω₃)
      (by rw [spend_ranges, hxl]; rfl) (by rw [spend_ranges]; exact hin)
      (by
        show XRuns p (oracles H (Damp.Exec.liftWitness w)) (spend (Value.ofExprs (argVars 0 5)) (Value.ofExprs [.var 5]))
          { next := 6 } _ _ _
        exact (spend_runs p H w _ _ env ω₀ σ u rl rr hrl hrr hto ⟨rfl, rfl⟩ kv.val hval fields hst hfl hw hf6 n c v i
          hnl hcl hv hread cfs wa selfFs hctx hc0 hself idx hidx hwf es m0 m1 m2 heff hm0 hm1 hm2 nf x hnf hx cm y
          hcm hy cm₂ z hcm₂ hz ω₁ ω₂ ω₃ hw₁ hw₂ hw₃ outv houtv chv hchv cmZ cmvZ hcmZ hcmvZ).conseq Iff.rfl
          fun r e w' l h => ⟨h.1, h.2.1, h.2.2⟩)
    refine ⟨h1.trans (by simp [hin]), fun r hr => h2 r hr⟩
  · have hnone : Exec.run p (oracles H (Damp.Exec.liftWitness w)) (mkCircuit "spend" ["to", "value"] spend) xs ω₀ σ = none := by
      rw [mkCircuit_exec]; split
      · rename_i h
        rw [spend_ranges] at h
        exact absurd h.2 hin
      · rfl
    rw [hnone]
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff, reduceCtorEq, false_implies, implies_true, and_true]
    exact fun h => hin h.1

/-- **`tokens.spend`, as a build ships it.** For any successful build of the
    `tokens` contract (any level the hash functions `p` suit, with or without
    `--ledger-opt`), the inputs `to = (u, rl, rr)` and `value = kv`, and every
    well-formed ledger state whose `held` cell (field 6) reads back as the
    qualified coin `n ++ c ++ [v, i]`, whose call context holds the contract's
    address (`selfFs`) and the commitment indices `idx`, and with the hashes,
    the witness answers and the stored coins as in `spend_runs`: the executor
    running the shipped circuit against the modelled VM completes exactly when
    the inputs pass their range checks, `kv ≤ v`, and, when there is change
    (`v - kv ≠ 0`), the change coin's commitment `z` has an index in `idx` and
    the qualified coin fits the VM's bound; it then returns nothing, leaves the
    private state the witness left (`ω₂`, or `ω₃` with change), and the ledger
    is `sendShielded`'s effects with `last` holding the coin sent and, with
    change, `held` holding the change qualified with its index
    (`SpendOutcome`); nothing else changes. And the ZKIR shipped for the
    circuit accepts the proof data the executor recorded. -/
theorem spend_shipped {level : OptLevel} {ledgerOpt : Bool} {shipped : Contract}
    {srcs : List (Circuit × Zkir.IrSource)} (hb : Examples.Tokens.contract.buildCore level ledgerOpt = .ok (shipped, srcs))
    (hp : level.SoundAt p) (ω₀ : ω) (σ : LedgerState)
    (u : Bool) (rl rr : List Fr) (hrl : rl.length = 2) (hrr : rr.length = 2) (kv : Fr) (hk128 : kv.val < 2 ^ 128)
    (fields : List SV) (hst : σ.state = .array fields) (hfl : 6 < fields.length)
    (hw : AV) (hf6 : fields[6]? = some (.cell hw))
    (n c : List Fr) (v i : Fr) (hnl : n.length = 2) (hcl : c.length = 2) (hv : v.val < 2 ^ 128)
    (hread : fieldsOf (alignOf QualifiedShieldedCoinInfo) hw.atoms = some (n ++ c ++ [v, i]))
    (cfs : List SV) (wa : AV) (selfFs : List Fr) (hctx : σ.context = .array cfs)
    (hc0 : cfs[0]? = some (.cell wa)) (hself : fieldsOf [.bytes 32] wa.atoms = some selfFs)
    (idx : List (AV × SV)) (hidx : cfs[1]? = some (.map idx)) (hwf : σ.WF)
    (es : List SV) (m0 m1 m2 : List (AV × SV)) (heff : σ.effects = .array es)
    (hm0 : es[0]? = some (.map m0)) (hm1 : es[1]? = some (.map m1)) (hm2 : es[2]? = some (.map m2))
    (nf : List Fr) (x : Nat) (hnf : phashFs p coinPreimageAlign (cnPre (n ++ c ++ [v]) selfFs) = some nf)
    (hx : AV.ofFields [.bytes 32] nf = some (hkey x))
    (cm : List Fr) (y : Nat)
    (hcm : phashFs p coinPreimageAlign (ccPre (derivedNonceFs p "midnight:kernel:nonce_evolve" n ++ c ++
      [Fr.ofNat kv.val]) u rl rr) = some cm)
    (hy : AV.ofFields [.bytes 32] cm = some (hkey y))
    (cm₂ : List Fr) (z : Nat)
    (hcm₂ : phashFs p coinPreimageAlign (ccPre (derivedNonceFs p "midnight:kernel:nonce_evolve/2" n ++ c ++
      [Fr.ofNat (v.val - kv.val)]) false [0, 0] selfFs) = some cm₂)
    (hz : AV.ofFields [.bytes 32] cm₂ = some (hkey z))
    (ω₁ ω₂ ω₃ : ω)
    (hw₁ : w "createZswapInput" (n ++ c ++ [v, i]) ω₀ = some ([], ω₁))
    (hw₂ : w "createZswapOutput" ((derivedNonceFs p "midnight:kernel:nonce_evolve" n ++ c ++ [Fr.ofNat kv.val]) ++
      (Fr.ofBool u :: rl ++ rr)) ω₁ = some ([], ω₂))
    (hw₃ : v.val - kv.val ≠ 0 → w "createZswapOutput" ((derivedNonceFs p "midnight:kernel:nonce_evolve/2" n ++ c ++
      [Fr.ofNat (v.val - kv.val)]) ++ (Fr.ofBool false :: [0, 0] ++ selfFs)) ω₂ = some ([], ω₃))
    (outv : AV) (houtv : AV.ofFields (alignOf ShieldedCoinInfo)
      (derivedNonceFs p "midnight:kernel:nonce_evolve" n ++ c ++ [Fr.ofNat kv.val]) = some outv)
    (chv : AV) (hchv : AV.ofFields (alignOf ShieldedCoinInfo)
      (derivedNonceFs p "midnight:kernel:nonce_evolve/2" n ++ c ++ [Fr.ofNat (v.val - kv.val)]) = some chv)
    (cmZ : List Fr) (cmvZ : AV)
    (hcmZ : phashFs p coinPreimageAlign (ccPre (List.replicate 5 0) false [0, 0] [0, 0]) = some cmZ)
    (hcmvZ : AV.ofFields [.bytes 32] cmZ = some cmvZ) :
    let xs := (Fr.ofBool u :: rl ++ rr) ++ [kv]
    ∃ src, (buildPassWith level ledgerOpt spend.circuit, src) ∈ srcs ∧
      ((∃ r, Exec.run p (oracles H (Damp.Exec.liftWitness w)) (buildPassWith level ledgerOpt spend.circuit) xs ω₀ σ = some r) ↔
        rangesHold (Value.ranges Recipient ++ Value.ranges Uint128) xs = true ∧
          kv.val ≤ v.val ∧ (v.val - kv.val ≠ 0 → (qualifyAV chv idx (hkey z)).isSome = true)) ∧
      ∀ r, Exec.run p (oracles H (Damp.Exec.liftWitness w)) (buildPassWith level ledgerOpt spend.circuit) xs ω₀ σ = some r →
        (r.outputs = [] ∧ SpendOutcome σ es m0 m1 m2 x y z (!u && decide (rr = selfFs)) outv chv idx v.val kv.val
          ω₂ ω₃ r.private_ r.ledger) ∧
        src.run p xs r.priv r.pub = some { outputs := r.outputs, groups := r.groups } :=
  shipped_of hb hp (by simp [Examples.Tokens.contract, Contract.allCircuits]) H (Damp.Exec.liftWitness w) (witnessesOK_lift w) _ ω₀ σ hwf
    (P := fun o w' l => o = [] ∧ SpendOutcome σ es m0 m1 m2 x y z (!u && decide (rr = selfFs)) outv chv idx v.val
      kv.val ω₂ ω₃ w' l)
    (spend_exec p H w ω₀ σ u rl rr hrl hrr kv hk128 fields hst hfl hw hf6 n c v i hnl hcl hv hread cfs wa selfFs hctx
      hc0 hself idx hidx hwf es m0 m1 m2 heff hm0 hm1 hm2 nf x hnf hx cm y hcm hy cm₂ z hcm₂ hz ω₁ ω₂ ω₃ hw₁ hw₂ hw₃
      outv houtv chv hchv cmZ cmvZ hcmZ hcmvZ)

end Spend

end Examples.CoinProofs
