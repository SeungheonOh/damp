/-
The token library (`Damp/Lang/Tokens.lean`) end to end: each operation, run by
the executor (`Exec.steps` via `XRuns`) against the modelled ledger
(`oracles H (Damp.Exec.liftWitness w)`): when it completes, its result, the private state, and the
exact ledger state afterwards. `receiveShielded`, the unshielded operations and
the balance reads are stated under a guard meaning `gb` (both values in one
statement); `mintShieldedToken`, `sendShielded`, `mergeCoin` (and their
`Immediate` forms) under a guard that holds.

**Nothing is assumed about hashes.** Commitments, nullifiers, token types and
derived nonces are whatever the circuit computes with the executor's
`p : Prims` (`phashFs`, `p.transientHash`, `TokensValues.lean`); the theorems
take those field elements as given (`hcm : phashFs p … = some cm`) and say what
the ledger does with them. With the guard off the circuit still computes them,
from the zeros an inactive ledger read returns (`selfOr`), so a hash must
evaluate there too.

The built-in witnesses `createZswapInput` / `createZswapOutput` are answered by
the witness oracle `w` of `oracles H (Damp.Exec.liftWitness w)` (the executor answers them itself); a
theorem states the answer it needs: no field elements, and the private state
afterwards.
-/
import Damp.Proofs.Ledger.TokensValues
import Damp.Proofs.Ledger.Tokens
import Damp.Proofs.Ledger.Kernel

namespace Damp.Ledger
open Damp.IR Damp.Impact

set_option linter.unusedSimpArgs false

/-! ## Shared steps -/

theorem read_req' {α : Type} [Value α] {p : Zkir.Prims} {mk : List Expr → List (Impact.Op Expr)} {e : Env}
    {R : List (Impact.Op Fr) → Prop}
    (h : ∃ req, (emitted (ledgerRead α mk)).bind (Exec.request p e) = some req ∧ R req) :
    ∃ req, Exec.request p e (mk (readVars α)) = some req ∧ R req := by
  rw [emitted_ledgerRead] at h; exact h

theorem op_req' {p : Zkir.Prims} {ops : List (Impact.Op Expr)} {e : Env} {R : List (Impact.Op Fr) → Prop}
    (h : ∃ req, (emitted (ledgerOp [] ops)).bind (Exec.request p e) = some req ∧ R req) :
    ∃ req, Exec.request p e ops = some req ∧ R req := h

/-- What a read of `kernel.self()` gives under a guard meaning `gb`: the
    address's limbs, or zeros when the guard is off. -/
def selfOr (gb : Bool) (selfFs : List Fr) : List Fr := if gb then selfFs else [0, 0]

theorem Fr.ofInt_zero : Fr.ofInt 0 = 0 := rfl

theorem fieldsOf_bytes32_length {atoms : List Nat} {ys : List Fr} (h : fieldsOf [.bytes 32] atoms = some ys) :
    ys.length = 2 := by
  match atoms with
  | [] => simp [fieldsOf] at h
  | x :: xs => simp [fieldsOf, fieldsOfAtom] at h; subst h; simp

theorem selfOr_length {gb : Bool} {selfFs : List Fr} (h : selfFs.length = 2) : (selfOr gb selfFs).length = 2 := by
  cases gb <;> simp [selfOr, h]

/-- A Zswap claim leaves a well-formed state well formed. -/
theorem claimed_wf (H : Hooks) {σ : LedgerState} {es : List SV} {m : List (AV × SV)} {i x : Nat} (hi : i ≤ 2)
    {ks : List Fr} (hks : AV.ofFields [.bytes 32] ks = some ⟨[.bytes 32], [x]⟩) (hwf : σ.WF)
    (heff : σ.effects = .array es) (hm : es[i]? = some (.map m)) :
    ({ σ with effects := .array (es.set i (.map (assocSet ⟨[.bytes 32], [x]⟩ .null m))) } : LedgerState).WF := by
  obtain ⟨y, hy, he⟩ := bytes32_key hks
  simp only [AV.mk.injEq, List.cons.injEq, and_true, true_and] at he
  subst he
  exact ledgerOracle_wf (claimReq_spec H σ es m i ⟨[.bytes 32], ks⟩ _ (by omega) hwf heff hm hks (effectEntry_hash hi hy))

section
variable {ω : Type} (H : Hooks) (p : Zkir.Prims) (w : String → List Fr → ω → Option (List Fr × ω))

theorem Kernel.self_eq : Kernel.self = ledgerRead ContractAddress (fun es =>
    [.dup 2, .idx true false [fieldKey 0], .popeq true [.bytes 32] es]) := rfl

/-- **`kernel.self()` under a guard meaning `gb`**: the address's limbs
    `selfFs` (zeros when off); the ledger and private state unchanged. -/
theorem self_runs {s : Build} {st : Exec.State ω LedgerState} {gb : Bool} (hg : GuardIs p s st.runState gb)
    (cfs : List SV) (wa : AV) (selfFs : List Fr) (hctx : st.ledger.context = .array cfs)
    (hc0 : cfs[0]? = some (.cell wa)) (hself : fieldsOf [.bytes 32] wa.atoms = some selfFs) (hwf : st.ledger.WF) :
    XRuns p (oracles H (Damp.Exec.liftWitness w)) Kernel.self s st True
      (fun r e w' l => w' = st.private_ ∧ l = st.ledger ∧ Value.Is p e r (selfOr gb selfFs) ∧ Value.Shaped r) := by
  rw [Kernel.self_eq]
  have h := XRuns.ledgerReadG (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (s := s) (st := st) (gb := gb) roundTrip_contractAddress
    (ReadOps.popeq_last [.dup 2, .idx true false [fieldKey 0]] true [.bytes 32]) (by decide) hg
    (res := some (selfFs, st.ledger)) (fun e _ =>
      read_req' (Kernel.self_spec H p e st.ledger cfs wa selfFs hctx hc0 hwf hself))
  have hsh := ledgerRead_shaped ContractAddress (fun es => [.dup 2, .idx true false [fieldKey 0], .popeq true [.bytes 32] es]) s
  refine (h.addResult hsh).conseq ⟨fun _ => trivial, fun _ _ => ⟨selfFs, _, rfl, fieldsOf_bytes32_length hself⟩⟩ ?_
  intro r e w' l ⟨⟨hw, hq⟩, hsh⟩
  refine ⟨hw, ?_, ?_, hsh⟩
  · cases gb with
    | true => simp only [ite_true] at hq; obtain ⟨ys, hy, -⟩ := hq; simp at hy; exact hy.2.symm
    | false => simp only [ite_false, Bool.false_eq_true] at hq; exact hq.1
  · cases gb with
    | true => simp only [ite_true] at hq; obtain ⟨ys, hy, hi⟩ := hq; simp at hy; rw [hy.1]; exact hi
    | false => simp only [ite_false, Bool.false_eq_true] at hq; exact hq.2

/-- `right a` for a contract address `a` meaning `as`: `[0, 0, 0] ++ as`. -/
theorem right_self_is {e : Env} {a : ContractAddress} {as : List Fr} (ha : Value.Is p e a as) :
    Value.Is p e (right a : Either ZswapCoinPublicKey ContractAddress) (Fr.ofBool false :: [0, 0] ++ as) :=
  either_mk_is (p := p) rfl rfl ha

theorem right_toExprs_length {a : ContractAddress} (ha : Value.Shaped a) :
    (Value.toExprs (right a : Either ZswapCoinPublicKey ContractAddress)).length =
      Value.width (Either ZswapCoinPublicKey ContractAddress) := by
  have := ContractAddress.shaped_len ha
  rw [Value.width_either]
  show (Boolean.false.expr :: (Value.toExprs (Value.zero ZswapCoinPublicKey) ++ a.bytes.limbs)).length = _
  simp [this]; rfl

/-- **`receiveShielded coin`**, under a guard meaning `gb`, `coin` meaning
    `coinFs`, the context's address meaning `selfFs`, and the commitment of the
    coin sent to this contract (what the circuit hashes, `ccPre`) being `cm`,
    the 32-byte atom `x`. With the guard on: it asks the witness oracle to add
    the output `createZswapOutput(coin, right(self))`, which must answer
    nothing; then it completes, with the private state the oracle left, and
    the only change to the ledger is `x` added to the coins received (effects
    slot 1). With the guard off: nothing is asked and nothing changes. -/
theorem receiveShielded_runs (coin : ShieldedCoinInfo) {s : Build} {st : Exec.State ω LedgerState} {gb : Bool}
    (hg : GuardIs p s st.runState gb) (coinFs : List Fr)
    (hcoin : Stable s.next st.env (fun e => Value.Is p e coin coinFs))
    (cfs : List SV) (wa : AV) (selfFs : List Fr) (hctx : st.ledger.context = .array cfs)
    (hc0 : cfs[0]? = some (.cell wa)) (hself : fieldsOf [.bytes 32] wa.atoms = some selfFs) (hwf : st.ledger.WF)
    (es : List SV) (m : List (AV × SV)) (heff : st.ledger.effects = .array es) (hm : es[1]? = some (.map m))
    (cm : List Fr) (hcm : phashFs p coinPreimageAlign (ccPre coinFs false [0, 0] (selfOr gb selfFs)) = some cm)
    (x : Nat) (hx : AV.ofFields [.bytes 32] cm = some ⟨[.bytes 32], [x]⟩) :
    XRuns p (oracles H (Damp.Exec.liftWitness w)) (receiveShielded coin) s st
      (gb = true → ∃ w', w "createZswapOutput" (coinFs ++ (Fr.ofBool false :: [0, 0] ++ selfFs)) st.private_ =
        some ([], w'))
      (fun _ _ w' l => if gb then
          w "createZswapOutput" (coinFs ++ (Fr.ofBool false :: [0, 0] ++ selfFs)) st.private_ = some ([], w') ∧
          l = { st.ledger with effects := .array (es.set 1 (.map (assocSet ⟨[.bytes 32], [x]⟩ .null m))) }
        else w' = st.private_ ∧ l = st.ledger) := by
  have hsl := fieldsOf_bytes32_length hself
  unfold receiveShielded
  refine (XRuns.seq (ok₂ := gb = true → ∃ w', w "createZswapOutput"
      (coinFs ++ (Fr.ofBool false :: [0, 0] ++ selfFs)) st.private_ = some ([], w')) (self_runs H p w hg cfs wa selfFs hctx hc0 hself hwf)
    (fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.ledgerOp _ _)
    fun a s₁ st₁ hn₁ hgd₁ ha₁ hQ₁ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hw₁, hl₁, -, hsh₁⟩ := hQ₁.holds
  have hg₁ := GuardIs.later hg ha₁ hn₁ hgd₁
  -- `const recipient := right self`
  have hlen := right_toExprs_length hsh₁
  refine (XRuns.seq (ok₂ := gb = true → ∃ w', w "createZswapOutput"
      (coinFs ++ (Fr.ofBool false :: [0, 0] ++ selfFs)) st.private_ = some ([], w')) ((XRuns.val (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (s := s₁) (st := st₁) (roundTrip_either roundTrip_zswapKey
      roundTrip_contractAddress) (x := (right a : Either ZswapCoinPublicKey ContractAddress)) "recipient"
      hlen (hQ₁.imp fun e h => right_self_is p h.2.2.1)).addResult (val_shaped _ "recipient" s₁ hlen))
    (fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.ledgerOp _ _)
    fun r s₂ st₂ hn₂ hgd₂ ha₂ hQ₂ => ?_).conseq (ok' := gb = true → ∃ w', w "createZswapOutput"
      (coinFs ++ (Fr.ofBool false :: [0, 0] ++ selfFs)) st.private_ = some ([], w')) (by simp) fun _ _ _ _ h => h
  obtain ⟨⟨hr₂, hw₂, hl₂⟩, hshr⟩ := hQ₂.holds
  have hg₂ := GuardIs.later hg₁ ha₂ hn₂ hgd₂
  have hA₂ : Agree s.next st.env st₂.env := ha₁.trans (ha₂.mono hn₁)
  have hcoin₂ := hcoin.later hA₂ (Nat.le_trans hn₁ hn₂)
  have hrecip : Stable s₂.next st₂.env (fun e => Value.Is p e r (Fr.ofBool false :: [0, 0] ++ selfOr gb selfFs)) :=
    hQ₂.imp fun e h => h.1.1
  -- `createZswapOutput coin recipient`
  have hargs : Expr.evalList p st₂.env (Value.toExprs coin ++ Value.toExprs r) =
      some (coinFs ++ (Fr.ofBool false :: [0, 0] ++ selfOr gb selfFs)) :=
    evalList_append_some hcoin₂.holds hrecip.holds
  refine (XRuns.seq (ok₂ := True) (XRuns.askWitness0G_iso (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (α := Unit) rfl rfl "createZswapOutput" hg₂ hargs)
    (fun _ => Grows.ledgerOp _ _) fun u s₃ st₃ hn₃ hgd₃ ha₃ hQ₃ => ?_).conseq (ok' := gb = true → ∃ w',
      w "createZswapOutput" (coinFs ++ (Fr.ofBool false :: [0, 0] ++ selfFs)) st.private_ = some ([], w'))
    (by
      rw [hw₂, hw₁]
      cases gb <;> simp [selfOr, oracles])
    fun _ _ _ _ h => h
  obtain ⟨hl₃, hw₃⟩ := hQ₃.holds
  have hg₃ := GuardIs.later hg₂ ha₃ hn₃ hgd₃
  -- `Kernel.claimZswapCoinReceive (coinCommitment coin recipient)`
  let σ' : LedgerState := { st.ledger with effects := .array (es.set 1 (.map (assocSet ⟨[.bytes 32], [x]⟩ .null m))) }
  have hreq : ∀ e, Agree s₃.next st₃.env e → ∃ req, Exec.request p e
      [.swap 0, .idx true true [fieldKey 1], .push false (alignedOf (coinCommitment coin r)), .pushNull false,
        .ins true 2, .swap 0] = some req ∧ (oracles H (Damp.Exec.liftWitness w)).ledger req st₃.ledger = some ([], σ') := by
    intro e he
    have hc := (hcoin₂.later ha₃ hn₃) e he
    have hre := (hrecip.later ha₃ hn₃) e he
    have hcm' := coinCommitment_is hc (Either.shaped_parts hshr) rfl hre hcm
    rw [hl₃, hl₂, hl₁]
    exact op_req' (Kernel.claimZswapCoinReceive_spec H p e st.ledger es m _ cm _ hwf heff hm hcm' hx)
  refine (XRuns.ledgerOpG (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (s := s₃) (st := st₃) (gb := gb) (by simp) hg₃ hreq).conseq
    (by simp) fun _ _ w' l h => ?_
  obtain ⟨hw', hl'⟩ := h
  cases gb with
  | true =>
    simp only [ite_true, Option.some.injEq, Prod.mk.injEq, true_and] at hl' hw₃ ⊢
    refine ⟨?_, hl'.symm⟩
    rw [hw', ← hw₃, hw₂, hw₁]; simp [selfOr, oracles]
  | false =>
    simp only [Bool.false_eq_true, ite_false] at hl' hw₃ ⊢
    exact ⟨hw'.trans (hw₃.trans (hw₂.trans hw₁)), hl'.trans (hl₃.trans (hl₂.trans hl₁))⟩

/-! ## Balance comparisons (the VM's `lt` takes `u64` operands) -/

/-- The balance atom the context holds for a token type stored as `kv`: 0
    when absent, the cell's one atom otherwise. -/
def balAtom (bal : List (AV × SV)) (kv : AV) : Option Nat :=
  match assocGet kv bal with
  | none => some 0
  | some (.cell ⟨_, [B]⟩) => some B
  | _ => none

/-- **`Kernel.balanceLessThan t amount`**: with the balance atom `B` and the
    amount `av`, it answers `B < av` exactly when both fit 64 bits (the VM's
    `lt` pops two `u64`s); otherwise the request fails, the whole transaction
    with it, even though a balance and an amount are `u128`s. -/
theorem Kernel.balanceLessThan_spec (H : Hooks) (p : Zkir.Prims) (env : Env) (σ : LedgerState) (t : TokenType)
    (amount : Uint128) (ks : List Fr) (kv : AV) (hk : Expr.evalList p env (Value.toExprs t) = some ks)
    (hkv : AV.ofFields alignTokenType ks = some kv) (av : Fr) (hav : amount.expr.eval p env = some av)
    (cfs : List SV) (bal : List (AV × SV)) (hctx : σ.context = .array cfs) (hb : cfs[5]? = some (.map bal))
    (hwf : σ.WF) (B : Nat) (hB : balAtom bal kv = some B) :
    ∃ req, (emitted (Kernel.balanceLessThan t amount)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = if B < 2 ^ 64 ∧ av.val < 2 ^ 64 then some ([Fr.ofBool (decide (B < av.val))], σ)
        else none := by
  have he : Kernel.balanceLessThan t amount = ledgerRead Boolean (fun es =>
      [.dup 2, .idx true false [fieldKey 5], .dup 0, .push false (alignedOf t), .member, .branch 3, .pop,
       .push false ⟨[.bytes 16], [.const 0]⟩, .jmp 1, .idx true false [alignedOf t],
       .push false ⟨[.bytes 16], [amount.expr]⟩, .lt, .popeq true [.bytes 1] es]) := rfl
  rw [he, emitted_ledgerRead]
  rw [evalList_eq_mapM] at hk
  refine ⟨[.dup 2, .idx true false [⟨[.bytes 1], [Fr.ofInt 5]⟩], .dup 0, .push false ⟨alignTokenType, ks⟩, .member,
    .branch 3, .pop, .push false ⟨[.bytes 16], [Fr.ofInt 0]⟩, .jmp 1, .idx true false [⟨alignTokenType, ks⟩],
    .push false ⟨[.bytes 16], [av]⟩, .lt, .popeq true [.bytes 1] []], ?_, ?_⟩
  · simp [Exec.request, Op.mapM, Aligned.mapM, Exec.blank, fieldKey, Expr.eval, mapM_eval_readVars, alignedOf, hk, hav]
    rfl
  · have hkey : AV.ofFields [.bytes 1] [Fr.ofInt 5] = some ⟨[.bytes 1], [5]⟩ := ofAligned_byteKey (i := 5) (by decide)
    have h00 : (Fr.ofInt 0).val = 0 := rfl
    have h0 : AV.ofFields [.bytes 16] [Fr.ofInt 0] = some ⟨[.bytes 16], [0]⟩ := by
      simp [AV.ofFields, atomWidth, atomOfFields, atomFits, h00]
    by_cases ha128' : ¬ av.val < 2 ^ 128
    · have ha128 := ha128'
      rw [ledgerOracle_of_toR_none H (o := .push false ⟨[.bytes 16], [av]⟩) (by simp)
        (by simp [Op.toR, AV.ofAligned, AV.ofFields, atomWidth, atomOfFields, atomFits, ha128])]
      have : ¬ av.val < 2 ^ 64 := fun h => ha128 (Nat.lt_trans h (by decide))
      simp [this]
    have ha128 : av.val < 2 ^ 128 := Decidable.not_not.1 ha128'
    have hav' : AV.ofFields [.bytes 16] [av] = some ⟨[.bytes 16], [av.val]⟩ := by
      simp [AV.ofFields, atomWidth, atomOfFields, atomFits, ha128]
    rw [LedgerState.WF] at hwf
    obtain ⟨ctx, eff, st⟩ := σ
    simp only at hctx hwf ⊢
    subst hctx
    have hi := lt_of_getElem? hb
    have hb' := getElem_of_getElem? hb
    have hbool := fieldsOf_bool (decide (B < av.val))
    simp only [decide_eq_true_eq] at hbool
    unfold balAtom at hB
    cases hg : assocGet kv bal with
    | none =>
      rw [hg] at hB; simp at hB; subst hB
      by_cases h64 : av.val < 2 ^ 64
      · vm_simp [hkey, hkv, h0, hav', hwf, hi, hb, hb', hg, AV.ofBool, readBack_cons, hbool, h64]
      · vm_simp [hkey, hkv, h0, hav', hwf, hi, hb, hb', hg, AV.ofBool, readBack_cons, hbool, h64]
    | some v =>
      rw [hg] at hB
      match v, hB with
      | .cell ⟨al, [B']⟩, hB =>
        simp at hB; subst hB
        by_cases h64 : av.val < 2 ^ 64
        · by_cases hB64 : B' < 2 ^ 64
          · vm_simp [hkey, hkv, h0, hav', hwf, hi, hb, hb', hg, AV.ofBool, readBack_cons, hbool, h64, hB64]
          · vm_simp [hkey, hkv, h0, hav', hwf, hi, hb, hb', hg, AV.ofBool, readBack_cons, hbool, h64, hB64]
        · by_cases hB64 : B' < 2 ^ 64
          · vm_simp [hkey, hkv, h0, hav', hwf, hi, hb, hb', hg, AV.ofBool, readBack_cons, hbool, h64, hB64]
          · vm_simp [hkey, hkv, h0, hav', hwf, hi, hb, hb', hg, AV.ofBool, readBack_cons, hbool, h64, hB64]

/-- **`Kernel.balanceGreaterThan t amount`**: with the balance atom `B` and the
    amount `av`, it answers `av < B` exactly when both fit 64 bits (the VM's
    `lt` pops two `u64`s); otherwise the request fails, the whole transaction
    with it, even though a balance and an amount are `u128`s. -/
theorem Kernel.balanceGreaterThan_spec (H : Hooks) (p : Zkir.Prims) (env : Env) (σ : LedgerState) (t : TokenType)
    (amount : Uint128) (ks : List Fr) (kv : AV) (hk : Expr.evalList p env (Value.toExprs t) = some ks)
    (hkv : AV.ofFields alignTokenType ks = some kv) (av : Fr) (hav : amount.expr.eval p env = some av)
    (cfs : List SV) (bal : List (AV × SV)) (hctx : σ.context = .array cfs) (hb : cfs[5]? = some (.map bal))
    (hwf : σ.WF) (B : Nat) (hB : balAtom bal kv = some B) :
    ∃ req, (emitted (Kernel.balanceGreaterThan t amount)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ = if B < 2 ^ 64 ∧ av.val < 2 ^ 64 then some ([Fr.ofBool (decide (av.val < B))], σ)
        else none := by
  have he : Kernel.balanceGreaterThan t amount = ledgerRead Boolean (fun es =>
      [.push false ⟨[.bytes 16], [amount.expr]⟩, .dup 3, .idx true false [fieldKey 5], .dup 0,
       .push false (alignedOf t), .member, .branch 3, .pop,
       .push false ⟨[.bytes 16], [.const 0]⟩, .jmp 1, .idx true false [alignedOf t], .lt, .popeq true [.bytes 1] es]) :=
    rfl
  rw [he, emitted_ledgerRead]
  rw [evalList_eq_mapM] at hk
  refine ⟨[.push false ⟨[.bytes 16], [av]⟩, .dup 3, .idx true false [⟨[.bytes 1], [Fr.ofInt 5]⟩], .dup 0,
    .push false ⟨alignTokenType, ks⟩, .member,
    .branch 3, .pop, .push false ⟨[.bytes 16], [Fr.ofInt 0]⟩, .jmp 1, .idx true false [⟨alignTokenType, ks⟩],
    .lt, .popeq true [.bytes 1] []], ?_, ?_⟩
  · simp [Exec.request, Op.mapM, Aligned.mapM, Exec.blank, fieldKey, Expr.eval, mapM_eval_readVars, alignedOf, hk, hav]
    rfl
  · have hkey : AV.ofFields [.bytes 1] [Fr.ofInt 5] = some ⟨[.bytes 1], [5]⟩ := ofAligned_byteKey (i := 5) (by decide)
    have h00 : (Fr.ofInt 0).val = 0 := rfl
    have h0 : AV.ofFields [.bytes 16] [Fr.ofInt 0] = some ⟨[.bytes 16], [0]⟩ := by
      simp [AV.ofFields, atomWidth, atomOfFields, atomFits, h00]
    by_cases ha128' : ¬ av.val < 2 ^ 128
    · have ha128 := ha128'
      rw [ledgerOracle_of_toR_none H (o := .push false ⟨[.bytes 16], [av]⟩) (by simp)
        (by simp [Op.toR, AV.ofAligned, AV.ofFields, atomWidth, atomOfFields, atomFits, ha128])]
      have : ¬ av.val < 2 ^ 64 := fun h => ha128 (Nat.lt_trans h (by decide))
      simp [this]
    have ha128 : av.val < 2 ^ 128 := Decidable.not_not.1 ha128'
    have hav' : AV.ofFields [.bytes 16] [av] = some ⟨[.bytes 16], [av.val]⟩ := by
      simp [AV.ofFields, atomWidth, atomOfFields, atomFits, ha128]
    rw [LedgerState.WF] at hwf
    obtain ⟨ctx, eff, st⟩ := σ
    simp only at hctx hwf ⊢
    subst hctx
    have hi := lt_of_getElem? hb
    have hb' := getElem_of_getElem? hb
    have hbool := fieldsOf_bool (decide (av.val < B))
    simp only [decide_eq_true_eq] at hbool
    have hbool0 := fieldsOf_bool false
    simp only [Bool.false_eq_true, ite_false] at hbool0
    unfold balAtom at hB
    cases hg : assocGet kv bal with
    | none =>
      rw [hg] at hB; simp at hB; subst hB
      by_cases h64 : av.val < 2 ^ 64
      · vm_simp [hkey, hkv, h0, hav', hwf, hi, hb, hb', hg, AV.ofBool, readBack_cons, hbool, hbool0, h64]
      · vm_simp [hkey, hkv, h0, hav', hwf, hi, hb, hb', hg, AV.ofBool, readBack_cons, hbool, hbool0, h64]
    | some v =>
      rw [hg] at hB
      match v, hB with
      | .cell ⟨al, [B']⟩, hB =>
        simp at hB; subst hB
        by_cases h64 : av.val < 2 ^ 64
        · by_cases hB64 : B' < 2 ^ 64
          · vm_simp [hkey, hkv, h0, hav', hwf, hi, hb, hb', hg, AV.ofBool, readBack_cons, hbool, h64, hB64]
          · vm_simp [hkey, hkv, h0, hav', hwf, hi, hb, hb', hg, AV.ofBool, readBack_cons, hbool, h64, hB64]
        · by_cases hB64 : B' < 2 ^ 64
          · vm_simp [hkey, hkv, h0, hav', hwf, hi, hb, hb', hg, AV.ofBool, readBack_cons, hbool, h64, hB64]
          · vm_simp [hkey, hkv, h0, hav', hwf, hi, hb, hb', hg, AV.ofBool, readBack_cons, hbool, h64, hB64]

/-! ## Unshielded tokens -/

/-- The field elements of `left c` (an unshielded token type) for a color meaning `cs`. -/
def leftFs (cs : List Fr) : List Fr := Fr.ofInt 1 :: cs ++ [Fr.ofInt 0, Fr.ofInt 0]

theorem left_is {e : Env} {color : Bytes 32} {cs : List Fr} (h : Value.Is p e color cs) :
    Value.Is p e (left color : TokenType) (leftFs cs) :=
  either_mk_is (p := p) rfl h (by
    unfold Value.Is
    show Expr.evalList p e (Value.toExprs (Value.zero (Bytes 32))) = _
    rw [show Value.toExprs (Value.zero (Bytes 32)) = [.const 0, .const 0] from zero_bytes32_limbs]; rfl)

/-- Whether an unshielded recipient meaning `Fr.ofBool u :: rl ++ ru` is this
    contract (address limbs `selfFs`): a contract, and that one. -/
def isSelfFs (u : Bool) (rl selfFs : List Fr) : Bool := u && decide (rl = selfFs)

/-- **`isSelfU recipient`** (whether an unshielded recipient is this contract;
    `kernel.self()` is read only when the recipient is a contract), under a
    guard meaning `gb`: nothing changes, and the result means `u && rl = self`,
    `self` read under the guard `gb && u` (zeros when off). -/
theorem isSelfU_runs (recipient : Either ContractAddress UserAddress) {s : Build} {st : Exec.State ω LedgerState}
    {gb : Bool} (hg : GuardIs p s st.runState gb) (u : Bool) (rl ru : List Fr) (hrl : rl.length = 2)
    (hsh : (Value.toExprs recipient.left).length = 2 ∧ (Value.toExprs recipient.right).length = 2)
    (hr : Stable s.next st.env (fun e => Value.Is p e recipient (Fr.ofBool u :: rl ++ ru)))
    (cfs : List SV) (wa : AV) (selfFs : List Fr) (hctx : st.ledger.context = .array cfs)
    (hc0 : cfs[0]? = some (.cell wa)) (hself : fieldsOf [.bytes 32] wa.atoms = some selfFs) (hwf : st.ledger.WF) :
    XRuns p (oracles H (Damp.Exec.liftWitness w)) (cond recipient.isLeft (do return recipient.left.bytes ==. (← Kernel.self).bytes)
      (pure Boolean.false)) s st True
      (fun b e w' l => w' = st.private_ ∧ l = st.ledger ∧ Boolean.Is p e b (isSelfFs u rl (selfOr (gb && u) selfFs))) := by
  have hparts : ∀ e, Value.Is p e recipient (Fr.ofBool u :: rl ++ ru) →
      recipient.isLeft.expr.eval p e = some (Fr.ofBool u) ∧ Value.Is p e recipient.left rl ∧
        Value.Is p e recipient.right ru := fun e h => either_is (by rw [hsh.1, hrl]) h
  have hsl := fieldsOf_bytes32_length hself
  refine (XRuns.cond (Qt := fun a env w' l => w' = st.private_ ∧ l = st.ledger ∧
      Boolean.Is p env a (decide (rl = selfOr (gb && u) selfFs)))
    (Qe := fun a b env w' l => (w' = st.private_ ∧ l = st.ledger ∧
      Boolean.Is p env a (decide (rl = selfOr (gb && u) selfFs))) ∧ Boolean.Is p env b false)
    (okt := True) (oke := True) hg (hr.imp fun e h => (hparts e h).1)
    (Grows.bind (Grows.ledgerRead _ _) fun _ => Grows.pure' _) (Grows.pure' _) ?_ ?_).conseq (by simp) ?_
  · intro s' st' ctx
    refine (XRuns.seq (ok₂ := True) (self_runs H p w ctx.2.2.2.2 cfs wa selfFs (by rw [ctx.2.2.2.1]; exact hctx) hc0
      hself (by rw [ctx.2.2.2.1]; exact hwf)) (fun _ => Grows.pure' _)
      fun a s₁ st₁ hn₁ hgd₁ ha₁ hQ₁ => XRuns.pure fun e he => ?_).conseq (by simp) fun _ _ _ _ h => h
    obtain ⟨hw₁, hl₁, ha, hsha⟩ := hQ₁ e he
    refine ⟨hw₁.trans ctx.2.2.1, hl₁.trans ctx.2.2.2.1, ?_⟩
    have hle := (hparts e (((hr.transfer ctx.2.1).mono ctx.1).later ha₁ hn₁ e he)).2.1
    exact valueEq_is (p := p) hle ha (by rw [hrl, selfOr_length hsl])
  · intro a s' st' hn hA hgd hQ
    exact XRuns.pure (hQ.imp fun e h => ⟨h, rfl⟩)
  · intro r env w' l ⟨a, b, hrab, ⟨⟨hw, hl, ha⟩, hb⟩, hc⟩
    refine ⟨hw, hl, ?_⟩
    rw [hrab]
    have := select_is (p := p) roundTrip_boolean hc rfl rfl (show Value.Is p env a
        [Fr.ofBool (decide (rl = selfOr (gb && u) selfFs))] by
      simp [Value.Is, Value.toExprs, Expr.evalList, show a.expr.eval p env = _ from ha]) (show Value.Is p env b
        [Fr.ofBool false] by simp [Value.Is, Value.toExprs, Expr.evalList, show b.expr.eval p env = _ from hb])
    simp only [Value.Is, Value.toExprs, Expr.evalList] at this
    show (select recipient.isLeft a b).expr.eval p env = _
    cases h : (select recipient.isLeft a b).expr.eval p env with
    | none => simp [h] at this
    | some y =>
      rw [h] at this
      cases u <;> (simp at this; simp [isSelfFs, this])

theorem isSelfFs_selfOr (u : Bool) (rl selfFs : List Fr) : isSelfFs u rl (selfOr u selfFs) = isSelfFs u rl selfFs := by
  cases u <;> rfl

/-- The effects after `sendUnshielded` with the guard on: the outputs (slot 7)
    and the spends (slot 8) count `a` more, and the inputs (slot 6) too when the
    recipient is this contract. -/
def sendUEffects (es : List SV) (m6 m7 m8 : List (AV × SV)) (k kv8 : AV) (a : Nat) (self : Bool) : List SV :=
  if self then ((es.set 7 (addMap 7 m7 k a)).set 8 (addMap 8 m8 kv8 a)).set 6 (addMap 6 m6 k a)
  else (es.set 7 (addMap 7 m7 k a)).set 8 (addMap 8 m8 kv8 a)

/-- When `sendUnshielded` with the guard on completes: each addition fits. -/
def sendUOk (m6 m7 m8 : List (AV × SV)) (k kv8 : AV) (a : Nat) (self : Bool) : Prop :=
  addOk m7 k a ∧ addOk m8 kv8 a ∧ (self = true → addOk m6 k a)

theorem setEff_wf {σ σ' : LedgerState} {req : List (Op Fr)} {xs : List Fr} (h : ledgerOracle H req σ = some (xs, σ')) :
    σ'.WF := ledgerOracle_wf h

/-- **`sendUnshielded color amount recipient`**, under a guard meaning `gb`:
    `color` meaning the limbs `cs` of the 32-byte atom `c`, `amount` meaning
    `a < 2^128`, `recipient` meaning `Fr.ofBool u :: rl ++ ru` (a contract with
    address `rl` when `u`, a user `ru` otherwise), stored with the token type
    as the spend key `kv8`, a well-formed `(TokenType, PublicAddress)`. With the
    guard on it completes exactly when each addition fits (`sendUOk`: an entry
    is new or its sum fits 64 bits) and then changes only the effects, as
    `sendUEffects` says (slot 6 too exactly when `recipient` is this contract,
    `isSelfFs`); with the guard off nothing changes. The private state is
    unchanged. -/
theorem sendUnshielded_runs (color : Bytes 32) (amount : Uint128) (recipient : Either ContractAddress UserAddress)
    {s : Build} {st : Exec.State ω LedgerState} {gb : Bool} (hg : GuardIs p s st.runState gb)
    (cs : List Fr) (hcl : cs.length = 2) (hcs : Stable s.next st.env (fun e => Value.Is p e color cs))
    (c : Nat) (hc : AV.ofFields [.bytes 32] cs = some ⟨[.bytes 32], [c]⟩)
    (a : Fr) (ha : Stable s.next st.env (fun e => amount.expr.eval p e = some a)) (ha128 : a.val < 2 ^ 128)
    (u : Bool) (rl ru : List Fr) (hrl : rl.length = 2)
    (hsh : (Value.toExprs recipient.left).length = 2 ∧ (Value.toExprs recipient.right).length = 2)
    (hr : Stable s.next st.env (fun e => Value.Is p e recipient (Fr.ofBool u :: rl ++ ru)))
    (kv8 : AV) (hkv8 : AV.ofFields (alignTokenType ++ alignPublicAddress) (leftFs cs ++ (Fr.ofBool u :: rl ++ ru)) =
      some kv8) (hok8 : spendKeyOk kv8.atoms = true)
    (cfs : List SV) (wa : AV) (selfFs : List Fr) (hctx : st.ledger.context = .array cfs)
    (hc0 : cfs[0]? = some (.cell wa)) (hself : fieldsOf [.bytes 32] wa.atoms = some selfFs) (hwf : st.ledger.WF)
    (es : List SV) (m6 m7 m8 : List (AV × SV)) (heff : st.ledger.effects = .array es)
    (hm6 : es[6]? = some (.map m6)) (hm7 : es[7]? = some (.map m7)) (hm8 : es[8]? = some (.map m8)) :
    XRuns p (oracles H (Damp.Exec.liftWitness w)) (sendUnshielded color amount recipient) s st
      (gb = true → sendUOk m6 m7 m8 (leftKey c) kv8 a.val (isSelfFs u rl selfFs))
      (fun _ _ w' l => w' = st.private_ ∧ l = if gb then
        { st.ledger with effects := .array (sendUEffects es m6 m7 m8 (leftKey c) kv8 a.val (isSelfFs u rl selfFs)) }
        else st.ledger) := by
  let σ := st.ledger
  let k := leftKey c
  let es₁ := es.set 7 (addMap 7 m7 k a.val)
  let σ₁ : LedgerState := { σ with effects := .array es₁ }
  -- 1. `Kernel.incUnshieldedOutputs (left color) amount`
  have hreq₁ : ∀ e, Agree s.next st.env e → ∃ req,
      (emitted (Kernel.incUnshieldedOutputs (left color) amount)).bind (Exec.request p e) = some req ∧
      (oracles H (Damp.Exec.liftWitness w)).ledger req st.ledger = if addOk m7 k a.val then some ([], σ₁) else none := by
    intro e he
    obtain ⟨ks, hks, hkv, hok⟩ := tokenKey_left p e color cs c (hcs e he) hcl hc
    exact Kernel.incUnshieldedOutputs_spec H p e st.ledger es m7 (left color) amount ks (leftKey c) a hwf heff hm7
      hks hkv hok (ha e he) ha128
  let cb' := isSelfFs u rl (selfOr (gb && u) selfFs)
  have hsl := fieldsOf_bytes32_length hself
  unfold sendUnshielded
  refine (XRuns.seq (ok₂ := (gb = true → addOk m8 kv8 a.val) ∧ (True ∧ ((gb && cb') = true → addOk m6 k a.val)))
    (XRuns.condOp rfl (by simp) hg hreq₁)
    (fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.cond _ (Grows.bind (Grows.ledgerRead _ _)
      fun _ => Grows.pure' _) (Grows.pure' _)) fun _ => Grows.when_ _ (Grows.ledgerOp _ _))
    fun _ s₁ st₁ hn₁ hgd₁ ha₁ hQ₁ => ?_).conseq
    (ok' := gb = true → sendUOk m6 m7 m8 (leftKey c) kv8 a.val (isSelfFs u rl selfFs)) ?_ (fun _ _ _ _ h => h)
  rotate_left
  · cases gb with
    | false => simp
    | true =>
      simp only [forall_const, true_and, sendUOk, cb', Bool.true_and, isSelfFs_selfOr]
      exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩⟩
  obtain ⟨hw₁, hP₁, hl₁⟩ := hQ₁.holds
  have hg₁ := GuardIs.later hg ha₁ hn₁ hgd₁
  let es₁' := if gb then es₁ else es
  let l₁ : LedgerState := if gb then σ₁ else σ
  have heff₁ : l₁.effects = .array es₁' := by cases gb <;> simp [l₁, es₁', σ₁, σ, heff]
  have hctx₁ : l₁.context = .array cfs := by cases gb <;> simp [l₁, σ₁, σ, hctx]
  have hwf₁ : l₁.WF := by
    cases gb with
    | false => exact hwf
    | true =>
      obtain ⟨req, -, hq⟩ := hreq₁ st.env (Agree.refl _ _)
      simp only [hP₁ rfl, ite_true] at hq
      exact ledgerOracle_wf hq
  have hm8₁ : es₁'[8]? = some (.map m8) := by cases gb <;> simp [es₁', es₁, List.getElem?_set_ne, hm8]
  have hm6₁ : es₁'[6]? = some (.map m6) := by cases gb <;> simp [es₁', es₁, List.getElem?_set_ne, hm6]
  have hA₁ : Agree s.next st.env st₁.env := ha₁
  -- 2. `Kernel.claimUnshieldedCoinSpend (left color) recipient amount`
  let es₂ := es₁'.set 8 (addMap 8 m8 kv8 a.val)
  let σ₂ : LedgerState := { l₁ with effects := .array es₂ }
  have hreq₂ : ∀ e, Agree s₁.next st₁.env e → ∃ req,
      (emitted (Kernel.claimUnshieldedCoinSpend (left color) recipient amount)).bind (Exec.request p e) = some req ∧
      (oracles H (Damp.Exec.liftWitness w)).ledger req st₁.ledger = if addOk m8 kv8 a.val then some ([], σ₂) else none := by
    intro e he
    have hA : Agree s.next st.env e := hA₁.trans (he.mono hn₁)
    have hk : Expr.evalList p e (Value.toExprs (left color, recipient)) = some (leftFs cs ++ (Fr.ofBool u :: rl ++ ru)) :=
      prod_is (left_is p (hcs e hA)) (hr e hA)
    rw [hl₁]
    exact Kernel.claimUnshieldedCoinSpend_spec H p e l₁ es₁' m8 (left color) recipient amount _ kv8 a hwf₁ heff₁ hm8₁
      hk hkv8 hok8 (ha e hA) ha128
  refine (XRuns.seq (ok₂ := True ∧ ((gb && cb') = true → addOk m6 k a.val)) (XRuns.condOp rfl (by simp) hg₁ hreq₂)
    (fun _ => Grows.bind (Grows.cond _ (Grows.bind (Grows.ledgerRead _ _)
      fun _ => Grows.pure' _) (Grows.pure' _)) fun _ => Grows.when_ _ (Grows.ledgerOp _ _))
    fun _ s₂ st₂ hn₂ hgd₂ ha₂ hQ₂ => ?_).conseq Iff.rfl (fun _ _ _ _ h => h)
  obtain ⟨hw₂, hP₂, hl₂⟩ := hQ₂.holds
  have hg₂ := GuardIs.later hg₁ ha₂ hn₂ hgd₂
  let es₂' := if gb then es₂ else es₁'
  let l₂ : LedgerState := if gb then σ₂ else l₁
  have hl₂' : st₂.ledger = l₂ := by rw [hl₂, hl₁]
  have heff₂ : l₂.effects = .array es₂' := by cases gb <;> simp [l₂, es₂', σ₂, heff₁]
  have hctx₂ : l₂.context = .array cfs := by cases gb <;> simp [l₂, σ₂, hctx₁]
  have hwf₂ : l₂.WF := by
    cases gb with
    | false => exact hwf₁
    | true =>
      obtain ⟨req, -, hq⟩ := hreq₂ st₁.env (Agree.refl _ _)
      simp only [hP₂ rfl, ite_true] at hq
      exact ledgerOracle_wf hq
  have hm6₂ : es₂'[6]? = some (.map m6) := by cases gb <;> simp [es₂', es₂, List.getElem?_set_ne, hm6₁]
  have hA₂ : Agree s.next st.env st₂.env := hA₁.trans (ha₂.mono hn₁)
  -- 3. `isSelfU recipient`
  refine (XRuns.seq (ok₂ := (gb && cb') = true → addOk m6 k a.val)
    (isSelfU_runs H p w recipient hg₂ u rl ru hrl hsh ((hr.later hA₂ (Nat.le_trans hn₁ hn₂))) cfs wa selfFs
      (by rw [hl₂']; exact hctx₂) hc0 hself (by rw [hl₂']; exact hwf₂))
    (fun _ => Grows.when_ _ (Grows.ledgerOp _ _))
    fun b s₃ st₃ hn₃ hgd₃ ha₃ hQ₃ => ?_).conseq Iff.rfl (fun _ _ _ _ h => h)
  obtain ⟨hw₃, hl₃, -⟩ := hQ₃.holds
  have hg₃ := GuardIs.later hg₂ ha₃ hn₃ hgd₃
  have hA₃ : Agree s.next st.env st₃.env := hA₂.trans (ha₃.mono (Nat.le_trans hn₁ hn₂))
  -- 4. `if% self then Kernel.incUnshieldedInputs (left color) amount`
  let σ₃ : LedgerState := { l₂ with effects := .array (es₂'.set 6 (addMap 6 m6 k a.val)) }
  have hreq₃ : ∀ e, Agree s₃.next st₃.env e → ∃ req,
      (emitted (Kernel.incUnshieldedInputs (left color) amount)).bind (Exec.request p e) = some req ∧
      (oracles H (Damp.Exec.liftWitness w)).ledger req st₃.ledger = if addOk m6 k a.val then some ([], σ₃) else none := by
    intro e he
    have hA : Agree s.next st.env e := hA₃.trans (he.mono (Nat.le_trans hn₁ (Nat.le_trans hn₂ hn₃)))
    obtain ⟨ks, hks, hkv, hok⟩ := tokenKey_left p e color cs c (hcs e hA) hcl hc
    rw [hl₃, hl₂']
    exact Kernel.incUnshieldedInputs_spec H p e l₂ es₂' m6 (left color) amount ks (leftKey c) a hwf₂ heff₂ hm6₂
      hks hkv hok (ha e hA) ha128
  refine (XRuns.when_condOp (cb := cb') rfl (by simp) hg₃ (hQ₃.imp fun e h => h.2.2) hreq₃).conseq Iff.rfl
    fun _ _ w' l h => ⟨?_, ?_⟩
  · rw [h.1, hw₃, hw₂, hw₁]
  · rw [h.2.2, hl₃, hl₂']
    cases gb with
    | false => simp [cb', l₂, l₁, σ]
    | true =>
      cases hs : isSelfFs u rl selfFs with
      | true =>
        have : cb' = true := by simp only [cb', Bool.true_and, isSelfFs_selfOr, hs]
        simp only [this, Bool.and_self, ite_true, σ₃, l₂, σ₂, l₁, σ₁, es₂', es₂, es₁', es₁, sendUEffects, hs, σ, k]
      | false =>
        have : cb' = false := by simp only [cb', Bool.true_and, isSelfFs_selfOr, hs]
        simp only [this, Bool.and_false, ite_true, ite_false, Bool.false_eq_true, l₂, σ₂, l₁, σ₁, es₂', es₂, es₁',
          es₁, sendUEffects, hs, σ, k]
/-- The effects after `mintUnshieldedToken` with the guard on: the mints
    (slot 5) under the domain separator `dk`, the spends (slot 8), and the
    inputs (slot 6) under the token type `tk` when the recipient is this
    contract. -/
def mintUEffects (es : List SV) (m5 m6 m8 : List (AV × SV)) (dk tk kv8 : AV) (a : Nat) (self : Bool) : List SV :=
  if self then ((es.set 5 (addMap 5 m5 dk a)).set 8 (addMap 8 m8 kv8 a)).set 6 (addMap 6 m6 tk a)
  else (es.set 5 (addMap 5 m5 dk a)).set 8 (addMap 8 m8 kv8 a)

/-- When `mintUnshieldedToken` with the guard on completes. -/
def mintUOk (m5 m6 m8 : List (AV × SV)) (dk tk kv8 : AV) (a : Nat) (self : Bool) : Prop :=
  addOk m5 dk a ∧ addOk m8 kv8 a ∧ (self = true → addOk m6 tk a)

theorem widen_eval {m k : Nat} (a : Uint m) (hk : k ≤ Uint.maxBound) (h : m ≤ k) (e : Env) :
    (a.widen h).expr.eval p e = a.expr.eval p e := Uint.capped_eval hk _

/-- **`mintUnshieldedToken domainSep amount recipient`**, under a guard meaning
    `gb`: `domainSep` meaning `dsFs` (the 32-byte atom `d`), `amount` meaning
    `a < 2^64`, the recipient as in `sendUnshielded_runs`; the token type the
    circuit derives (`tokenType domainSep self`, whatever the hash gives on
    `tokenTypePre`, with `self` read under the guard) is `ts`, the atom `t`,
    stored with the recipient as the spend key `kv8`. With the guard on it
    completes exactly when each addition fits (`mintUOk`) and then changes only
    the effects (`mintUEffects`); with the guard off nothing changes. The
    result means `ts`; the private state is unchanged. -/
theorem mintUnshieldedToken_runs (domainSep : Bytes 32) (amount : Uint64) (recipient : Either ContractAddress UserAddress)
    {s : Build} {st : Exec.State ω LedgerState} {gb : Bool} (hg : GuardIs p s st.runState gb)
    (dsFs : List Fr) (hds : Stable s.next st.env (fun e => Value.Is p e domainSep dsFs))
    (d : Nat) (hd : AV.ofFields [.bytes 32] dsFs = some ⟨[.bytes 32], [d]⟩)
    (a : Fr) (ha : Stable s.next st.env (fun e => amount.expr.eval p e = some a)) (ha64 : a.val < 2 ^ 64)
    (u : Bool) (rl ru : List Fr) (hrl : rl.length = 2)
    (hsh : (Value.toExprs recipient.left).length = 2 ∧ (Value.toExprs recipient.right).length = 2)
    (hr : Stable s.next st.env (fun e => Value.Is p e recipient (Fr.ofBool u :: rl ++ ru)))
    (cfs : List SV) (wa : AV) (selfFs : List Fr) (hctx : st.ledger.context = .array cfs)
    (hc0 : cfs[0]? = some (.cell wa)) (hself : fieldsOf [.bytes 32] wa.atoms = some selfFs) (hwf : st.ledger.WF)
    (ts : List Fr) (htt : phashFs p tokenTypeAlign (tokenTypePre dsFs (selfOr gb selfFs)) = some ts)
    (t : Nat) (ht : AV.ofFields [.bytes 32] ts = some ⟨[.bytes 32], [t]⟩)
    (kv8 : AV) (hkv8 : AV.ofFields (alignTokenType ++ alignPublicAddress) (leftFs ts ++ (Fr.ofBool u :: rl ++ ru)) =
      some kv8) (hok8 : spendKeyOk kv8.atoms = true)
    (es : List SV) (m5 m6 m8 : List (AV × SV)) (heff : st.ledger.effects = .array es)
    (hm5 : es[5]? = some (.map m5)) (hm6 : es[6]? = some (.map m6)) (hm8 : es[8]? = some (.map m8)) :
    XRuns p (oracles H (Damp.Exec.liftWitness w)) (mintUnshieldedToken domainSep amount recipient) s st
      (gb = true → mintUOk m5 m6 m8 ⟨[.bytes 32], [d]⟩ (leftKey t) kv8 a.val (isSelfFs u rl selfFs))
      (fun r e w' l => Value.Is p e r ts ∧ w' = st.private_ ∧ l = if gb then
        { st.ledger with effects := .array (mintUEffects es m5 m6 m8 ⟨[.bytes 32], [d]⟩ (leftKey t) kv8 a.val
          (isSelfFs u rl selfFs)) }
        else st.ledger) := by
  let σ := st.ledger
  let dk : AV := ⟨[.bytes 32], [d]⟩
  let k := leftKey t
  let es₁ := es.set 5 (addMap 5 m5 dk a.val)
  let σ₁ : LedgerState := { σ with effects := .array es₁ }
  let cb' := isSelfFs u rl (selfOr (gb && u) selfFs)
  have hsl := fieldsOf_bytes32_length hself
  have htl : ts.length = 2 := phashFs_length htt
  have ha' : Stable s.next st.env (fun e => (amount.widen : Uint128).expr.eval p e = some a) :=
    ha.imp fun e h => by rw [widen_eval p amount uint128_bound (by decide) e]; exact h
  have ha128 : a.val < 2 ^ 128 := Nat.lt_trans ha64 (by decide)
  -- 1. `Kernel.mintUnshielded domainSep amount`
  have hreq₁ : ∀ e, Agree s.next st.env e → ∃ req,
      (emitted (Kernel.mintUnshielded domainSep amount)).bind (Exec.request p e) = some req ∧
      (oracles H (Damp.Exec.liftWitness w)).ledger req st.ledger = if addOk m5 dk a.val then some ([], σ₁) else none := fun e he =>
    Kernel.mintUnshielded_spec H p e st.ledger es m5 domainSep amount dsFs dk a hwf heff hm5 (hds e he) hd (ha e he) ha64
  unfold mintUnshieldedToken
  refine (XRuns.seq (ok₂ := True ∧ (True ∧ ((gb = true → addOk m8 kv8 a.val) ∧ (True ∧
      (((gb && cb') = true → addOk m6 k a.val) ∧ True))))) (XRuns.condOp rfl (by simp) hg hreq₁)
    (fun _ => Grows.bind (Grows.ledgerRead _ _) fun _ => Grows.bind (Grows.val _ _) fun _ =>
      Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.cond _ (Grows.bind (Grows.ledgerRead _ _)
      fun _ => Grows.pure' _) (Grows.pure' _)) fun _ => Grows.bind (Grows.when_ _ (Grows.ledgerOp _ _)) fun _ =>
      Grows.pure' _)
    fun _ s₁ st₁ hn₁ hgd₁ ha₁ hQ₁ => ?_).conseq
    (ok' := gb = true → mintUOk m5 m6 m8 dk k kv8 a.val (isSelfFs u rl selfFs)) ?_ (fun _ _ _ _ h => h)
  rotate_left
  · cases gb with
    | false => simp
    | true =>
      simp only [forall_const, true_and, and_true, mintUOk, cb', Bool.true_and, isSelfFs_selfOr]
  obtain ⟨hw₁, hP₁, hl₁⟩ := hQ₁.holds
  have hg₁ := GuardIs.later hg ha₁ hn₁ hgd₁
  let es₁' := if gb then es₁ else es
  let l₁ : LedgerState := if gb then σ₁ else σ
  have heff₁ : l₁.effects = .array es₁' := by cases gb <;> simp [l₁, es₁', σ₁, σ, heff]
  have hctx₁ : l₁.context = .array cfs := by cases gb <;> simp [l₁, σ₁, σ, hctx]
  have hwf₁ : l₁.WF := by
    cases gb with
    | false => exact hwf
    | true =>
      obtain ⟨req, -, hq⟩ := hreq₁ st.env (Agree.refl _ _)
      simp only [hP₁ rfl, ite_true] at hq
      exact ledgerOracle_wf hq
  have hm8₁ : es₁'[8]? = some (.map m8) := by cases gb <;> simp [es₁', es₁, List.getElem?_set_ne, hm8]
  have hm6₁ : es₁'[6]? = some (.map m6) := by cases gb <;> simp [es₁', es₁, List.getElem?_set_ne, hm6]
  have hA₁ : Agree s.next st.env st₁.env := ha₁
  -- 2. `kernel.self()`
  refine (XRuns.seq (ok₂ := True ∧ ((gb = true → addOk m8 kv8 a.val) ∧ (True ∧
      (((gb && cb') = true → addOk m6 k a.val) ∧ True))))
    (self_runs H p w hg₁ cfs wa selfFs (by rw [hl₁]; exact hctx₁) hc0 hself (by rw [hl₁]; exact hwf₁))
    (fun _ => Grows.bind (Grows.val _ _) fun _ =>
      Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.cond _ (Grows.bind (Grows.ledgerRead _ _)
      fun _ => Grows.pure' _) (Grows.pure' _)) fun _ => Grows.bind (Grows.when_ _ (Grows.ledgerOp _ _)) fun _ =>
      Grows.pure' _)
    fun x s₂ st₂ hn₂ hgd₂ ha₂ hQ₂ => ?_).conseq (by simp) (fun _ _ _ _ h => h)
  obtain ⟨hw₂, hl₂, -, hshx⟩ := hQ₂.holds
  have hg₂ := GuardIs.later hg₁ ha₂ hn₂ hgd₂
  have hA₂ : Agree s.next st.env st₂.env := hA₁.trans (ha₂.mono hn₁)
  -- 3. `const color := tokenType domainSep self`
  have hcol : Stable s₂.next st₂.env (fun e => Value.Is p e (tokenType domainSep x) ts) := fun e he =>
    tokenType_is ((hds.later hA₂ (Nat.le_trans hn₁ hn₂)) e he) (hQ₂ e he).2.2.1 htt
  refine (XRuns.seq (ok₂ := (gb = true → addOk m8 kv8 a.val) ∧ (True ∧
      (((gb && cb') = true → addOk m6 k a.val) ∧ True)))
    ((XRuns.val (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (s := s₂) (st := st₂) roundTrip_bytes "color"
      (by rw [← Damp.evalList_length hcol.holds, htl]; rfl) hcol).addResult
      (val_shaped _ "color" s₂ (by rw [← Damp.evalList_length hcol.holds, htl]; rfl)))
    (fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.cond _ (Grows.bind (Grows.ledgerRead _ _)
      fun _ => Grows.pure' _) (Grows.pure' _)) fun _ => Grows.bind (Grows.when_ _ (Grows.ledgerOp _ _)) fun _ =>
      Grows.pure' _)
    fun color s₃ st₃ hn₃ hgd₃ ha₃ hQ₃ => ?_).conseq (by simp) (fun _ _ _ _ h => h)
  obtain ⟨⟨-, hw₃, hl₃⟩, -⟩ := hQ₃.holds
  have hg₃ := GuardIs.later hg₂ ha₃ hn₃ hgd₃
  have hA₃ : Agree s.next st.env st₃.env := hA₂.trans (ha₃.mono (Nat.le_trans hn₁ hn₂))
  have hn₀₃ : s.next ≤ s₃.next := Nat.le_trans hn₁ (Nat.le_trans hn₂ hn₃)
  have hcolor : Stable s₃.next st₃.env (fun e => Value.Is p e color ts) := hQ₃.imp fun e h => h.1.1
  have hl₃' : st₃.ledger = l₁ := by rw [hl₃, hl₂, hl₁]
  -- 4. `Kernel.claimUnshieldedCoinSpend (left color) recipient amount.widen`
  let es₂ := es₁'.set 8 (addMap 8 m8 kv8 a.val)
  let σ₂ : LedgerState := { l₁ with effects := .array es₂ }
  have hreq₂ : ∀ e, Agree s₃.next st₃.env e → ∃ req,
      (emitted (Kernel.claimUnshieldedCoinSpend (left color) recipient amount.widen)).bind (Exec.request p e) =
        some req ∧
      (oracles H (Damp.Exec.liftWitness w)).ledger req st₃.ledger = if addOk m8 kv8 a.val then some ([], σ₂) else none := by
    intro e he
    have hA : Agree s.next st.env e := hA₃.trans (he.mono hn₀₃)
    have hk : Expr.evalList p e (Value.toExprs (left color, recipient)) = some (leftFs ts ++ (Fr.ofBool u :: rl ++ ru)) :=
      prod_is (left_is p (hcolor e he)) (hr e hA)
    rw [hl₃']
    exact Kernel.claimUnshieldedCoinSpend_spec H p e l₁ es₁' m8 (left color) recipient amount.widen _ kv8 a hwf₁ heff₁
      hm8₁ hk hkv8 hok8 (ha' e hA) ha128
  refine (XRuns.seq (ok₂ := True ∧ (((gb && cb') = true → addOk m6 k a.val) ∧ True))
    (XRuns.condOp rfl (by simp) hg₃ hreq₂)
    (fun _ => Grows.bind (Grows.cond _ (Grows.bind (Grows.ledgerRead _ _)
      fun _ => Grows.pure' _) (Grows.pure' _)) fun _ => Grows.bind (Grows.when_ _ (Grows.ledgerOp _ _)) fun _ =>
      Grows.pure' _)
    fun _ s₄ st₄ hn₄ hgd₄ ha₄ hQ₄ => ?_).conseq Iff.rfl (fun _ _ _ _ h => h)
  obtain ⟨hw₄, hP₄, hl₄⟩ := hQ₄.holds
  have hg₄ := GuardIs.later hg₃ ha₄ hn₄ hgd₄
  let es₂' := if gb then es₂ else es₁'
  let l₂ : LedgerState := if gb then σ₂ else l₁
  have hl₄' : st₄.ledger = l₂ := by rw [hl₄, hl₃']
  have heff₂ : l₂.effects = .array es₂' := by cases gb <;> simp [l₂, es₂', σ₂, heff₁]
  have hctx₂ : l₂.context = .array cfs := by cases gb <;> simp [l₂, σ₂, hctx₁]
  have hwf₂ : l₂.WF := by
    cases gb with
    | false => exact hwf₁
    | true =>
      obtain ⟨req, -, hq⟩ := hreq₂ st₃.env (Agree.refl _ _)
      simp only [hP₄ rfl, ite_true] at hq
      exact ledgerOracle_wf hq
  have hm6₂ : es₂'[6]? = some (.map m6) := by cases gb <;> simp [es₂', es₂, List.getElem?_set_ne, hm6₁]
  have hA₄ : Agree s.next st.env st₄.env := hA₃.trans (ha₄.mono hn₀₃)
  have hn₀₄ : s.next ≤ s₄.next := Nat.le_trans hn₀₃ hn₄
  -- 5. `isSelfU recipient`
  refine (XRuns.seq (ok₂ := ((gb && cb') = true → addOk m6 k a.val) ∧ True)
    (isSelfU_runs H p w recipient hg₄ u rl ru hrl hsh (hr.later hA₄ hn₀₄) cfs wa selfFs
      (by rw [hl₄']; exact hctx₂) hc0 hself (by rw [hl₄']; exact hwf₂))
    (fun _ => Grows.bind (Grows.when_ _ (Grows.ledgerOp _ _)) fun _ => Grows.pure' _)
    fun b s₅ st₅ hn₅ hgd₅ ha₅ hQ₅ => ?_).conseq Iff.rfl (fun _ _ _ _ h => h)
  obtain ⟨hw₅, hl₅, -⟩ := hQ₅.holds
  have hg₅ := GuardIs.later hg₄ ha₅ hn₅ hgd₅
  have hA₅ : Agree s.next st.env st₅.env := hA₄.trans (ha₅.mono hn₀₄)
  have hn₀₅ : s.next ≤ s₅.next := Nat.le_trans hn₀₄ hn₅
  -- 6. `if% self then Kernel.incUnshieldedInputs (left color) amount.widen`
  let σ₃ : LedgerState := { l₂ with effects := .array (es₂'.set 6 (addMap 6 m6 k a.val)) }
  have hreq₃ : ∀ e, Agree s₅.next st₅.env e → ∃ req,
      (emitted (Kernel.incUnshieldedInputs (left color) amount.widen)).bind (Exec.request p e) = some req ∧
      (oracles H (Damp.Exec.liftWitness w)).ledger req st₅.ledger = if addOk m6 k a.val then some ([], σ₃) else none := by
    intro e he
    have hA : Agree s.next st.env e := hA₅.trans (he.mono hn₀₅)
    obtain ⟨ks, hks, hkv, hok⟩ := tokenKey_left p e color ts t (((hcolor.later ha₄ hn₄).later ha₅ hn₅) e he) htl ht
    rw [hl₅, hl₄']
    exact Kernel.incUnshieldedInputs_spec H p e l₂ es₂' m6 (left color) amount.widen ks (leftKey t) a hwf₂ heff₂ hm6₂
      hks hkv hok (ha' e hA) ha128
  refine (XRuns.seq (ok₂ := True) (XRuns.when_condOp (cb := cb') rfl (by simp) hg₅ (hQ₅.imp fun e h => h.2.2) hreq₃)
    (fun _ => Grows.pure' _) fun _ s₆ st₆ hn₆ hgd₆ ha₆ hQ₆ => ?_).conseq Iff.rfl (fun _ _ _ _ h => h)
  obtain ⟨hw₆, -, hl₆⟩ := hQ₆.holds
  refine XRuns.pure fun e he => ⟨(((hcolor.later ha₄ hn₄).later ha₅ hn₅).later ha₆ hn₆) e he, ?_, ?_⟩
  · rw [hw₆, hw₅, hw₄, hw₃, hw₂, hw₁]
  · rw [hl₆, hl₅, hl₄']
    cases gb with
    | false => simp [cb', l₂, l₁, σ]
    | true =>
      cases hs : isSelfFs u rl selfFs with
      | true =>
        have : cb' = true := by simp only [cb', Bool.true_and, isSelfFs_selfOr, hs]
        simp only [this, Bool.and_self, ite_true, σ₃, l₂, σ₂, l₁, σ₁, es₂', es₂, es₁', es₁, mintUEffects, hs, σ, k, dk]
      | false =>
        have : cb' = false := by simp only [cb', Bool.true_and, isSelfFs_selfOr, hs]
        simp only [this, Bool.and_false, ite_true, ite_false, Bool.false_eq_true, l₂, σ₂, l₁, σ₁, es₂', es₂, es₁',
          es₁, mintUEffects, hs, σ, k, dk]

/-! ## Balance reads, end to end -/

theorem fieldsOf_small' {k X : Nat} (hk : k ≤ 31) (hX : X < 2 ^ (8 * k)) :
    fieldsOf [.bytes k] [X] = some [Fr.ofNat X] := by
  have hm : X < Fr.modulus := Nat.lt_of_lt_of_le hX (Nat.le_of_lt (Nat.lt_of_le_of_lt
    (Nat.pow_le_pow_right (by decide) (by omega : 8 * k ≤ 248)) (by decide)))
  have hn : ¬ k > 31 := by omega
  simp [fieldsOf, fieldsOfAtom, hn, hm]
  exact Fr.ext (Nat.mod_eq_of_lt hm).symm

/-- A reading operation answering one truth value `b` when `P` (and failing
    otherwise), under a guard meaning `gb`: it completes exactly when
    `gb → P`, and the result means `gb && b`; nothing changes. -/
theorem boolRead_runs {mk : List Expr → List (Op Expr)} (hmk : ReadOps mk) {s : Build}
    {st : Exec.State ω LedgerState} {gb : Bool} (hg : GuardIs p s st.runState gb) {P : Prop} [Decidable P] {b : Bool}
    (hreq : ∀ e, Agree s.next st.env e → ∃ req, Exec.request p e (mk (readVars Boolean)) = some req ∧
      (oracles H (Damp.Exec.liftWitness w)).ledger req st.ledger = if P then some ([Fr.ofBool b], st.ledger) else none) :
    XRuns p (oracles H (Damp.Exec.liftWitness w)) (ledgerRead Boolean mk) s st (gb = true → P)
      (fun r e w' l => w' = st.private_ ∧ l = st.ledger ∧ Boolean.Is p e r (gb && b)) := by
  refine (XRuns.ledgerReadG (p := p) (O := oracles H (Damp.Exec.liftWitness w)) roundTrip_boolean hmk (by decide) hg hreq).conseq ?_ ?_
  · cases gb with
    | false => simp
    | true => by_cases hP : P <;> simp [hP]; rfl
  · intro r e w' l ⟨hw, hq⟩
    refine ⟨hw, ?_⟩
    cases gb with
    | false =>
      simp only [Bool.false_eq_true, ite_false] at hq
      refine ⟨hq.1, ?_⟩
      have h2 : Expr.evalList p e [r.expr] = some [0] := hq.2
      obtain ⟨x, xs, hx, -, hxe⟩ := evalList_cons.1 h2
      simp only [List.cons.injEq] at hxe
      show r.expr.eval p e = _
      rw [hx, ← hxe.1]; rfl
    | true =>
      simp only [ite_true] at hq
      obtain ⟨ys, hy, hi⟩ := hq
      by_cases hP : P
      · simp only [hP, ite_true, Option.some.injEq, Prod.mk.injEq] at hy
        obtain ⟨rfl, rfl⟩ := hy
        refine ⟨rfl, ?_⟩
        simp [Value.Is, Value.toExprs, Expr.evalList] at hi
        show r.expr.eval p e = _
        cases h : r.expr.eval p e <;> simp_all
      · simp [hP] at hy

/-- **`unshieldedBalance color`** (`Kernel.balance (left color)`), under a guard
    meaning `gb`, with the context's balance of `(1, c, 0)` the atom
    `B < 2^128` (0 when absent): the result means `B` (0 with the guard off);
    nothing changes. -/
theorem unshieldedBalance_runs (color : Bytes 32) {s : Build} {st : Exec.State ω LedgerState} {gb : Bool}
    (hg : GuardIs p s st.runState gb) (cs : List Fr) (hcl : cs.length = 2)
    (hcs : Stable s.next st.env (fun e => Value.Is p e color cs))
    (c : Nat) (hc : AV.ofFields [.bytes 32] cs = some ⟨[.bytes 32], [c]⟩)
    (cfs : List SV) (bal : List (AV × SV)) (hctx : st.ledger.context = .array cfs) (hb : cfs[5]? = some (.map bal))
    (hwf : st.ledger.WF) (B : Nat) (hB : balAtom bal (leftKey c) = some B) (hB128 : B < 2 ^ 128) :
    XRuns p (oracles H (Damp.Exec.liftWitness w)) (unshieldedBalance color) s st True
      (fun r e w' l => w' = st.private_ ∧ l = st.ledger ∧ Value.Is p e r [Fr.ofNat (if gb then B else 0)]) := by
  have hres : ∀ e, Agree s.next st.env e → ∃ req, Exec.request p e
      ((fun es => [.dup 2, .idx true false [fieldKey 5], .dup 0, .push false (alignedOf (left color : TokenType)),
        .member, .branch 3, .pop, .push false ⟨[.bytes 16], [.const 0]⟩, .jmp 1,
        .idx true false [alignedOf (left color : TokenType)], .popeq true [.bytes 16] es]) (readVars Uint128)) =
          some req ∧ (oracles H (Damp.Exec.liftWitness w)).ledger req st.ledger = some ([Fr.ofNat B], st.ledger) := by
    intro e he
    obtain ⟨ks, hks, hkv, -⟩ := tokenKey_left p e color cs c (hcs e he) hcl hc
    obtain ⟨req, h1, h2⟩ := read_req' (Kernel.balance_spec H p e st.ledger (left color) ks (leftKey c) hks hkv cfs bal
      hctx hb hwf)
    refine ⟨req, h1, ?_⟩
    show ledgerOracle H req st.ledger = _
    rw [h2]
    unfold balAtom at hB
    cases hg : assocGet (leftKey c) bal with
    | none => rw [hg] at hB; simp at hB; subst hB; rfl
    | some v =>
      rw [hg] at hB
      match v, hB with
      | .cell ⟨al, [B']⟩, hB =>
        simp at hB; subst hB
        simp [fieldsOf_small' (k := 16) (by decide) (by simpa using hB128)]
  refine (XRuns.ledgerReadG (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (s := s) (st := st) (gb := gb) (roundTrip_uint uint128_bound)
    (ReadOps.popeq_last _ true [.bytes 16]) (by rw [Value.width_uint]; decide) hg hres).conseq
    ⟨fun _ => trivial, fun _ _ => ⟨_, _, rfl, by rw [Value.width_uint]; rfl⟩⟩ ?_
  intro r e w' l ⟨hw, hq⟩
  cases gb with
  | true =>
    simp only [ite_true] at hq ⊢
    obtain ⟨ys, hy, hi⟩ := hq
    simp only [Option.some.injEq, Prod.mk.injEq] at hy
    obtain ⟨rfl, rfl⟩ := hy
    exact ⟨hw, rfl, hi⟩
  | false =>
    simp only [Bool.false_eq_true, ite_false] at hq ⊢
    exact ⟨hw, hq.1, by have := hq.2; rw [Value.width_uint] at this; exact this⟩

/-- **`unshieldedBalanceLt color amount`** (`Kernel.balanceLessThan`), under a
    guard meaning `gb`, the balance atom `B` (0 when absent) and the amount
    meaning `av`: with the guard on it completes exactly when `B` and `av` both
    fit 64 bits (the VM's `lt` is `u64`; a balance or amount of `2^64` or more
    fails the transaction), and then means `B < av`; with it off it means false.
    Nothing changes. -/
theorem unshieldedBalanceLt_runs (color : Bytes 32) (amount : Uint128) {s : Build} {st : Exec.State ω LedgerState}
    {gb : Bool} (hg : GuardIs p s st.runState gb) (cs : List Fr) (hcl : cs.length = 2)
    (hcs : Stable s.next st.env (fun e => Value.Is p e color cs))
    (c : Nat) (hc : AV.ofFields [.bytes 32] cs = some ⟨[.bytes 32], [c]⟩)
    (av : Fr) (hav : Stable s.next st.env (fun e => amount.expr.eval p e = some av))
    (cfs : List SV) (bal : List (AV × SV)) (hctx : st.ledger.context = .array cfs) (hb : cfs[5]? = some (.map bal))
    (hwf : st.ledger.WF) (B : Nat) (hB : balAtom bal (leftKey c) = some B) :
    XRuns p (oracles H (Damp.Exec.liftWitness w)) (unshieldedBalanceLt color amount) s st (gb = true → B < 2 ^ 64 ∧ av.val < 2 ^ 64)
      (fun r e w' l => w' = st.private_ ∧ l = st.ledger ∧ Boolean.Is p e r (gb && decide (B < av.val))) := by
  let pre : List (Op Expr) :=
      [.dup 2, .idx true false [fieldKey 5], .dup 0, .push false (alignedOf (left color : TokenType)), .member,
       .branch 3, .pop, .push false ⟨[.bytes 16], [.const 0]⟩, .jmp 1, .idx true false [alignedOf (left color : TokenType)],
       .push false ⟨[.bytes 16], [amount.expr]⟩, .lt]
  rw [show unshieldedBalanceLt color amount = ledgerRead Boolean (fun es => pre ++ [.popeq true [.bytes 1] es]) from rfl]
  exact boolRead_runs H p w (P := B < 2 ^ 64 ∧ av.val < 2 ^ 64) (b := decide (B < av.val))
    (ReadOps.popeq_last pre true [.bytes 1]) hg fun e he => by
    obtain ⟨ks, hks, hkv, -⟩ := tokenKey_left p e color cs c (hcs e he) hcl hc
    exact read_req' (Kernel.balanceLessThan_spec H p e st.ledger (left color) amount ks (leftKey c) hks hkv av
      (hav e he) cfs bal hctx hb hwf B hB)

/-- `unshieldedBalanceGte`: the negation of `unshieldedBalanceLt`. -/
theorem unshieldedBalanceGte_runs (color : Bytes 32) (amount : Uint128) {s : Build} {st : Exec.State ω LedgerState}
    {gb : Bool} (hg : GuardIs p s st.runState gb) (cs : List Fr) (hcl : cs.length = 2)
    (hcs : Stable s.next st.env (fun e => Value.Is p e color cs))
    (c : Nat) (hc : AV.ofFields [.bytes 32] cs = some ⟨[.bytes 32], [c]⟩)
    (av : Fr) (hav : Stable s.next st.env (fun e => amount.expr.eval p e = some av))
    (cfs : List SV) (bal : List (AV × SV)) (hctx : st.ledger.context = .array cfs) (hb : cfs[5]? = some (.map bal))
    (hwf : st.ledger.WF) (B : Nat) (hB : balAtom bal (leftKey c) = some B) :
    XRuns p (oracles H (Damp.Exec.liftWitness w)) (unshieldedBalanceGte color amount) s st (gb = true → B < 2 ^ 64 ∧ av.val < 2 ^ 64)
      (fun r e w' l => w' = st.private_ ∧ l = st.ledger ∧ Boolean.Is p e r (!(gb && decide (B < av.val)))) := by
  unfold unshieldedBalanceGte
  refine (XRuns.seq (ok₂ := True) (unshieldedBalanceLt_runs H p w color amount hg cs hcl hcs c hc av hav cfs bal hctx hb
    hwf B hB) (fun _ => Grows.pure' _) fun a s₁ st₁ hn₁ hgd₁ ha₁ hQ₁ =>
    XRuns.pure (hQ₁.imp fun e h => ⟨h.1, h.2.1, Boolean.not_is h.2.2⟩)).conseq (by simp) fun _ _ _ _ h => h

/-- **`unshieldedBalanceGt color amount`** (`Kernel.balanceGreaterThan`): as
    `unshieldedBalanceLt_runs`, meaning `av < B`. -/
theorem unshieldedBalanceGt_runs (color : Bytes 32) (amount : Uint128) {s : Build} {st : Exec.State ω LedgerState}
    {gb : Bool} (hg : GuardIs p s st.runState gb) (cs : List Fr) (hcl : cs.length = 2)
    (hcs : Stable s.next st.env (fun e => Value.Is p e color cs))
    (c : Nat) (hc : AV.ofFields [.bytes 32] cs = some ⟨[.bytes 32], [c]⟩)
    (av : Fr) (hav : Stable s.next st.env (fun e => amount.expr.eval p e = some av))
    (cfs : List SV) (bal : List (AV × SV)) (hctx : st.ledger.context = .array cfs) (hb : cfs[5]? = some (.map bal))
    (hwf : st.ledger.WF) (B : Nat) (hB : balAtom bal (leftKey c) = some B) :
    XRuns p (oracles H (Damp.Exec.liftWitness w)) (unshieldedBalanceGt color amount) s st (gb = true → B < 2 ^ 64 ∧ av.val < 2 ^ 64)
      (fun r e w' l => w' = st.private_ ∧ l = st.ledger ∧ Boolean.Is p e r (gb && decide (av.val < B))) := by
  let pre : List (Op Expr) :=
      [.push false ⟨[.bytes 16], [amount.expr]⟩, .dup 3, .idx true false [fieldKey 5], .dup 0,
       .push false (alignedOf (left color : TokenType)), .member, .branch 3, .pop,
       .push false ⟨[.bytes 16], [.const 0]⟩, .jmp 1, .idx true false [alignedOf (left color : TokenType)], .lt]
  rw [show unshieldedBalanceGt color amount = ledgerRead Boolean (fun es => pre ++ [.popeq true [.bytes 1] es]) from rfl]
  exact boolRead_runs H p w (P := B < 2 ^ 64 ∧ av.val < 2 ^ 64) (b := decide (av.val < B))
    (ReadOps.popeq_last pre true [.bytes 1]) hg fun e he => by
    obtain ⟨ks, hks, hkv, -⟩ := tokenKey_left p e color cs c (hcs e he) hcl hc
    exact read_req' (Kernel.balanceGreaterThan_spec H p e st.ledger (left color) amount ks (leftKey c) hks hkv av
      (hav e he) cfs bal hctx hb hwf B hB)

/-- `unshieldedBalanceLte`: the negation of `unshieldedBalanceGt`. -/
theorem unshieldedBalanceLte_runs (color : Bytes 32) (amount : Uint128) {s : Build} {st : Exec.State ω LedgerState}
    {gb : Bool} (hg : GuardIs p s st.runState gb) (cs : List Fr) (hcl : cs.length = 2)
    (hcs : Stable s.next st.env (fun e => Value.Is p e color cs))
    (c : Nat) (hc : AV.ofFields [.bytes 32] cs = some ⟨[.bytes 32], [c]⟩)
    (av : Fr) (hav : Stable s.next st.env (fun e => amount.expr.eval p e = some av))
    (cfs : List SV) (bal : List (AV × SV)) (hctx : st.ledger.context = .array cfs) (hb : cfs[5]? = some (.map bal))
    (hwf : st.ledger.WF) (B : Nat) (hB : balAtom bal (leftKey c) = some B) :
    XRuns p (oracles H (Damp.Exec.liftWitness w)) (unshieldedBalanceLte color amount) s st (gb = true → B < 2 ^ 64 ∧ av.val < 2 ^ 64)
      (fun r e w' l => w' = st.private_ ∧ l = st.ledger ∧ Boolean.Is p e r (!(gb && decide (av.val < B)))) := by
  unfold unshieldedBalanceLte
  refine (XRuns.seq (ok₂ := True) (unshieldedBalanceGt_runs H p w color amount hg cs hcl hcs c hc av hav cfs bal hctx hb
    hwf B hB) (fun _ => Grows.pure' _) fun a s₁ st₁ hn₁ hgd₁ ha₁ hQ₁ =>
    XRuns.pure (hQ₁.imp fun e h => ⟨h.1, h.2.1, Boolean.not_is h.2.2⟩)).conseq (by simp) fun _ _ _ _ h => h

/-- **`receiveUnshielded color amount`, under a guard of either value**
    (`receiveUnshielded_runs` is the guard-on case): with the guard on it
    completes exactly when the addition to slot 6 fits; with it off nothing
    changes. -/
theorem receiveUnshielded_runsG (color : Bytes 32) (amount : Uint128) {s : Build} {st : Exec.State ω LedgerState}
    {gb : Bool} (hg : GuardIs p s st.runState gb) (cs : List Fr) (hcl : cs.length = 2)
    (hcs : Stable s.next st.env (fun e => Value.Is p e color cs))
    (c : Nat) (hc : AV.ofFields [.bytes 32] cs = some ⟨[.bytes 32], [c]⟩)
    (a : Fr) (ha : Stable s.next st.env (fun e => amount.expr.eval p e = some a)) (ha128 : a.val < 2 ^ 128)
    (es : List SV) (m : List (AV × SV)) (hwf : st.ledger.WF) (heff : st.ledger.effects = .array es)
    (hm : es[6]? = some (.map m)) :
    XRuns p (oracles H (Damp.Exec.liftWitness w)) (receiveUnshielded color amount) s st (gb = true → addOk m (leftKey c) a.val)
      (fun _ _ w' l => w' = st.private_ ∧ l = if gb then
        { st.ledger with effects := .array (es.set 6 (addMap 6 m (leftKey c) a.val)) } else st.ledger) :=
  (XRuns.condOp rfl (by simp [receiveUnshieldedOps]) hg fun e he => by
    obtain ⟨ks, hks, hkv, hok⟩ := tokenKey_left p e color cs c (hcs e he) hcl hc
    exact Kernel.incUnshieldedInputs_spec H p e st.ledger es m (left color) amount ks (leftKey c) a hwf heff hm
      hks hkv hok (ha e he) ha128).conseq Iff.rfl fun _ _ _ _ h => ⟨h.1, h.2.2⟩

/-! ## Shielded tokens: `mergeCoin` -/

/-- A 32-byte atom as an effects key. -/
abbrev hkey (x : Nat) : AV := ⟨[.bytes 32], [x]⟩

/-- A qualified coin whose parts mean `n` (nonce limbs), `c` (color limbs),
    `v` (value) and `i` (Merkle index). -/
structure QCoinIs (p : Zkir.Prims) (e : Env) (q : QualifiedShieldedCoinInfo) (n c : List Fr) (v i : Fr) : Prop where
  nonce : Value.Is p e q.nonce n
  color : Value.Is p e q.color c
  value : q.value.expr.eval p e = some v
  index : q.mt_index.expr.eval p e = some i

theorem QCoinIs.is {e : Env} {q : QualifiedShieldedCoinInfo} {n c : List Fr} {v i : Fr} (h : QCoinIs p e q n c v i) :
    Value.Is p e q (n ++ c ++ [v, i]) := by
  unfold Value.Is
  show Expr.evalList p e (q.nonce.limbs ++ (q.color.limbs ++ ([q.value.expr] ++ ([q.mt_index.expr] ++ [])))) = _
  rw [show n ++ c ++ [v, i] = n ++ (c ++ [v, i]) by simp]
  exact evalList_append_some (p := p) (env := e) h.nonce (evalList_append_some h.color
    (show Expr.evalList p e ([q.value.expr] ++ ([q.mt_index.expr] ++ [])) = some [v, i] by
      simp [Expr.evalList, h.value, h.index]))

theorem QCoinIs.down {e : Env} {q : QualifiedShieldedCoinInfo} {n c : List Fr} {v i : Fr} (h : QCoinIs p e q n c v i) :
    Value.Is p e ({ nonce := q.nonce, color := q.color, value := q.value } : ShieldedCoinInfo) (n ++ c ++ [v]) := by
  unfold Value.Is
  show Expr.evalList p e (q.nonce.limbs ++ (q.color.limbs ++ ([q.value.expr] ++ []))) = _
  rw [show n ++ c ++ [v] = n ++ (c ++ [v]) by simp]
  exact evalList_append_some (p := p) (env := e) h.nonce (evalList_append_some h.color
    (show Expr.evalList p e ([q.value.expr] ++ []) = some [v] by simp [Expr.evalList, h.value]))

theorem QCoinIs.later {k k' : Nat} {env env' : Env} {q : QualifiedShieldedCoinInfo} {n c : List Fr} {v i : Fr}
    (h : Stable k env (fun e => QCoinIs p e q n c v i)) (ha : Agree k env env') (hk : k ≤ k') :
    Stable k' env' (fun e => QCoinIs p e q n c v i) := h.later ha hk

theorem uint128_means {e : Env} {a : Uint128} {v : Fr} (h : a.expr.eval p e = some v) (hv : v.val < 2 ^ 128) :
    Uint.Means p e a v.val :=
  ⟨uint128_bound, by show v.val ≤ 340282366920938463463374607431768211455; omega,
   by rw [h]; congr 1; exact (Fr.ext (Fr.val_ofNat_of_lt v.isLt)).symm⟩

/-- The effects after `mergeCoin` with the guard on: both nullifiers claimed
    (slot 0), the new coin's commitment claimed as spent (2) and received (1). -/
def mergeEffects (es : List SV) (m0 m1 m2 : List (AV × SV)) (xa xb y : Nat) : List SV :=
  ((es.set 0 (.map (assocSet (hkey xb) .null (assocSet (hkey xa) .null m0)))).set 2
    (.map (assocSet (hkey y) .null m2))).set 1 (.map (assocSet (hkey y) .null m1))

/-- **`mergeCoin a b`**, under a guard that holds. The coins' parts mean
    `an, ac, av, ai` and `bn, bc, bv, bi` (values below `2^128`); the address
    read is `selfFs`. Whatever the hashes give: the nullifiers (`cnPre`) are
    the atoms `xa`, `xb`; the new coin is `(nn, ac, av + bv)` with `nn` the
    derived nonce of `an`; its commitment to this contract is the atom `y`. The
    built-in witness is asked to spend `a`, then `b`, then to create the new
    coin (answers given: no field elements, private states `ω₁`, `ω₂`, `ω₃`).
    The call completes exactly when the colors agree and `av + bv < 2^128`;
    the result is the new coin, the private state `ω₃`, and the ledger changes
    only in the effects (`mergeEffects`). -/
theorem mergeCoin_runs (a b : QualifiedShieldedCoinInfo) {s : Build} {st : Exec.State ω LedgerState}
    (hg : GuardIs p s st.runState true) (an ac bn bc : List Fr) (av ai bv bi : Fr)
    (hanl : a.nonce.limbs.length = 2) (hacl : ac.length = 2) (hbcl : bc.length = 2)
    (hav : av.val < 2 ^ 128) (hbv : bv.val < 2 ^ 128)
    (ha : Stable s.next st.env (fun e => QCoinIs p e a an ac av ai))
    (hb : Stable s.next st.env (fun e => QCoinIs p e b bn bc bv bi))
    (cfs : List SV) (wa : AV) (selfFs : List Fr) (hctx : st.ledger.context = .array cfs)
    (hc0 : cfs[0]? = some (.cell wa)) (hself : fieldsOf [.bytes 32] wa.atoms = some selfFs) (hwf : st.ledger.WF)
    (es : List SV) (m0 m1 m2 : List (AV × SV)) (heff : st.ledger.effects = .array es)
    (hm0 : es[0]? = some (.map m0)) (hm1 : es[1]? = some (.map m1)) (hm2 : es[2]? = some (.map m2))
    (nfa nfb : List Fr) (xa xb : Nat)
    (hnfa : phashFs p coinPreimageAlign (cnPre (an ++ ac ++ [av]) selfFs) = some nfa)
    (hxa : AV.ofFields [.bytes 32] nfa = some (hkey xa))
    (hnfb : phashFs p coinPreimageAlign (cnPre (bn ++ bc ++ [bv]) selfFs) = some nfb)
    (hxb : AV.ofFields [.bytes 32] nfb = some (hkey xb))
    (cm : List Fr) (y : Nat)
    (hcm : phashFs p coinPreimageAlign (ccPre (derivedNonceFs p "midnight:kernel:nonce_evolve" an ++ ac ++
      [Fr.ofNat (av.val + bv.val)]) false [0, 0] selfFs) = some cm)
    (hy : AV.ofFields [.bytes 32] cm = some (hkey y))
    (ω₁ ω₂ ω₃ : ω)
    (hw₁ : w "createZswapInput" (an ++ ac ++ [av, ai]) st.private_ = some ([], ω₁))
    (hw₂ : w "createZswapInput" (bn ++ bc ++ [bv, bi]) ω₁ = some ([], ω₂))
    (hw₃ : w "createZswapOutput" ((derivedNonceFs p "midnight:kernel:nonce_evolve" an ++ ac ++
      [Fr.ofNat (av.val + bv.val)]) ++ (Fr.ofBool false :: [0, 0] ++ selfFs)) ω₂ = some ([], ω₃)) :
    XRuns p (oracles H (Damp.Exec.liftWitness w)) (mergeCoin a b) s st (ac = bc ∧ av.val + bv.val < 2 ^ 128)
      (fun r e w' l => Value.Is p e r (derivedNonceFs p "midnight:kernel:nonce_evolve" an ++ ac ++
          [Fr.ofNat (av.val + bv.val)]) ∧ w' = ω₃ ∧
        l = { st.ledger with effects := .array (mergeEffects es m0 m1 m2 xa xb y) }) := by
  have hsl := fieldsOf_bytes32_length hself
  let σ := st.ledger
  let nn := derivedNonceFs p "midnight:kernel:nonce_evolve" an
  let vv := av.val + bv.val
  let mA := assocSet (hkey xa) .null m0
  let es₁ := es.set 0 (.map mA)
  let es₂ := es₁.set 0 (.map (assocSet (hkey xb) .null mA))
  let es₃ := es₂.set 2 (.map (assocSet (hkey y) .null m2))
  let es₄ := es₃.set 1 (.map (assocSet (hkey y) .null m1))
  let L : List SV → LedgerState := fun es' => { σ with effects := .array es' }
  have hmA : es₁[0]? = some (.map mA) := List.getElem?_set_self (lt_of_getElem? hm0)
  have hm2' : es₂[2]? = some (.map m2) := by simp [es₂, es₁, List.getElem?_set_ne, hm2]
  have hm1' : es₃[1]? = some (.map m1) := by simp [es₃, es₂, es₁, List.getElem?_set_ne, hm1]
  have hwf₁ : (L es₁).WF := claimed_wf H (by decide) hxa hwf heff hm0
  have hwf₂ : (L es₂).WF := claimed_wf H (σ := L es₁) (by decide) hxb hwf₁ rfl hmA
  have hwf₃ : (L es₃).WF := claimed_wf H (σ := L es₂) (by decide) hy hwf₂ rfl hm2'
  -- 1. `const selfAddr ← Kernel.self`
  have h1 : XRuns p (oracles H (Damp.Exec.liftWitness w)) (valM Kernel.self "selfAddr") s st True
      (fun r e w' l => Value.Is p e r selfFs ∧ w' = st.private_ ∧ l = σ ∧ Value.Shaped r) := by
    unfold valM
    refine (XRuns.seq (ok₂ := True) (self_runs H p w hg cfs wa selfFs hctx hc0 hself hwf)
      (fun _ => Grows.val _ _) fun x s₁ st₁ hn₁ hgd₁ ha₁ hQ₁ => ?_).conseq (by simp) fun _ _ _ _ h => h
    obtain ⟨hw₁, hl₁, -, hsh₁⟩ := hQ₁.holds
    have hlen : (Value.toExprs x).length = Value.width ContractAddress := ContractAddress.shaped_len hsh₁
    exact ((XRuns.val (p := p) (O := oracles H (Damp.Exec.liftWitness w)) roundTrip_contractAddress "selfAddr" hlen
      (hQ₁.imp fun e h => h.2.2.1)).addResult (val_shaped x "selfAddr" s₁ hlen)).conseq Iff.rfl
      fun r e w' l h => ⟨h.1.1, h.1.2.1.trans hw₁, h.1.2.2.trans hl₁, h.2⟩
  unfold mergeCoin
  refine (XRuns.seq (ok₂ := ac = bc ∧ vv < 2 ^ 128) h1
    (fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.require _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.castTo _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _)
    fun selfAddr s₁ st₁ hn₁ hgd₁ ha₁ hQ₁ => ?_).conseq (ok' := ac = bc ∧ av.val + bv.val < 2 ^ 128) (by simp [vv])
      fun _ _ _ _ h => h
  obtain ⟨-, hP₁, hL₁, hshS⟩ := hQ₁.holds
  have hS₁ : Stable s₁.next st₁.env (fun e => Value.Is p e selfAddr selfFs) := hQ₁.imp fun e h => h.1
  have hg₁ := GuardIs.later hg ha₁ hn₁ hgd₁
  have ha₁' := ha.later ha₁ hn₁
  have hb₁' := hb.later ha₁ hn₁
  -- 2. `createZswapInput a`
  refine (XRuns.seq (ok₂ := ac = bc ∧ vv < 2 ^ 128)
    ((XRuns.askWitness0_iso (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (α := Unit) rfl rfl "createZswapInput" hg₁ ha₁'.holds.is).conseq
      (ok' := True) ⟨fun _ => trivial, fun _ => ⟨ω₁, by rw [hP₁]; exact hw₁⟩⟩
      (Q' := fun _ _ w' l => l = st₁.ledger ∧ w' = ω₁) fun _ _ w' l h => ⟨h.1, by
        have h2 := h.2; rw [hP₁] at h2; change w _ _ _ = _ at h2; rw [hw₁] at h2; simp at h2; exact h2.symm⟩)
    (fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.require _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.castTo _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _)
    fun _ s₂ st₂ hn₂ hgd₂ ha₂ hQ₂ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hL₂, hP₂⟩ := hQ₂.holds
  have hg₂ := GuardIs.later hg₁ ha₂ hn₂ hgd₂
  have hS₂ := hS₁.later ha₂ hn₂
  have ha₂' := ha₁'.later ha₂ hn₂
  have hb₂' := hb₁'.later ha₂ hn₂
  -- 3. `claimZswapNullifier (coinNullifier a selfAddr)`
  refine (XRuns.seq (ok₂ := ac = bc ∧ vv < 2 ^ 128)
    (XRuns.someOp (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (σ₁ := L es₁) rfl (by simp) hg₂ fun e he => by
      rw [hL₂, hL₁]
      exact Kernel.claimZswapNullifier_spec H p e σ es m0 _ nfa (hkey xa) hwf heff hm0
        (coinNullifier_is (ha₂' e he).down (hS₂ e he) hnfa) hxa)
    (fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.require _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.castTo _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _)
    fun _ s₃ st₃ hn₃ hgd₃ ha₃ hQ₃ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hP₃, hL₃⟩ := hQ₃.holds
  simp only [ite_true] at hL₃
  have hg₃ := GuardIs.later hg₂ ha₃ hn₃ hgd₃
  have hS₃ := hS₂.later ha₃ hn₃
  have ha₃' := ha₂'.later ha₃ hn₃
  have hb₃' := hb₂'.later ha₃ hn₃
  -- 4. `createZswapInput b`
  refine (XRuns.seq (ok₂ := ac = bc ∧ vv < 2 ^ 128)
    ((XRuns.askWitness0_iso (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (α := Unit) rfl rfl "createZswapInput" hg₃ hb₃'.holds.is).conseq
      (ok' := True) ⟨fun _ => trivial, fun _ => ⟨ω₂, by rw [hP₃, hP₂]; exact hw₂⟩⟩
      (Q' := fun _ _ w' l => l = st₃.ledger ∧ w' = ω₂) fun _ _ w' l h => ⟨h.1, by
        have h2 := h.2; rw [hP₃, hP₂] at h2; change w _ _ _ = _ at h2; rw [hw₂] at h2; simp at h2; exact h2.symm⟩)
    (fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.require _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.castTo _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _)
    fun _ s₄ st₄ hn₄ hgd₄ ha₄ hQ₄ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hL₄, hP₄⟩ := hQ₄.holds
  have hg₄ := GuardIs.later hg₃ ha₄ hn₄ hgd₄
  have hS₄ := hS₃.later ha₄ hn₄
  have ha₄' := ha₃'.later ha₄ hn₄
  have hb₄' := hb₃'.later ha₄ hn₄
  -- 5. `claimZswapNullifier (coinNullifier b selfAddr)`
  refine (XRuns.seq (ok₂ := ac = bc ∧ vv < 2 ^ 128)
    (XRuns.someOp (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (σ₁ := L es₂) rfl (by simp) hg₄ fun e he => by
      rw [hL₄, hL₃]
      exact Kernel.claimZswapNullifier_spec H p e (L es₁) es₁ mA _ nfb (hkey xb) hwf₁ rfl hmA
        (coinNullifier_is (hb₄' e he).down (hS₄ e he) hnfb) hxb)
    (fun _ => Grows.bind (Grows.require _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.castTo _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _)
    fun _ s₅ st₅ hn₅ hgd₅ ha₅ hQ₅ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hP₅, hL₅⟩ := hQ₅.holds
  simp only [ite_true] at hL₅
  have hg₅ := GuardIs.later hg₄ ha₅ hn₅ hgd₅
  have hS₅ := hS₄.later ha₅ hn₅
  have ha₅' := ha₄'.later ha₅ hn₅
  have hb₅' := hb₄'.later ha₅ hn₅
  -- 6. `require (a.color ==. b.color)`
  have hcolor : Stable s₅.next st₅.env (fun e => Boolean.Is p e (a.color ==. b.color) (decide (ac = bc))) :=
    fun e he => valueEq_is (p := p) (ha₅' e he).color (hb₅' e he).color (by rw [hacl, hbcl])
  refine (XRuns.seq (ok₂ := vv < 2 ^ 128)
    (XRuns.lift (O := oracles H (Damp.Exec.liftWitness w)) (st := st₅) (Runs.require (p := p) (st := st₅.runState) _ hg₅ hcolor)
      (Quiet.require _ _))
    (fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.castTo _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _)
    fun _ s₆ st₆ hn₆ hgd₆ ha₆ hQ₆ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨-, hP₆, hL₆⟩ := hQ₆.holds
  have hg₆ := GuardIs.later hg₅ ha₆ hn₆ hgd₆
  have hS₆ := hS₅.later ha₆ hn₆
  have ha₆' := ha₅'.later ha₆ hn₆
  have hb₆' := hb₅'.later ha₆ hn₆
  -- 7. `const nonce := derivedNonce … a.nonce`
  refine (XRuns.seq (ok₂ := vv < 2 ^ 128)
    (XRuns.val (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (s := s₆) (st := st₆) roundTrip_bytes (xs := nn) "nonce" rfl
      fun e he => derivedNonce_is "midnight:kernel:nonce_evolve" hanl (ha₆' e he).nonce)
    (fun _ => Grows.bind (Grows.castTo _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _)
    fun nonce s₇ st₇ hn₇ hgd₇ ha₇ hQ₇ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨-, hP₇, hL₇⟩ := hQ₇.holds
  have hN₇ : Stable s₇.next st₇.env (fun e => Value.Is p e nonce nn) := hQ₇.imp fun e h => h.1
  have hg₇ := GuardIs.later hg₆ ha₇ hn₇ hgd₇
  have hS₇ := hS₆.later ha₇ hn₇
  have ha₇' := ha₆'.later ha₇ hn₇
  have hb₇' := hb₆'.later ha₇ hn₇
  -- 8. `(a.value + b.value).castTo (2^128 - 1)`
  have hsum : Stable s₇.next st₇.env (fun e => Uint.Means p e (a.value + b.value) vv) := fun e he =>
    Uint.add_means (by decide) (uint128_means p (ha₇' e he).value hav) (uint128_means p (hb₇' e he).value hbv)
  refine (XRuns.seq (ok₂ := True)
    (XRuns.lift (O := oracles H (Damp.Exec.liftWitness w)) (st := st₇) (Runs.castTo (p := p) (st := st₇.runState) uint128_bound hg₇ hsum)
      (Quiet.castTo _ _))
    (fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _)
    fun value s₈ st₈ hn₈ hgd₈ ha₈ hQ₈ => ?_).conseq
    (by simp only [forall_const, and_true, vv]; constructor <;> intro h <;> omega) fun _ _ _ _ h => h
  obtain ⟨-, hP₈, hL₈⟩ := hQ₈.holds
  have hV₈ : Stable s₈.next st₈.env (fun e => Uint.Means p e value vv) := hQ₈.imp fun e h => by
    simpa using h.1
  have hg₈ := GuardIs.later hg₇ ha₈ hn₈ hgd₈
  have hS₈ := hS₇.later ha₈ hn₈
  have ha₈' := ha₇'.later ha₈ hn₈
  have hN₈ := hN₇.later ha₈ hn₈
  have hcoin : Stable s₈.next st₈.env (fun e => Value.Is p e
      ({ nonce := nonce, color := a.color, value := value } : ShieldedCoinInfo) (nn ++ ac ++ [Fr.ofNat vv])) := by
    intro e he
    unfold Value.Is
    show Expr.evalList p e (nonce.limbs ++ (a.color.limbs ++ ([value.expr] ++ []))) = _
    rw [show nn ++ ac ++ [Fr.ofNat vv] = nn ++ (ac ++ [Fr.ofNat vv]) by simp]
    exact evalList_append_some (hN₈ e he) (evalList_append_some (ha₈' e he).color
      (by simp [Expr.evalList, (hV₈ e he).eval]))
  have hrecip : Stable s₈.next st₈.env (fun e => Value.Is p e (right selfAddr : Either ZswapCoinPublicKey ContractAddress)
      (Fr.ofBool false :: [0, 0] ++ selfFs)) := fun e he => right_self_is p (hS₈ e he)
  -- 9. `createZswapOutput newCoin (right selfAddr)`
  refine (XRuns.seq (ok₂ := True)
    ((XRuns.askWitness0_iso (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (α := Unit) rfl rfl "createZswapOutput" hg₈
      (evalList_append_some hcoin.holds hrecip.holds)).conseq
      (ok' := True) ⟨fun _ => trivial, fun _ => ⟨ω₃, by rw [hP₈, hP₇, hP₆, hP₅, hP₄]; exact hw₃⟩⟩
      (Q' := fun _ _ w' l => l = st₈.ledger ∧ w' = ω₃) fun _ _ w' l h => ⟨h.1, by
        have h2 := h.2; rw [hP₈, hP₇, hP₆, hP₅, hP₄] at h2; change w _ _ _ = _ at h2; rw [hw₃] at h2; simp at h2
        exact h2.symm⟩)
    (fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _)
    fun _ s₉ st₉ hn₉ hgd₉ ha₉ hQ₉ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hL₉, hP₉⟩ := hQ₉.holds
  have hg₉ := GuardIs.later hg₈ ha₉ hn₉ hgd₉
  have hcoin₉ := hcoin.later ha₉ hn₉
  have hrecip₉ := hrecip.later ha₉ hn₉
  have hshR : (Value.toExprs (right selfAddr : Either ZswapCoinPublicKey ContractAddress).left).length = 2 ∧
      (Value.toExprs (right selfAddr : Either ZswapCoinPublicKey ContractAddress).right).length = 2 :=
    ⟨rfl, ContractAddress.shaped_len hshS⟩
  -- 10. `const cm := coinCommitment newCoin (right selfAddr)`
  refine (XRuns.seq (ok₂ := True)
    (XRuns.val (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (s := s₉) (st := st₉) roundTrip_bytes (xs := cm) "cm" rfl
      fun e he => coinCommitment_is (hcoin₉ e he) hshR rfl (hrecip₉ e he) hcm)
    (fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _)
    fun cmv s₁₀ st₁₀ hn₁₀ hgd₁₀ ha₁₀ hQ₁₀ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨-, hP₁₀, hL₁₀⟩ := hQ₁₀.holds
  have hC₁₀ : Stable s₁₀.next st₁₀.env (fun e => Value.Is p e cmv cm) := hQ₁₀.imp fun e h => h.1
  have hg₁₀ := GuardIs.later hg₉ ha₁₀ hn₁₀ hgd₁₀
  have hcoin₁₀ := hcoin₉.later ha₁₀ hn₁₀
  have hLs : st₁₀.ledger = L es₂ := by rw [hL₁₀, hL₉, hL₈, hL₇, hL₆, hL₅]
  -- 11. `claimZswapCoinSpend cm`
  refine (XRuns.seq (ok₂ := True)
    (XRuns.someOp (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (σ₁ := L es₃) rfl (by simp) hg₁₀ fun e he => by
      rw [hLs]
      exact Kernel.claimZswapCoinSpend_spec H p e (L es₂) es₂ m2 cmv cm (hkey y) hwf₂ rfl hm2' (hC₁₀ e he) hy)
    (fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _)
    fun _ s₁₁ st₁₁ hn₁₁ hgd₁₁ ha₁₁ hQ₁₁ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hP₁₁, hL₁₁⟩ := hQ₁₁.holds
  simp only [ite_true] at hL₁₁
  have hg₁₁ := GuardIs.later hg₁₀ ha₁₁ hn₁₁ hgd₁₁
  -- 12. `claimZswapCoinReceive cm`
  refine (XRuns.seq (ok₂ := True)
    (XRuns.someOp (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (σ₁ := L es₄) rfl (by simp) hg₁₁ fun e he => by
      rw [hL₁₁]
      exact Kernel.claimZswapCoinReceive_spec H p e (L es₃) es₃ m1 cmv cm (hkey y) hwf₃ rfl hm1'
        ((hC₁₀.later ha₁₁ hn₁₁) e he) hy)
    (fun _ => Grows.pure' _)
    fun _ s₁₂ st₁₂ hn₁₂ hgd₁₂ ha₁₂ hQ₁₂ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hP₁₂, hL₁₂⟩ := hQ₁₂.holds
  simp only [ite_true] at hL₁₂
  -- 13. `return newCoin`
  refine XRuns.pure fun e he => ⟨((hcoin₁₀.later ha₁₁ hn₁₁).later ha₁₂ hn₁₂) e he, ?_, ?_⟩
  · rw [hP₁₂, hP₁₁, hP₁₀, hP₉]
  · rw [hL₁₂]; simp [L, es₄, es₃, es₂, es₁, mergeEffects, List.set_set, mA, σ]
/-- A coin whose parts mean `n`, `c`, `v`. -/
structure CoinIs (p : Zkir.Prims) (e : Env) (q : ShieldedCoinInfo) (n c : List Fr) (v : Fr) : Prop where
  nonce : Value.Is p e q.nonce n
  color : Value.Is p e q.color c
  value : q.value.expr.eval p e = some v

/-- **`mergeCoinImmediate a b`** is `mergeCoin a b'`, `b'` the coin `b` with Merkle
    index 0: as `mergeCoin_runs`, the second input answered for `bn ++ bc ++ [bv, 0]`. -/
theorem mergeCoinImmediate_runs (a : QualifiedShieldedCoinInfo) (b : ShieldedCoinInfo) {s : Build}
    {st : Exec.State ω LedgerState}
    (hg : GuardIs p s st.runState true) (an ac bn bc : List Fr) (av ai bv : Fr)
    (hanl : a.nonce.limbs.length = 2) (hacl : ac.length = 2) (hbcl : bc.length = 2)
    (hav : av.val < 2 ^ 128) (hbv : bv.val < 2 ^ 128)
    (ha : Stable s.next st.env (fun e => QCoinIs p e a an ac av ai))
    (hb : Stable s.next st.env (fun e => CoinIs p e b bn bc bv))
    (cfs : List SV) (wa : AV) (selfFs : List Fr) (hctx : st.ledger.context = .array cfs)
    (hc0 : cfs[0]? = some (.cell wa)) (hself : fieldsOf [.bytes 32] wa.atoms = some selfFs) (hwf : st.ledger.WF)
    (es : List SV) (m0 m1 m2 : List (AV × SV)) (heff : st.ledger.effects = .array es)
    (hm0 : es[0]? = some (.map m0)) (hm1 : es[1]? = some (.map m1)) (hm2 : es[2]? = some (.map m2))
    (nfa nfb : List Fr) (xa xb : Nat)
    (hnfa : phashFs p coinPreimageAlign (cnPre (an ++ ac ++ [av]) selfFs) = some nfa)
    (hxa : AV.ofFields [.bytes 32] nfa = some (hkey xa))
    (hnfb : phashFs p coinPreimageAlign (cnPre (bn ++ bc ++ [bv]) selfFs) = some nfb)
    (hxb : AV.ofFields [.bytes 32] nfb = some (hkey xb))
    (cm : List Fr) (y : Nat)
    (hcm : phashFs p coinPreimageAlign (ccPre (derivedNonceFs p "midnight:kernel:nonce_evolve" an ++ ac ++
      [Fr.ofNat (av.val + bv.val)]) false [0, 0] selfFs) = some cm)
    (hy : AV.ofFields [.bytes 32] cm = some (hkey y))
    (ω₁ ω₂ ω₃ : ω)
    (hw₁ : w "createZswapInput" (an ++ ac ++ [av, ai]) st.private_ = some ([], ω₁))
    (hw₂ : w "createZswapInput" (bn ++ bc ++ [bv, 0]) ω₁ = some ([], ω₂))
    (hw₃ : w "createZswapOutput" ((derivedNonceFs p "midnight:kernel:nonce_evolve" an ++ ac ++
      [Fr.ofNat (av.val + bv.val)]) ++ (Fr.ofBool false :: [0, 0] ++ selfFs)) ω₂ = some ([], ω₃)) :
    XRuns p (oracles H (Damp.Exec.liftWitness w)) (mergeCoinImmediate a b) s st (ac = bc ∧ av.val + bv.val < 2 ^ 128)
      (fun r e w' l => Value.Is p e r (derivedNonceFs p "midnight:kernel:nonce_evolve" an ++ ac ++
          [Fr.ofNat (av.val + bv.val)]) ∧ w' = ω₃ ∧
        l = { st.ledger with effects := .array (mergeEffects es m0 m1 m2 xa xb y) }) :=
  mergeCoin_runs H p w a { nonce := b.nonce, color := b.color, value := b.value, mt_index := 0 } hg an ac bn bc av ai
    bv 0 hanl hacl hbcl hav hbv ha
    (hb.imp fun e h => ⟨h.nonce, h.color, h.value, by
      show (Uint.capped 18446744073709551615 (.const 0)).eval p e = some 0
      rw [Uint.capped_eval uint64_bound]; rfl⟩)
    cfs wa selfFs hctx hc0 hself hwf es m0 m1 m2 heff hm0 hm1 hm2 nfa nfb xa xb hnfa hxa hnfb hxb cm y hcm hy
    ω₁ ω₂ ω₃ hw₁ hw₂ hw₃

/-- The effects after `mintShieldedToken` with the guard on: `dk`'s mint
    (slot 4), the coin's commitment `y` claimed as spent (slot 2), and as
    received (slot 1) when the recipient is this contract. -/
def mintSEffects (es : List SV) (m1 m2 m4 : List (AV × SV)) (dk : AV) (a y : Nat) (self : Bool) : List SV :=
  if self then ((es.set 4 (addMap 4 m4 dk a)).set 2 (.map (assocSet (hkey y) .null m2))).set 1
    (.map (assocSet (hkey y) .null m1))
  else (es.set 4 (addMap 4 m4 dk a)).set 2 (.map (assocSet (hkey y) .null m2))

/-- **`mintShieldedToken domainSep value nonce recipient`**, under a guard that
    holds: `domainSep` meaning `dsFs` (the atom `d`), `value` meaning
    `a < 2^64`, `nonce` meaning `nFs` (two limbs), `recipient` meaning
    `Fr.ofBool u :: rl ++ rr` (a user key `rl` when `u`, a contract `rr`
    otherwise); the context's address `selfFs`. Whatever the hashes give: the
    token type (`tokenTypePre`) is `ts`, and the commitment of the new coin
    `(nFs, ts, a)` to the recipient is the atom `y`. The built-in witness is
    asked to create the output (answer: nothing, private state `ω₁`). The call
    completes exactly when the mint of `d` fits (`addOk`); it returns the coin,
    leaves the private state `ω₁`, and changes only the effects
    (`mintSEffects`: slot 1 too exactly when `recipient` is this contract). -/
theorem mintShieldedToken_runs (domainSep : Bytes 32) (value : Uint64) (nonce : Bytes 32)
    (recipient : Either ZswapCoinPublicKey ContractAddress) {s : Build} {st : Exec.State ω LedgerState}
    (hg : GuardIs p s st.runState true)
    (dsFs : List Fr) (hds : Stable s.next st.env (fun e => Value.Is p e domainSep dsFs))
    (d : Nat) (hd : AV.ofFields [.bytes 32] dsFs = some (hkey d))
    (a : Fr) (ha : Stable s.next st.env (fun e => value.expr.eval p e = some a)) (ha64 : a.val < 2 ^ 64)
    (nFs : List Fr) (hnl : nonce.limbs.length = 2) (hn : Stable s.next st.env (fun e => Value.Is p e nonce nFs))
    (u : Bool) (rl rr : List Fr) (hrl : rl.length = 2) (hrr : rr.length = 2)
    (hsh : (Value.toExprs recipient.left).length = 2 ∧ (Value.toExprs recipient.right).length = 2)
    (hr : Stable s.next st.env (fun e => Value.Is p e recipient (Fr.ofBool u :: rl ++ rr)))
    (cfs : List SV) (wa : AV) (selfFs : List Fr) (hctx : st.ledger.context = .array cfs)
    (hc0 : cfs[0]? = some (.cell wa)) (hself : fieldsOf [.bytes 32] wa.atoms = some selfFs) (hwf : st.ledger.WF)
    (es : List SV) (m1 m2 m4 : List (AV × SV)) (heff : st.ledger.effects = .array es)
    (hm1 : es[1]? = some (.map m1)) (hm2 : es[2]? = some (.map m2)) (hm4 : es[4]? = some (.map m4))
    (ts : List Fr) (htt : phashFs p tokenTypeAlign (tokenTypePre dsFs selfFs) = some ts)
    (cm : List Fr) (y : Nat) (hcm : phashFs p coinPreimageAlign (ccPre (nFs ++ ts ++ [a]) u rl rr) = some cm)
    (hy : AV.ofFields [.bytes 32] cm = some (hkey y))
    (ω₁ : ω) (hw₁ : w "createZswapOutput" ((nFs ++ ts ++ [a]) ++ (Fr.ofBool u :: rl ++ rr)) st.private_ =
      some ([], ω₁)) :
    XRuns p (oracles H (Damp.Exec.liftWitness w)) (mintShieldedToken domainSep value nonce recipient) s st (addOk m4 (hkey d) a.val)
      (fun r e w' l => Value.Is p e r (nFs ++ ts ++ [a]) ∧ w' = ω₁ ∧
        l = { st.ledger with effects := .array (mintSEffects es m1 m2 m4 (hkey d) a.val y
          (!u && decide (rr = selfFs))) }) := by
  have hsl := fieldsOf_bytes32_length hself
  have htl := phashFs_length htt
  let σ := st.ledger
  let es₁ := es.set 4 (addMap 4 m4 (hkey d) a.val)
  let es₂ := es₁.set 2 (.map (assocSet (hkey y) .null m2))
  let es₃ := es₂.set 1 (.map (assocSet (hkey y) .null m1))
  let L : List SV → LedgerState := fun es' => { σ with effects := .array es' }
  let cbv := !u && decide (rr = selfFs)
  have hm2₁ : es₁[2]? = some (.map m2) := by simp [es₁, List.getElem?_set_ne, hm2]
  have hm1₂ : es₂[1]? = some (.map m1) := by simp [es₂, es₁, List.getElem?_set_ne, hm1]
  have hreq₁ : ∀ e, Agree s.next st.env e → ∃ req,
      (emitted (Kernel.mintShielded domainSep value)).bind (Exec.request p e) = some req ∧
      (oracles H (Damp.Exec.liftWitness w)).ledger req st.ledger = if addOk m4 (hkey d) a.val then some ([], L es₁) else none := fun e he =>
    Kernel.mintShielded_spec H p e st.ledger es m4 domainSep value dsFs (hkey d) a hwf heff hm4 (hds e he) hd (ha e he)
      ha64
  unfold mintShieldedToken
  -- 1. `kernel.self()`
  refine (XRuns.seq (ok₂ := addOk m4 (hkey d) a.val) (self_runs H p w hg cfs wa selfFs hctx hc0 hself hwf)
    (fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind Grows.currentGuard fun _ => Grows.bind (Grows.nameGuard _) fun _ => Grows.bind (Grows.underGuard _ (Grows.ledgerRead _ _)) fun _ => Grows.bind (Grows.when_ _ (Grows.ledgerOp _ _)) fun _ => Grows.pure' _)
    fun x s₁ st₁ hn₁ hgd₁ ha₁ hQ₁ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hP₁, hL₁, -, -⟩ := hQ₁.holds
  have hg₁ := GuardIs.later hg ha₁ hn₁ hgd₁
  have hcoinE : Stable s₁.next st₁.env (fun e => Value.Is p e
      ({ nonce, color := tokenType domainSep x, value := (value.widen : Uint128) } : ShieldedCoinInfo) (nFs ++ ts ++ [a])) := by
    intro e he
    have hA : Agree s.next st.env e := ha₁.trans (he.mono hn₁)
    unfold Value.Is
    show Expr.evalList p e (nonce.limbs ++ ((tokenType domainSep x).limbs ++ ([(value.widen : Uint128).expr] ++ []))) = _
    rw [show nFs ++ ts ++ [a] = nFs ++ (ts ++ [a]) by simp]
    exact evalList_append_some (hn e hA) (evalList_append_some
      (tokenType_is (hds e hA) (hQ₁ e he).2.2.1 htt)
      (by simp [Expr.evalList, widen_eval p value uint128_bound (by decide) e, ha e hA]))
  -- 2. `const coin := …`
  have hlen : (Value.toExprs ({ nonce, color := tokenType domainSep x, value := (value.widen : Uint128) } : ShieldedCoinInfo)).length =
      Value.width ShieldedCoinInfo := by
    rw [Value.width_coin]
    show (nonce.limbs ++ ((tokenType domainSep x).limbs ++ ([(value.widen : Uint128).expr] ++ []))).length = 5
    simp [hnl]; rfl
  refine (XRuns.seq (ok₂ := addOk m4 (hkey d) a.val)
    (XRuns.val (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (s := s₁) (st := st₁) roundTrip_coin "coin" hlen hcoinE)
    (fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind Grows.currentGuard fun _ => Grows.bind (Grows.nameGuard _) fun _ => Grows.bind (Grows.underGuard _ (Grows.ledgerRead _ _)) fun _ => Grows.bind (Grows.when_ _ (Grows.ledgerOp _ _)) fun _ => Grows.pure' _)
    fun coin s₂ st₂ hn₂ hgd₂ ha₂ hQ₂ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨-, hP₂, hL₂⟩ := hQ₂.holds
  have hC₂ : Stable s₂.next st₂.env (fun e => Value.Is p e coin (nFs ++ ts ++ [a])) := hQ₂.imp fun e h => h.1
  have hg₂ := GuardIs.later hg₁ ha₂ hn₂ hgd₂
  have hA₂ : Agree s.next st.env st₂.env := ha₁.trans (ha₂.mono hn₁)
  have hn₀₂ : s.next ≤ s₂.next := Nat.le_trans hn₁ hn₂
  -- 3. `Kernel.mintShielded domainSep value`
  refine (XRuns.seq (ok₂ := True)
    (XRuns.condOp (p := p) (O := oracles H (Damp.Exec.liftWitness w)) rfl (by simp) hg₂ fun e he => by
      rw [hL₂, hL₁]; exact hreq₁ e (hA₂.trans (he.mono hn₀₂)))
    (fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind Grows.currentGuard fun _ => Grows.bind (Grows.nameGuard _) fun _ => Grows.bind (Grows.underGuard _ (Grows.ledgerRead _ _)) fun _ => Grows.bind (Grows.when_ _ (Grows.ledgerOp _ _)) fun _ => Grows.pure' _)
    fun _ s₃ st₃ hn₃ hgd₃ ha₃ hQ₃ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hP₃, hok₃, hL₃⟩ := hQ₃.holds
  simp only [ite_true, forall_const] at hL₃ hok₃
  have hwf₁ : (L es₁).WF := by
    obtain ⟨req, -, hq⟩ := hreq₁ st.env (Agree.refl _ _)
    simp only [hok₃, ite_true] at hq
    exact ledgerOracle_wf hq
  have hg₃ := GuardIs.later hg₂ ha₃ hn₃ hgd₃
  have hA₃ : Agree s.next st.env st₃.env := hA₂.trans (ha₃.mono hn₀₂)
  have hn₀₃ : s.next ≤ s₃.next := Nat.le_trans hn₀₂ hn₃
  have hC₃ := hC₂.later ha₃ hn₃
  have hR₃ := hr.later hA₃ hn₀₃
  -- 4. `createZswapOutput coin recipient`
  refine (XRuns.seq (ok₂ := True)
    ((XRuns.askWitness0_iso (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (α := Unit) rfl rfl "createZswapOutput" hg₃
      (evalList_append_some hC₃.holds hR₃.holds)).conseq
      (ok' := True) ⟨fun _ => trivial, fun _ => ⟨ω₁, by rw [hP₃, hP₂, hP₁]; exact hw₁⟩⟩
      (Q' := fun _ _ w' l => l = st₃.ledger ∧ w' = ω₁) fun _ _ w' l h => ⟨h.1, by
        have h2 := h.2; rw [hP₃, hP₂, hP₁] at h2; change w _ _ _ = _ at h2; rw [hw₁] at h2; simp at h2
        exact h2.symm⟩)
    (fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind Grows.currentGuard fun _ => Grows.bind (Grows.nameGuard _) fun _ => Grows.bind (Grows.underGuard _ (Grows.ledgerRead _ _)) fun _ => Grows.bind (Grows.when_ _ (Grows.ledgerOp _ _)) fun _ => Grows.pure' _)
    fun _ s₄ st₄ hn₄ hgd₄ ha₄ hQ₄ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hL₄, hP₄⟩ := hQ₄.holds
  have hg₄ := GuardIs.later hg₃ ha₄ hn₄ hgd₄
  have hC₄ := hC₃.later ha₄ hn₄
  have hR₄ := hR₃.later ha₄ hn₄
  have hparts : ∀ e, Value.Is p e recipient (Fr.ofBool u :: rl ++ rr) →
      recipient.isLeft.expr.eval p e = some (Fr.ofBool u) ∧ Value.Is p e recipient.left rl ∧
        Value.Is p e recipient.right rr := fun e h => either_is (by rw [hsh.1, hrl]) h
  -- 5. `const notLeft := !. recipient.isLeft`
  refine (XRuns.seq (ok₂ := True)
    (XRuns.lift (O := oracles H (Damp.Exec.liftWitness w)) (st := st₄) (Runs.val_boolean (p := p) (st := st₄.runState) (u := !u) "notLeft"
      (hR₄.imp fun e h => Boolean.not_is (hparts e h).1)) (Quiet.val _ _))
    (fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind Grows.currentGuard fun _ => Grows.bind (Grows.nameGuard _) fun _ => Grows.bind (Grows.underGuard _ (Grows.ledgerRead _ _)) fun _ => Grows.bind (Grows.when_ _ (Grows.ledgerOp _ _)) fun _ => Grows.pure' _)
    fun notLeft s₅ st₅ hn₅ hgd₅ ha₅ hQ₅ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨-, hP₅, hL₅⟩ := hQ₅.holds
  have hNL₅ : Stable s₅.next st₅.env (fun e => Boolean.Is p e notLeft (!u)) := hQ₅.imp fun e h => h.1
  have hg₅ := GuardIs.later hg₄ ha₅ hn₅ hgd₅
  have hC₅ := hC₄.later ha₅ hn₅
  have hR₅ := hR₄.later ha₅ hn₅
  -- 6. `const cm := coinCommitment coin recipient`
  refine (XRuns.seq (ok₂ := True)
    (XRuns.val (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (s := s₅) (st := st₅) roundTrip_bytes (xs := cm) "cm" rfl
      fun e he => coinCommitment_is (hC₅ e he) hsh hrl (hR₅ e he) hcm)
    (fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind Grows.currentGuard fun _ => Grows.bind (Grows.nameGuard _) fun _ => Grows.bind (Grows.underGuard _ (Grows.ledgerRead _ _)) fun _ => Grows.bind (Grows.when_ _ (Grows.ledgerOp _ _)) fun _ => Grows.pure' _)
    fun cmv s₆ st₆ hn₆ hgd₆ ha₆ hQ₆ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨-, hP₆, hL₆⟩ := hQ₆.holds
  have hCM₆ : Stable s₆.next st₆.env (fun e => Value.Is p e cmv cm) := hQ₆.imp fun e h => h.1
  have hg₆ := GuardIs.later hg₅ ha₆ hn₆ hgd₆
  have hLs₆ : st₆.ledger = L es₁ := by rw [hL₆, hL₅, hL₄, hL₃]
  -- 7. `Kernel.claimZswapCoinSpend cm`
  have hwf₂ : (L es₂).WF := claimed_wf H (σ := L es₁) (by decide) hy hwf₁ rfl hm2₁
  refine (XRuns.seq (ok₂ := True)
    (XRuns.someOp (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (σ₁ := L es₂) rfl (by simp) hg₆ fun e he => by
      rw [hLs₆]
      exact Kernel.claimZswapCoinSpend_spec H p e (L es₁) es₁ m2 cmv cm (hkey y) hwf₁ rfl hm2₁ (hCM₆ e he) hy)
    (fun _ => Grows.bind Grows.currentGuard fun _ => Grows.bind (Grows.nameGuard _) fun _ => Grows.bind (Grows.underGuard _ (Grows.ledgerRead _ _)) fun _ => Grows.bind (Grows.when_ _ (Grows.ledgerOp _ _)) fun _ => Grows.pure' _)
    fun _ s₇ st₇ hn₇ hgd₇ ha₇ hQ₇ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hP₇, hL₇⟩ := hQ₇.holds
  simp only [ite_true] at hL₇
  have hg₇ := GuardIs.later hg₆ ha₇ hn₇ hgd₇
  -- 8. `currentGuard`, `nameGuard (guardAnd g notLeft)`, `underGuard g' Kernel.self`
  refine (XRuns.seq (ok₂ := True)
    (XRuns.lift (O := oracles H (Damp.Exec.liftWitness w)) (st := st₇) (Runs.currentGuard (p := p) (s := s₇) (st := st₇.runState))
      Quiet.currentGuard)
    (fun _ => Grows.bind (Grows.nameGuard _) fun _ => Grows.bind (Grows.underGuard _ (Grows.ledgerRead _ _)) fun _ => Grows.bind (Grows.when_ _ (Grows.ledgerOp _ _)) fun _ => Grows.pure' _)
    fun g s₈ st₈ hn₈ hgd₈ ha₈ hQ₈ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hgg, hP₈, hL₈⟩ := hQ₈.holds
  have hg₈ := GuardIs.later hg₇ ha₈ hn₈ hgd₈
  have hNL₈ := (hNL₅.later ha₆ hn₆ |>.later ha₇ hn₇).later ha₈ hn₈
  have hgv : Stable s₈.next st₈.env (fun e => (guardAnd g notLeft.expr).eval p e = some (Fr.ofBool (true && !u))) :=
    fun e he => guardAnd_eval (by rw [hgg, ← hgd₈]; exact hg₈ e he) (hNL₈ e he)
  refine (XRuns.seq (ok₂ := True)
    (XRuns.lift (O := oracles H (Damp.Exec.liftWitness w)) (st := st₈) (Runs.nameGuard (p := p) (st := st₈.runState) hgv) (Quiet.nameGuard _))
    (fun _ => Grows.bind (Grows.underGuard _ (Grows.ledgerRead _ _)) fun _ => Grows.bind (Grows.when_ _ (Grows.ledgerOp _ _)) fun _ => Grows.pure' _)
    fun g' s₉ st₉ hn₉ hgd₉ ha₉ hQ₉ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨-, hP₉, hL₉⟩ := hQ₉.holds
  have hLs₉ : st₉.ledger = L es₂ := by rw [hL₉, hL₈, hL₇]
  have hgu : GuardIs p { s₉ with guard := g' } st₉.runState (!u) := fun e he => by
    have := hQ₉ e he; exact this.1
  refine (XRuns.seq (ok₂ := True)
    (XRuns.underGuard (self_runs H p w hgu cfs wa selfFs (by rw [hLs₉]; exact hctx) hc0 hself
      (by rw [hLs₉]; exact hwf₂)))
    (fun _ => Grows.bind (Grows.when_ _ (Grows.ledgerOp _ _)) fun _ => Grows.pure' _)
    fun me s₁₀ st₁₀ hn₁₀ hgd₁₀ ha₁₀ hQ₁₀ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hP₁₀, hL₁₀, -, -⟩ := hQ₁₀.holds
  have hg₁₀ := GuardIs.later (GuardIs.later hg₈ ha₉ hn₉ hgd₉) ha₁₀ hn₁₀ hgd₁₀
  have hR₁₀ := ((((hR₅.later ha₆ hn₆).later ha₇ hn₇).later ha₈ hn₈).later ha₉ hn₉).later ha₁₀ hn₁₀
  have hcond : Stable s₁₀.next st₁₀.env (fun e => Boolean.Is p e
      (!. recipient.isLeft &&. (recipient.right.bytes ==. me.bytes)) cbv) := by
    intro e he
    have hp := hparts e (hR₁₀ e he)
    have hme := (hQ₁₀ e he).2.2.1
    have heq : Boolean.Is p e (recipient.right.bytes ==. me.bytes) (decide (rr = selfOr (!u) selfFs)) :=
      valueEq_is (p := p) hp.2.2 hme (by rw [hrr, selfOr_length hsl])
    have := Boolean.and_is (Boolean.not_is (show Boolean.Is p e recipient.isLeft u from hp.1)) heq
    cases u <;> simpa [cbv, selfOr] using this
  have hCM₁₀ := ((((hCM₆.later ha₇ hn₇).later ha₈ hn₈).later ha₉ hn₉).later ha₁₀ hn₁₀)
  have hLs₁₀ : st₁₀.ledger = L es₂ := by rw [hL₁₀, hLs₉]
  -- 9. `if% … then Kernel.claimZswapCoinReceive cm`
  have hwf₂' := hwf₂
  refine (XRuns.seq (ok₂ := True)
    (XRuns.when_someOp (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (cb := cbv) (σ₁ := L es₃) rfl (by simp) hg₁₀ hcond fun e he => by
      rw [hLs₁₀]
      exact Kernel.claimZswapCoinReceive_spec H p e (L es₂) es₂ m1 cmv cm (hkey y) hwf₂' rfl hm1₂ (hCM₁₀ e he) hy)
    (fun _ => Grows.pure' _)
    fun _ s₁₁ st₁₁ hn₁₁ hgd₁₁ ha₁₁ hQ₁₁ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hP₁₁, hL₁₁⟩ := hQ₁₁.holds
  refine XRuns.pure fun e he => ⟨?_, ?_, ?_⟩
  · exact ((((((((hC₅.later ha₆ hn₆).later ha₇ hn₇).later ha₈ hn₈).later ha₉ hn₉).later ha₁₀ hn₁₀).later ha₁₁
      hn₁₁)) e he)
  · rw [hP₁₁, hP₁₀, hP₉, hP₈, hP₇, hP₆, hP₅, hP₄]
  · rw [hL₁₁, hLs₁₀]
    cases hc : cbv with
    | true => simp [hc, L, es₃, es₂, es₁, mintSEffects, σ, cbv] at hc ⊢
    | false => simp [hc, L, es₂, es₁, mintSEffects, σ, cbv] at hc ⊢

/-- The effects after `sendShielded` with the guard on: the input's nullifier
    `x` (slot 0), the sent coin's commitment `y` claimed as spent (2) and, when
    sent to this contract, received (1); and with change, its commitment `z`
    in both. -/
def sendSEffects (es : List SV) (m0 m1 m2 : List (AV × SV)) (x y z : Nat) (selfR hasChange : Bool) : List SV :=
  let es₈ := (es.set 0 (.map (assocSet (hkey x) .null m0))).set 2 (.map (assocSet (hkey y) .null m2))
  let m1' := if selfR then assocSet (hkey y) .null m1 else m1
  let es₉ := if selfR then es₈.set 1 (.map m1') else es₈
  if hasChange then (es₉.set 2 (.map (assocSet (hkey z) .null (assocSet (hkey y) .null m2)))).set 1
    (.map (assocSet (hkey z) .null m1'))
  else es₉

/-- **`sendShielded input recipient value`**, under a guard that holds. The
    input coin's parts mean `n, c, v, i` (`v < 2^128`), `value` means `k`, the
    recipient `Fr.ofBool u :: rl ++ rr`, the address `selfFs`. Whatever the
    hashes give: the input's nullifier is `x`; the sent coin is
    `outFs = (nonce evolved from n, c, k)`, its commitment to the recipient `y`;
    the change `v - k` is the coin `chFs = (nonce evolved under ".../2", c, v - k)`,
    its commitment to this contract `z`. The built-in witness spends the input
    (`ω₁`), creates the sent coin (`ω₂`) and, if `v - k ≠ 0`, the change (`ω₃`).
    The call completes exactly when `k ≤ v`; the result is `(none, outFs)` when
    there is no change and `(some chFs, outFs)` otherwise; and only the effects
    change (`sendSEffects`). -/
theorem sendShielded_runs (input : QualifiedShieldedCoinInfo) (recipient : Either ZswapCoinPublicKey ContractAddress)
    (value : Uint128) {s : Build} {st : Exec.State ω LedgerState} (hg : GuardIs p s st.runState true)
    (n c : List Fr) (v i : Fr) (hnl : input.nonce.limbs.length = 2) (hcl : c.length = 2) (hv : v.val < 2 ^ 128)
    (hin : Stable s.next st.env (fun e => QCoinIs p e input n c v i))
    (k : Nat) (hk : Stable s.next st.env (fun e => Uint.Means p e value k))
    (u : Bool) (rl rr : List Fr) (hrl : rl.length = 2) (hrr : rr.length = 2)
    (hsh : (Value.toExprs recipient.left).length = 2 ∧ (Value.toExprs recipient.right).length = 2)
    (hr : Stable s.next st.env (fun e => Value.Is p e recipient (Fr.ofBool u :: rl ++ rr)))
    (cfs : List SV) (wa : AV) (selfFs : List Fr) (hctx : st.ledger.context = .array cfs)
    (hc0 : cfs[0]? = some (.cell wa)) (hself : fieldsOf [.bytes 32] wa.atoms = some selfFs) (hwf : st.ledger.WF)
    (es : List SV) (m0 m1 m2 : List (AV × SV)) (heff : st.ledger.effects = .array es)
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
    (hw₁ : w "createZswapInput" (n ++ c ++ [v, i]) st.private_ = some ([], ω₁))
    (hw₂ : w "createZswapOutput" ((derivedNonceFs p "midnight:kernel:nonce_evolve" n ++ c ++ [Fr.ofNat k]) ++
      (Fr.ofBool u :: rl ++ rr)) ω₁ = some ([], ω₂))
    (hw₃ : v.val - k ≠ 0 → w "createZswapOutput" ((derivedNonceFs p "midnight:kernel:nonce_evolve/2" n ++ c ++
      [Fr.ofNat (v.val - k)]) ++ (Fr.ofBool false :: [0, 0] ++ selfFs)) ω₂ = some ([], ω₃)) :
    XRuns p (oracles H (Damp.Exec.liftWitness w)) (sendShielded input recipient value) s st (k ≤ v.val)
      (fun r e w' l => Value.Is p e r (if v.val - k = 0
          then (Fr.ofBool false :: List.replicate (Value.width ShieldedCoinInfo) 0) ++
            (derivedNonceFs p "midnight:kernel:nonce_evolve" n ++ c ++ [Fr.ofNat k])
          else (Fr.ofBool true :: (derivedNonceFs p "midnight:kernel:nonce_evolve/2" n ++ c ++
            [Fr.ofNat (v.val - k)])) ++ (derivedNonceFs p "midnight:kernel:nonce_evolve" n ++ c ++ [Fr.ofNat k])) ∧
        w' = (if v.val - k = 0 then ω₂ else ω₃) ∧
        l = { st.ledger with effects := .array (sendSEffects es m0 m1 m2 x y z (!u && decide (rr = selfFs))
          (!decide (v.val - k = 0))) }) := by
  have hsl := fieldsOf_bytes32_length hself
  let σ := st.ledger
  let outFs := derivedNonceFs p "midnight:kernel:nonce_evolve" n ++ c ++ [Fr.ofNat k]
  let chg := v.val - k
  let chFs := derivedNonceFs p "midnight:kernel:nonce_evolve/2" n ++ c ++ [Fr.ofNat chg]
  let selfR := !u && decide (rr = selfFs)
  let L : List SV → LedgerState := fun es' => { σ with effects := .array es' }
  let es₁ := es.set 0 (.map (assocSet (hkey x) .null m0))
  let es₈ := es₁.set 2 (.map (assocSet (hkey y) .null m2))
  let m1' := if selfR then assocSet (hkey y) .null m1 else m1
  let es₉ := if selfR then es₈.set 1 (.map m1') else es₈
  let esA := es₉.set 2 (.map (assocSet (hkey z) .null (assocSet (hkey y) .null m2)))
  let esB := esA.set 1 (.map (assocSet (hkey z) .null m1'))
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
  -- 1. `const selfAddr ← Kernel.self`
  have h1 : XRuns p (oracles H (Damp.Exec.liftWitness w)) (valM Kernel.self "selfAddr") s st True
      (fun r e w' l => Value.Is p e r selfFs ∧ w' = st.private_ ∧ l = σ ∧ Value.Shaped r) := by
    unfold valM
    refine (XRuns.seq (ok₂ := True) (self_runs H p w hg cfs wa selfFs hctx hc0 hself hwf)
      (fun _ => Grows.val _ _) fun x s₁ st₁ hn₁ hgd₁ ha₁ hQ₁ => ?_).conseq (by simp) fun _ _ _ _ h => h
    obtain ⟨hw₁, hl₁, -, hsh₁⟩ := hQ₁.holds
    have hlen : (Value.toExprs x).length = Value.width ContractAddress := ContractAddress.shaped_len hsh₁
    exact ((XRuns.val (p := p) (O := oracles H (Damp.Exec.liftWitness w)) roundTrip_contractAddress "selfAddr" hlen
      (hQ₁.imp fun e h => h.2.2.1)).addResult (val_shaped x "selfAddr" s₁ hlen)).conseq Iff.rfl
      fun r e w' l h => ⟨h.1.1, h.1.2.1.trans hw₁, h.1.2.2.trans hl₁, h.2⟩
  unfold sendShielded
  refine (XRuns.seq (ok₂ := k ≤ v.val) h1
    (fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.valM (Grows.sub _ _) _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.when_ _ (Grows.ledgerOp _ _)) fun _ => Grows.cond _ (Grows.pure' _) (Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _))
    fun selfAddr s₁ st₁ hn₁ hgd₁ ha₁ hQ₁ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨-, hP₁, hL₁, hshS⟩ := hQ₁.holds
  have hS₁ : Stable s₁.next st₁.env (fun e => Value.Is p e selfAddr selfFs) := hQ₁.imp fun e h => h.1
  have hg₁ := GuardIs.later hg ha₁ hn₁ hgd₁
  have hin₁ := hin.later ha₁ hn₁
  -- 2. `createZswapInput input`
  refine (XRuns.seq (ok₂ := k ≤ v.val)
    ((XRuns.askWitness0_iso (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (α := Unit) rfl rfl "createZswapInput" hg₁ hin₁.holds.is).conseq
      (ok' := True) ⟨fun _ => trivial, fun _ => ⟨ω₁, by rw [hP₁]; exact hw₁⟩⟩
      (Q' := fun _ _ w' l => l = st₁.ledger ∧ w' = ω₁) fun _ _ w' l h => ⟨h.1, by
        have h2 := h.2; rw [hP₁] at h2; change w _ _ _ = _ at h2; rw [hw₁] at h2; simp at h2; exact h2.symm⟩)
    (fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.valM (Grows.sub _ _) _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.when_ _ (Grows.ledgerOp _ _)) fun _ => Grows.cond _ (Grows.pure' _) (Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _))
    fun _ s₂ st₂ hn₂ hgd₂ ha₂ hQ₂ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hL₂, hP₂⟩ := hQ₂.holds
  have hg₂ := GuardIs.later hg₁ ha₂ hn₂ hgd₂
  have hS₂ := hS₁.later ha₂ hn₂
  have hin₂ := hin₁.later ha₂ hn₂
  -- 3. `claimZswapNullifier (coinNullifier input selfAddr)`
  refine (XRuns.seq (ok₂ := k ≤ v.val)
    (XRuns.someOp (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (σ₁ := L es₁) rfl (by simp) hg₂ fun e he => by
      rw [hL₂, hL₁]
      exact Kernel.claimZswapNullifier_spec H p e σ es m0 _ nf (hkey x) hwf heff hm0
        (coinNullifier_is (hin₂ e he).down (hS₂ e he) hnf) hx)
    (fun _ => Grows.bind (Grows.valM (Grows.sub _ _) _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.when_ _ (Grows.ledgerOp _ _)) fun _ => Grows.cond _ (Grows.pure' _) (Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _))
    fun _ s₃ st₃ hn₃ hgd₃ ha₃ hQ₃ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hP₃, hL₃⟩ := hQ₃.holds
  simp only [ite_true] at hL₃
  have hg₃ := GuardIs.later hg₂ ha₃ hn₃ hgd₃
  have hA₃ : Agree s.next st.env st₃.env := ha₁.trans ((ha₂.mono hn₁).trans (ha₃.mono (Nat.le_trans hn₁ hn₂)))
  have hn₀₃ : s.next ≤ s₃.next := Nat.le_trans hn₁ (Nat.le_trans hn₂ hn₃)
  have hin₃ := hin₂.later ha₃ hn₃
  have hk₃ := hk.later hA₃ hn₀₃
  -- 4. `const change ← input.value.sub value`
  have h4 : XRuns p (oracles H (Damp.Exec.liftWitness w)) (valM (input.value.sub value) "change") s₃ st₃ (k ≤ v.val)
      (fun r e w' l => Uint.Means p e r chg ∧ w' = st₃.private_ ∧ l = st₃.ledger) := by
    unfold valM
    refine (XRuns.seq (ok₂ := True)
      (XRuns.lift (O := oracles H (Damp.Exec.liftWitness w)) (st := st₃) (Runs.sub (p := p) (st := st₃.runState) hg₃
        (fun e he => uint128_means p (hin₃ e he).value hv) hk₃) (Quiet.sub _ _))
      (fun _ => Grows.val _ _) fun d s₄ st₄ hn₄ hgd₄ ha₄ hQ₄ => ?_).conseq (by simp) fun _ _ _ _ h => h
    obtain ⟨-, hP₄, hL₄⟩ := hQ₄.holds
    exact (XRuns.lift (O := oracles H (Damp.Exec.liftWitness w)) (st := st₄) (Runs.val_uint (p := p) (st := st₄.runState) "change"
      (hQ₄.imp fun e h => by simpa using h.1)) (Quiet.val _ _)).conseq Iff.rfl
      fun r e w' l h => ⟨h.1, h.2.1.trans hP₄, h.2.2.trans hL₄⟩
  refine (XRuns.seq (ok₂ := True) h4
    (fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.when_ _ (Grows.ledgerOp _ _)) fun _ => Grows.cond _ (Grows.pure' _) (Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _))
    fun change s₄ st₄ hn₄ hgd₄ ha₄ hQ₄ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨-, hP₄, hL₄⟩ := hQ₄.holds
  have hCh₄ : Stable s₄.next st₄.env (fun e => Uint.Means p e change chg) := hQ₄.imp fun e h => h.1
  have hg₄ := GuardIs.later hg₃ ha₄ hn₄ hgd₄
  have hin₄ := hin₃.later ha₄ hn₄
  have hk₄ := hk₃.later ha₄ hn₄
  -- 5. `const output := { nonce := …, color := input.color, value }`
  have hout : Stable s₄.next st₄.env (fun e => Value.Is p e
      ({ nonce := upgradeFromTransient (transientHash (#v[Field.ofString "midnight:kernel:nonce_evolve",
          degradeToTransient input.nonce] : Vector Field 2)), color := input.color, value } : ShieldedCoinInfo)
      outFs) := by
    intro e he
    unfold Value.Is
    show Expr.evalList p e (_ ++ (input.color.limbs ++ ([value.expr] ++ []))) = _
    rw [show outFs = derivedNonceFs p "midnight:kernel:nonce_evolve" n ++ (c ++ [Fr.ofNat k]) by simp [outFs]]
    exact evalList_append_some (derivedNonce_is "midnight:kernel:nonce_evolve" hnl (hin₄ e he).nonce)
      (evalList_append_some (hin₄ e he).color (by simp [Expr.evalList, (hk₄ e he).eval]))
  refine (XRuns.seq (ok₂ := True)
    ((XRuns.val (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (s := s₄) (st := st₄) roundTrip_coin (xs := outFs) "output"
      (by rw [← Damp.evalList_length hout.holds]; simp [outFs, derivedNonceFs, hcl]; rfl) hout).addResult
      (val_shaped _ "output" s₄ (by rw [← Damp.evalList_length hout.holds]; simp [outFs, derivedNonceFs, hcl]; rfl)))
    (fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.when_ _ (Grows.ledgerOp _ _)) fun _ => Grows.cond _ (Grows.pure' _) (Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _))
    fun output s₅ st₅ hn₅ hgd₅ ha₅ hQ₅ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨⟨-, hP₅, hL₅⟩, hshO⟩ := hQ₅.holds
  have hO₅ : Stable s₅.next st₅.env (fun e => Value.Is p e output outFs) := hQ₅.imp fun e h => h.1.1
  have hg₅ := GuardIs.later hg₄ ha₅ hn₅ hgd₅
  have hA₅ : Agree s.next st.env st₅.env := hA₃.trans ((ha₄.mono hn₀₃).trans (ha₅.mono (Nat.le_trans hn₀₃ hn₄)))
  have hn₀₅ : s.next ≤ s₅.next := Nat.le_trans hn₀₃ (Nat.le_trans hn₄ hn₅)
  have hR₅ := hr.later hA₅ hn₀₅
  -- 6. `createZswapOutput output recipient`
  refine (XRuns.seq (ok₂ := True)
    ((XRuns.askWitness0_iso (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (α := Unit) rfl rfl "createZswapOutput" hg₅
      (evalList_append_some hO₅.holds hR₅.holds)).conseq
      (ok' := True) ⟨fun _ => trivial, fun _ => ⟨ω₂, by rw [hP₅, hP₄, hP₃, hP₂]; exact hw₂⟩⟩
      (Q' := fun _ _ w' l => l = st₅.ledger ∧ w' = ω₂) fun _ _ w' l h => ⟨h.1, by
        have h2 := h.2; rw [hP₅, hP₄, hP₃, hP₂] at h2; change w _ _ _ = _ at h2; rw [hw₂] at h2; simp at h2
        exact h2.symm⟩)
    (fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.when_ _ (Grows.ledgerOp _ _)) fun _ => Grows.cond _ (Grows.pure' _) (Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _))
    fun _ s₆ st₆ hn₆ hgd₆ ha₆ hQ₆ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hL₆, hP₆⟩ := hQ₆.holds
  have hg₆ := GuardIs.later hg₅ ha₆ hn₆ hgd₆
  have hO₆ := hO₅.later ha₆ hn₆
  have hR₆ := hR₅.later ha₆ hn₆
  -- 7. `const cm := coinCommitment output recipient`
  refine (XRuns.seq (ok₂ := True)
    (XRuns.val (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (s := s₆) (st := st₆) roundTrip_bytes (xs := cm) "cm" rfl
      fun e he => coinCommitment_is (hO₆ e he) hsh hrl (hR₆ e he) hcm)
    (fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.when_ _ (Grows.ledgerOp _ _)) fun _ => Grows.cond _ (Grows.pure' _) (Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _))
    fun cmv s₇ st₇ hn₇ hgd₇ ha₇ hQ₇ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨-, hP₇, hL₇⟩ := hQ₇.holds
  have hCM₇ : Stable s₇.next st₇.env (fun e => Value.Is p e cmv cm) := hQ₇.imp fun e h => h.1
  have hg₇ := GuardIs.later hg₆ ha₇ hn₇ hgd₇
  have hLs₇ : st₇.ledger = L es₁ := by rw [hL₇, hL₆, hL₅, hL₄, hL₃]
  -- 8. `Kernel.claimZswapCoinSpend cm`
  refine (XRuns.seq (ok₂ := True)
    (XRuns.someOp (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (σ₁ := L es₈) rfl (by simp) hg₇ fun e he => by
      rw [hLs₇]
      exact Kernel.claimZswapCoinSpend_spec H p e (L es₁) es₁ m2 cmv cm (hkey y) hwf₁ rfl hm2₁ (hCM₇ e he) hy)
    (fun _ => Grows.bind (Grows.when_ _ (Grows.ledgerOp _ _)) fun _ => Grows.cond _ (Grows.pure' _) (Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _))
    fun _ s₈ st₈ hn₈ hgd₈ ha₈ hQ₈ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hP₈, hL₈⟩ := hQ₈.holds
  simp only [ite_true] at hL₈
  have hg₈ := GuardIs.later hg₇ ha₈ hn₈ hgd₈
  have hparts : ∀ e, Value.Is p e recipient (Fr.ofBool u :: rl ++ rr) →
      recipient.isLeft.expr.eval p e = some (Fr.ofBool u) ∧ Value.Is p e recipient.left rl ∧
        Value.Is p e recipient.right rr := fun e h => either_is (by rw [hsh.1, hrl]) h
  have hR₈ := (hR₆.later ha₇ hn₇).later ha₈ hn₈
  have hS₈ := ((((((hS₂.later ha₃ hn₃).later ha₄ hn₄).later ha₅ hn₅).later ha₆ hn₆).later ha₇ hn₇).later ha₈ hn₈)
  have hcond : Stable s₈.next st₈.env (fun e => Boolean.Is p e
      (!. recipient.isLeft &&. (recipient.right.bytes ==. selfAddr.bytes)) selfR) := by
    intro e he
    have hp := hparts e (hR₈ e he)
    have heq : Boolean.Is p e (recipient.right.bytes ==. selfAddr.bytes) (decide (rr = selfFs)) :=
      valueEq_is (p := p) hp.2.2 (hS₈ e he) (by rw [hrr, hsl])
    exact Boolean.and_is (Boolean.not_is (show Boolean.Is p e recipient.isLeft u from hp.1)) heq
  have hCM₈ := hCM₇.later ha₈ hn₈
  -- 9. `if% … then Kernel.claimZswapCoinReceive cm`
  refine (XRuns.seq (ok₂ := True)
    (XRuns.when_someOp (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (cb := selfR) (σ₁ := L (es₈.set 1 (.map (assocSet (hkey y) .null m1))))
      rfl (by simp) hg₈ hcond fun e he => by
      rw [hL₈]
      exact Kernel.claimZswapCoinReceive_spec H p e (L es₈) es₈ m1 cmv cm (hkey y) hwf₈ rfl hm1₈ (hCM₈ e he) hy)
    (fun _ => Grows.cond _ (Grows.pure' _) (Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _))
    fun _ s₉ st₉ hn₉ hgd₉ ha₉ hQ₉ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hP₉, hL₉⟩ := hQ₉.holds
  have hLs₉ : st₉.ledger = L es₉ := by
    rw [hL₉]; cases hs : selfR <;> simp [hs, es₉, m1', L, hL₈]
  have hg₉ := GuardIs.later hg₈ ha₉ hn₉ hgd₉
  have hPs₉ : st₉.private_ = ω₂ := by rw [hP₉, hP₈, hP₇, hP₆]
  have hA₉ : Agree s₅.next st₅.env st₉.env :=
    ha₆.trans ((ha₇.mono hn₆).trans ((ha₈.mono (Nat.le_trans hn₆ hn₇)).trans
      (ha₉.mono (Nat.le_trans hn₆ (Nat.le_trans hn₇ hn₈)))))
  have hn₅₉ : s₅.next ≤ s₉.next := Nat.le_trans hn₆ (Nat.le_trans hn₇ (Nat.le_trans hn₈ hn₉))
  have hCh₉ := (hCh₄.later ha₅ hn₅).later hA₉ hn₅₉
  have hin₉ := (hin₄.later ha₅ hn₅).later hA₉ hn₅₉
  have hO₉ := hO₅.later hA₉ hn₅₉
  have hS₉ := hS₈.later ha₉ hn₉
  have hc : Stable s₉.next st₉.env (fun e => Boolean.Is p e (change ==. (0 : Uint128)) (decide (chg = 0))) :=
    fun e he => cmpEq_means (hCh₉ e he) (Uint.numeral_means (by decide) uint128_bound)
  let noneFs := Fr.ofBool false :: List.replicate (Value.width ShieldedCoinInfo) 0
  let gb' := !decide (chg = 0)
  let es' := if gb' then esA else es₉
  have hwf' : (L es').WF := by cases hg' : gb' <;> simp [es', hg'] <;> assumption
  have hm1' : es'[1]? = some (.map m1') := by cases hg' : gb' <;> simp [es', hg', hm1A, hm1₉]
  have hshR : (Value.toExprs (right selfAddr : Either ZswapCoinPublicKey ContractAddress).left).length = 2 ∧
      (Value.toExprs (right selfAddr : Either ZswapCoinPublicKey ContractAddress).right).length = 2 :=
    ⟨rfl, ContractAddress.shaped_len hshS⟩
  -- 10. `cond (change ==. 0) (pure (none, output)) (… the change coin …)`
  refine (XRuns.cond (α := ShieldedSendResult) (gb := true) (cb := decide (chg = 0))
    (Qt := fun a env w' l => Value.Is p env a (noneFs ++ (outFs ++ [])) ∧ w' = ω₂ ∧ l = L es₉)
    (Qe := fun a b env w' l => Value.Is p env a (noneFs ++ (outFs ++ [])) ∧
      Value.Is p env b ((Fr.ofBool true :: chFs) ++ (outFs ++ [])) ∧
      w' = (if chg = 0 then ω₂ else ω₃) ∧ l = (if gb' then L esB else L es₉))
    (okt := True) (oke := True) hg₉ hc (Grows.pure' _) (Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _) ?_ ?_).conseq (by simp) ?_
  · intro s' st' ctx
    refine XRuns.pure fun e he => ⟨?_, ctx.2.2.1.trans hPs₉, ctx.2.2.2.1.trans hLs₉⟩
    unfold Value.Is
    exact evalList_append_some (Maybe.none_is roundTrip_coin) (evalList_append_some ((ctx.transfer hO₉) e he) rfl)
  · intro a s' st' hn' hA' hgd' hQt
    obtain ⟨-, hPt, hLt⟩ := hQt.holds
    have hin' := hin₉.later hA' hn'
    have hCh' := hCh₉.later hA' hn'
    have hO' := hO₉.later hA' hn'
    have hS' := hS₉.later hA' hn'
    have hg'' : GuardIs p s' st'.runState gb' := hgd'
    -- e1. `const changeCoin := …`
    have hcc : Stable s'.next st'.env (fun e => Value.Is p e
        ({ nonce := upgradeFromTransient (transientHash (#v[Field.ofString "midnight:kernel:nonce_evolve/2",
            degradeToTransient input.nonce] : Vector Field 2)), color := input.color, value := change } :
          ShieldedCoinInfo) chFs) := by
      intro e he
      unfold Value.Is
      show Expr.evalList p e (_ ++ (input.color.limbs ++ ([change.expr] ++ []))) = _
      rw [show chFs = derivedNonceFs p "midnight:kernel:nonce_evolve/2" n ++ (c ++ [Fr.ofNat chg]) by simp [chFs]]
      exact evalList_append_some (derivedNonce_is "midnight:kernel:nonce_evolve/2" hnl (hin' e he).nonce)
        (evalList_append_some (hin' e he).color (by simp [Expr.evalList, (hCh' e he).eval]))
    refine (XRuns.seq (ok₂ := True)
      (XRuns.val (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (s := s') (st := st') roundTrip_coin (xs := chFs) "changeCoin"
        (by rw [← Damp.evalList_length hcc.holds]; simp [chFs, derivedNonceFs, hcl]; rfl) hcc)
      (fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _)
      fun cc t₁ u₁ hm₁ hgt₁ hb₁ hR₁ => ?_).conseq (by simp) fun _ _ _ _ h => h
    obtain ⟨-, hQP₁, hQL₁⟩ := hR₁.holds
    have hCC₁ : Stable t₁.next u₁.env (fun e => Value.Is p e cc chFs) := hR₁.imp fun e h => h.1
    have hgu₁ := GuardIs.later hg'' hb₁ hm₁ hgt₁
    have hS₁' := hS'.later hb₁ hm₁
    have hO₁' := hO'.later hb₁ hm₁
    -- e2. `createZswapOutput changeCoin (right selfAddr)`
    refine (XRuns.seq (ok₂ := True)
      ((XRuns.askWitness0G_iso (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (α := Unit) rfl rfl "createZswapOutput" hgu₁
        (evalList_append_some hCC₁.holds (right_self_is p hS₁'.holds))).conseq (ok' := True)
        ⟨fun _ => trivial, fun _ h => ⟨ω₃, by
          rw [hQP₁, hPt]; exact hw₃ (by simpa [gb'] using h)⟩⟩ (fun _ _ _ _ h => h))
      (fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _)
      fun _ t₂ u₂ hm₂ hgt₂ hb₂ hR₂ => ?_).conseq (by simp) fun _ _ _ _ h => h
    obtain ⟨hQL₂, hQP₂⟩ := hR₂.holds
    have hgu₂ := GuardIs.later hgu₁ hb₂ hm₂ hgt₂
    have hCC₂ := hCC₁.later hb₂ hm₂
    have hS₂' := hS₁'.later hb₂ hm₂
    -- e3. `const cm := coinCommitment changeCoin (right selfAddr)`
    refine (XRuns.seq (ok₂ := True)
      (XRuns.val (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (s := t₂) (st := u₂) roundTrip_bytes (xs := cm₂) "cm" rfl
        fun e he => coinCommitment_is (hCC₂ e he) hshR rfl (right_self_is p (hS₂' e he)) hcm₂)
      (fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _)
      fun cmv₂ t₃ u₃ hm₃ hgt₃ hb₃ hR₃ => ?_).conseq (by simp) fun _ _ _ _ h => h
    obtain ⟨-, hQP₃, hQL₃⟩ := hR₃.holds
    have hCM₃ : Stable t₃.next u₃.env (fun e => Value.Is p e cmv₂ cm₂) := hR₃.imp fun e h => h.1
    have hgu₃ := GuardIs.later hgu₂ hb₃ hm₃ hgt₃
    have hLu₃ : u₃.ledger = L es₉ := by rw [hQL₃, hQL₂, hQL₁, hLt]
    -- e4. `Kernel.claimZswapCoinSpend cm`
    refine (XRuns.seq (ok₂ := True)
      (XRuns.someOp (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (σ₁ := L esA) rfl (by simp) hgu₃ fun e he => by
        rw [hLu₃]
        exact Kernel.claimZswapCoinSpend_spec H p e (L es₉) es₉ _ cmv₂ cm₂ (hkey z) hwf₉ rfl hm2₉ (hCM₃ e he) hz)
      (fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _)
      fun _ t₄ u₄ hm₄ hgt₄ hb₄ hR₄ => ?_).conseq (by simp) fun _ _ _ _ h => h
    obtain ⟨hQP₄, hQL₄⟩ := hR₄.holds
    have hgu₄ := GuardIs.later hgu₃ hb₄ hm₄ hgt₄
    have hLu₄ : u₄.ledger = L es' := by rw [hQL₄, hLu₃]; cases hg' : gb' <;> simp [es', hg']
    have hCM₄ := hCM₃.later hb₄ hm₄
    -- e5. `Kernel.claimZswapCoinReceive cm`
    refine (XRuns.seq (ok₂ := True)
      (XRuns.someOp (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (σ₁ := L (es'.set 1 (.map (assocSet (hkey z) .null m1'))))
        rfl (by simp) hgu₄ fun e he => by
        rw [hLu₄]
        exact Kernel.claimZswapCoinReceive_spec H p e (L es') es' m1' cmv₂ cm₂ (hkey z) hwf' rfl hm1' (hCM₄ e he) hz)
      (fun _ => Grows.pure' _)
      fun _ t₅ u₅ hm₅ hgt₅ hb₅ hR₅ => ?_).conseq (by simp) fun _ _ _ _ h => h
    obtain ⟨hQP₅, hQL₅⟩ := hR₅.holds
    have hCC₅ := ((hCC₂.later hb₃ hm₃).later hb₄ hm₄).later hb₅ hm₅
    have hO₅' := (((hO₁'.later hb₂ hm₂).later hb₃ hm₃).later hb₄ hm₄).later hb₅ hm₅
    refine XRuns.pure fun e he => ⟨?_, ?_, ?_, ?_⟩
    · exact (((((hQt.imp fun e h => h.1).later hb₁ hm₁).later hb₂ hm₂).later hb₃ hm₃).later hb₄ hm₄).later hb₅ hm₅
        e he
    · unfold Value.Is
      exact evalList_append_some (Maybe.some_is (hCC₅ e he)) (evalList_append_some (hO₅' e he) rfl)
    · rw [hQP₅, hQP₄, hQP₃]
      cases hc0' : decide (chg = 0) with
      | true =>
        have h0 : chg = 0 := of_decide_eq_true hc0'
        have : gb' = false := by simp [gb', hc0']
        rw [this] at hQP₂; simp at hQP₂; rw [hQP₂, hQP₁, hPt]; simp [h0]
      | false =>
        have h0 : ¬ chg = 0 := of_decide_eq_false hc0'
        have : gb' = true := by simp [gb', hc0']
        rw [this] at hQP₂; simp only [ite_true] at hQP₂
        rw [hQP₁, hPt] at hQP₂
        have := hw₃ h0
        change w _ _ _ = _ at hQP₂
        rw [this] at hQP₂; simp at hQP₂; simp [h0, hQP₂]
    · rw [hQL₅, hLu₄]
      cases hg' : gb' <;> simp [hg', es', esB, L]
  · intro r env w' l ⟨a, b, hrab, ⟨ha', hb', hw', hl'⟩, hc'⟩
    have hla : (Value.toExprs a).length = Value.width ShieldedSendResult := by
      rw [← Damp.evalList_length ha', Value.width_sendResult, Value.width_maybe, Value.width_coin]
      simp [noneFs, outFs, derivedNonceFs, hcl, Value.width_coin]
    have hlb : (Value.toExprs b).length = Value.width ShieldedSendResult := by
      rw [← Damp.evalList_length hb', Value.width_sendResult, Value.width_maybe, Value.width_coin]
      simp [chFs, outFs, derivedNonceFs, hcl]
    have hsel := select_is (p := p) roundTrip_sendResult hc' hla hlb ha' hb'
    rw [hrab]
    refine ⟨?_, hw', ?_⟩
    · by_cases h0 : chg = 0
      · simp only [h0, decide_true, ite_true] at hsel
        have e : v.val - k = 0 := h0
        rw [if_pos e]
        have : (Fr.ofBool false :: List.replicate (Value.width ShieldedCoinInfo) 0) ++
            (derivedNonceFs p "midnight:kernel:nonce_evolve" n ++ c ++ [Fr.ofNat k]) = noneFs ++ (outFs ++ []) := by
          simp [noneFs, outFs]
        rw [this]; exact hsel
      · simp only [h0, decide_false, ite_false] at hsel
        have e : ¬ v.val - k = 0 := h0
        rw [if_neg e]
        have : (Fr.ofBool true :: (derivedNonceFs p "midnight:kernel:nonce_evolve/2" n ++ c ++
            [Fr.ofNat (v.val - k)])) ++ (derivedNonceFs p "midnight:kernel:nonce_evolve" n ++ c ++ [Fr.ofNat k]) =
            (Fr.ofBool true :: chFs) ++ (outFs ++ []) := by
          simp [chFs, outFs, chg]
        rw [this]; exact hsel
    · rw [hl']
      by_cases h0 : chg = 0
      · have : gb' = false := by simp [gb', h0]
        simp only [this, ite_false, L, sendSEffects, es₉, es₈, es₁, m1', selfR, σ]
        simp only [chg] at h0; simp [h0]
      · have : gb' = true := by simp [gb', h0]
        simp only [this, ite_true, L, sendSEffects, esB, esA, es₉, es₈, es₁, m1', selfR, σ]
        simp only [chg] at h0; simp [h0]


/-- **`sendImmediateShielded input recipient value`** is `sendShielded` of the
    coin `input` with Merkle index 0: as `sendShielded_runs`. -/
theorem sendImmediateShielded_runs (input : ShieldedCoinInfo) (recipient : Either ZswapCoinPublicKey ContractAddress)
    (value : Uint128) {s : Build} {st : Exec.State ω LedgerState} (hg : GuardIs p s st.runState true)
    (n c : List Fr) (v : Fr) (hnl : input.nonce.limbs.length = 2) (hcl : c.length = 2) (hv : v.val < 2 ^ 128)
    (hin : Stable s.next st.env (fun e => CoinIs p e input n c v))
    (k : Nat) (hk : Stable s.next st.env (fun e => Uint.Means p e value k))
    (u : Bool) (rl rr : List Fr) (hrl : rl.length = 2) (hrr : rr.length = 2)
    (hsh : (Value.toExprs recipient.left).length = 2 ∧ (Value.toExprs recipient.right).length = 2)
    (hr : Stable s.next st.env (fun e => Value.Is p e recipient (Fr.ofBool u :: rl ++ rr)))
    (cfs : List SV) (wa : AV) (selfFs : List Fr) (hctx : st.ledger.context = .array cfs)
    (hc0 : cfs[0]? = some (.cell wa)) (hself : fieldsOf [.bytes 32] wa.atoms = some selfFs) (hwf : st.ledger.WF)
    (es : List SV) (m0 m1 m2 : List (AV × SV)) (heff : st.ledger.effects = .array es)
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
    (hw₁ : w "createZswapInput" (n ++ c ++ [v, 0]) st.private_ = some ([], ω₁))
    (hw₂ : w "createZswapOutput" ((derivedNonceFs p "midnight:kernel:nonce_evolve" n ++ c ++ [Fr.ofNat k]) ++
      (Fr.ofBool u :: rl ++ rr)) ω₁ = some ([], ω₂))
    (hw₃ : v.val - k ≠ 0 → w "createZswapOutput" ((derivedNonceFs p "midnight:kernel:nonce_evolve/2" n ++ c ++
      [Fr.ofNat (v.val - k)]) ++ (Fr.ofBool false :: [0, 0] ++ selfFs)) ω₂ = some ([], ω₃)) :
    XRuns p (oracles H (Damp.Exec.liftWitness w)) (sendImmediateShielded input recipient value) s st (k ≤ v.val)
      (fun r e w' l => Value.Is p e r (if v.val - k = 0
          then (Fr.ofBool false :: List.replicate (Value.width ShieldedCoinInfo) 0) ++
            (derivedNonceFs p "midnight:kernel:nonce_evolve" n ++ c ++ [Fr.ofNat k])
          else (Fr.ofBool true :: (derivedNonceFs p "midnight:kernel:nonce_evolve/2" n ++ c ++
            [Fr.ofNat (v.val - k)])) ++ (derivedNonceFs p "midnight:kernel:nonce_evolve" n ++ c ++ [Fr.ofNat k])) ∧
        w' = (if v.val - k = 0 then ω₂ else ω₃) ∧
        l = { st.ledger with effects := .array (sendSEffects es m0 m1 m2 x y z (!u && decide (rr = selfFs))
          (!decide (v.val - k = 0))) }) :=
  sendShielded_runs H p w { nonce := input.nonce, color := input.color, value := input.value, mt_index := 0 } recipient
    value hg n c v 0 hnl hcl hv
    (hin.imp fun e h => ⟨h.nonce, h.color, h.value, by
      show (Uint.capped 18446744073709551615 (.const 0)).eval p e = some 0
      rw [Uint.capped_eval uint64_bound]; rfl⟩)
    k hk u rl rr hrl hrr hsh hr cfs wa selfFs hctx hc0 hself hwf es m0 m1 m2 heff hm0 hm1 hm2 nf x hnf hx cm y hcm hy
    cm₂ z hcm₂ hz ω₁ ω₂ ω₃ hw₁ hw₂ hw₃

end

end Damp.Ledger
