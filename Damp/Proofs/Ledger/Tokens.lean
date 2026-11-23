/-
The token library (`Damp/Lang/Tokens.lean`) against the VM model: what its
operations do to the effects and to the contract state, composed from the
kernel specifications of `Damp/Proofs/Ledger/Effects.lean`.

**What is assumed about hashes: nothing.** Every coin commitment, nullifier and
token type is computed by the circuit with the hash functions `p : Prims` the
executor runs with; a theorem takes the field elements those expressions
evaluate to (`Value.Is p e x xs`, or `Expr.evalList`) as given and says what the
ledger does with them. No collision resistance or other property of Poseidon or
SHA-256 is used. (What ties a commitment to a coin on chain is outside the
contract, in Zswap.)

What the operations write (unguarded; `c` the 32-byte atom of a color, `cm` of
a commitment, `nf` of a nullifier):

| operation | effects | contract state |
|---|---|---|
| `receiveUnshielded c k` | slot 6: `(1, c, 0) ↦ old + k` | unchanged |
| `sendUnshielded c k r` | slot 7: `(1, c, 0) ↦ old + k`; slot 8: `((1, c, 0), r) ↦ old + k`; slot 6 as `receiveUnshielded` if `r` is this contract | unchanged |
| `mintUnshieldedToken d k r` | slot 5: `d ↦ old + k`; slot 8: `((1, t, 0), r) ↦ old + k`, `t` the token type; slot 6 if `r` is this contract | unchanged |
| `receiveShielded coin` | slot 1: `cm` | unchanged |
| `mintShieldedToken d k n r` | slot 4: `d ↦ old + k`; slot 2: `cm`; slot 1: `cm` if `r` is this contract | unchanged |
| `sendShielded coin r k` | slot 0: `nf`; slot 2: `cm`; slot 1: `cm` if `r` is this contract; the change coin (if any) in slots 2 and 1 | unchanged |
| `mergeCoin a b` | slot 0: `nf a`, `nf b`; slots 2 and 1: the new coin's `cm` | unchanged |
| balance reads | none | unchanged |

Proved here:

* the keys the library builds: `left c` is always a well-formed `TokenType`
  (`tokenKey_left`), so the unshielded operations never fail on their key; the
  spend key `(left c, r)` is well formed exactly when `r` is a well-formed
  `PublicAddress` (`spendKey_left`), so `sendUnshielded` and
  `mintUnshieldedToken` with an `Either` recipient that has both sides set
  fail (`executor/test/either-both.mjs` checks the same end to end);
* `receiveUnshielded`, end to end through the executor (`XRuns`):
  `receiveUnshielded_runs`;
* the unshielded operations' two additions composed (`addReq_seq`,
  `sendUnshielded_requests`, `mintUnshielded_requests`), and the failure of
  a malformed recipient (`sendUnshielded_badRecipient`);
* the Zswap claims composed (`claims_compose`): any sequence of claims of
  32-byte keys in slots 0 to 2 (what `receiveShielded`, `sendShielded`,
  `mergeCoin` and `mintShieldedToken` claim) never fails and only adds the
  keys to their slots;
* every effect-writing kernel request changes only the effects
  (`EffectsOnly`: `claimReq_effectsOnly`, `addReq_effectsOnly`,
  `callClaimReq_effectsOnly`), and so does any sequence of them
  (`effectsOnly_chain`, which also keeps `WF`);
* the balance read (`Kernel.balance_spec`): 0 when the context's balance map
  (context slot 5) has no entry for the token type, the entry read as `u128`
  otherwise; the ledger unchanged.

Not proved here: the shielded operations and `sendUnshielded` /
`mintUnshieldedToken` end to end through the executor (the `XRuns`
descriptions of their bodies, with `if%`, `cond` and the zero-width
`createZswap*` witnesses); what is stated for them is about the ledger
requests they send, in the order they send them, and those requests are
exactly the ones the per-operation theorems of `Effects.lean` compute from the
emitted statements. `balanceLessThan` and `balanceGreaterThan` compare with
`lt`, which takes `u64` operands: a balance or amount of `2^64` or more makes
them fail (not stated here; the model and the runtime agree on `lt`).
-/
import Damp.Proofs.Ledger.Effects
import Damp.Proofs.Interface.LedgerLogic
import Damp.Lang.Tokens

namespace Damp.Ledger
open Damp.IR Damp.Impact

set_option linter.unusedSimpArgs false

/-! ## The keys the token library builds -/

theorem zero_bytes32_limbs : (Value.zero (Bytes 32)).limbs = [.const 0, .const 0] := by
  simp [Value.zero, Value.ofExprs, Value.shape, Shape.ranges, Shape.tys, Ty.ranges, byteLimbs]

/-- `left c` (an unshielded token type, Compact's `left<Bytes<32>, Bytes<32>>(c)`)
    as the VM stores it: `(1, c, 0)`, a well-formed `TokenType`. -/
theorem tokenKey_left (p : Zkir.Prims) (env : Env) (color : Bytes 32) (cs : List Fr) (c : Nat)
    (hcs : Value.Is p env color cs) (hlen : cs.length = 2) (hc : AV.ofFields [.bytes 32] cs = some ⟨[.bytes 32], [c]⟩) :
    ∃ ks, Expr.evalList p env (Value.toExprs (left color : TokenType)) = some ks ∧
      AV.ofFields alignTokenType ks = some ⟨alignTokenType, [1, c, 0]⟩ ∧ tokenTypeOk [1, c, 0] = true := by
  have hc256 : c < 2 ^ 256 := by
    obtain ⟨x, hx, he⟩ := bytes32_key hc
    simp at he; subst he; exact hx
  match cs, hlen with
  | [c₁, c₂], _ =>
    refine ⟨[Fr.ofInt 1, c₁, c₂, Fr.ofInt 0, Fr.ofInt 0], ?_, ?_, ?_⟩
    · unfold Value.Is at hcs
      rw [evalList_eq_mapM] at hcs ⊢
      simp only [Value.toExprs] at hcs
      have hz := zero_bytes32_limbs
      simp only [left, Value.toExprs, Boolean.true, List.mapM_cons, List.mapM_append, hcs, hz, Expr.eval]
      rfl
    · have h0 : (Fr.ofInt 0).val = 0 := rfl
      simp only [AV.ofFields, atomWidth, atomOfFields, atomFits] at hc
      simp at hc
      have hn : ¬ 2 ^ 256 ≤ c := by omega
      simp [AV.ofFields, atomWidth, atomOfFields, atomFits, frOfInt_val_one, h0, alignTokenType, hc.1, hc.2, hn]
    · simp [tokenTypeOk, hashOk, hc256]

/-- The spend key `(left c, r)` (effects slot 8) is well formed exactly when the
    recipient's three atoms are a well-formed `PublicAddress`. -/
theorem spendKey_left (c : Nat) (hc : c < 2 ^ 256) (r : List Nat) (hr : r.length = 3) :
    spendKeyOk ([1, c, 0] ++ r) = publicAddressOk r := by
  have : tokenTypeOk [1, c, 0] = true := by simp [tokenTypeOk, hashOk, hc]
  simp [spendKeyOk, hr, this]

theorem effectKey_spend_left (c : Nat) (hc : c < 2 ^ 256) (r : List Nat) (hr : r.length = 3) :
    effectKey 8 ⟨alignTokenType ++ alignPublicAddress, [1, c, 0] ++ r⟩ =
      if publicAddressOk r then some ⟨alignTokenType ++ alignPublicAddress, [1, c, 0] ++ r⟩ else none := by
  have hs : spendKeyOk ([1, c, 0] ++ r) = publicAddressOk r := spendKey_left c hc r hr
  simp only [effectKey]
  simp only [show ¬ ((8 : Nat) ≤ 2 ∨ (8 : Nat) = 4 ∨ (8 : Nat) = 5) by decide, ite_false,
    show ¬ ((8 : Nat) = 3) by decide, show ¬ ((8 : Nat) = 6 ∨ (8 : Nat) = 7) by decide, ite_true, hs]

/-! ## `receiveUnshielded`, end to end -/

section
variable {ω : Type} (H : Hooks) (p : Zkir.Prims) (w : String → List Fr → ω → Option (List Fr × ω))

/-- The key `receiveUnshielded` writes. -/
def leftKey (c : Nat) : AV := ⟨alignTokenType, [1, c, 0]⟩

/-- The instructions `receiveUnshielded` sends (`incUnshieldedInputs (left color)`). -/
def receiveUnshieldedOps (color : Bytes 32) (amount : Uint128) : List (Op Expr) :=
  [.swap 0, .idx true true [fieldKey 6],
   .push false (alignedOf (left color : TokenType)), .dup 1, .dup 1, .member,
   .push false ⟨[.bytes 16], [amount.expr]⟩, .swap 0, .neg, .branch 4, .dup 2, .dup 2, .idxStack [], .add,
   .ins true 2, .swap 0]

theorem receiveUnshielded_eq (color : Bytes 32) (amount : Uint128) :
    receiveUnshielded color amount = ledgerOp [] (receiveUnshieldedOps color amount) := rfl

/-- **`receiveUnshielded color amount`, run by the executor** against the
    modelled ledger, under a guard that holds, with `color` meaning the limbs
    `cs` of the 32-byte atom `c` and `amount` meaning `a < 2^128`: it completes
    exactly when `(1, c, 0)` has no entry among the unshielded inputs (effects
    slot 6) or the sum fits 64 bits; then the private state is unchanged and the
    ledger is `σ` with only slot 6 changed, `(1, c, 0) ↦ old + a`. -/
theorem receiveUnshielded_runs (color : Bytes 32) (amount : Uint128) {s : Build} {st : Exec.State ω LedgerState}
    (hg : GuardIs p s st.runState true) (cs : List Fr) (hlen : cs.length = 2) (c : Nat)
    (hcs : Stable s.next st.env (fun e => Value.Is p e color cs))
    (hc : AV.ofFields [.bytes 32] cs = some ⟨[.bytes 32], [c]⟩)
    (a : Fr) (ha : Stable s.next st.env (fun e => amount.expr.eval p e = some a)) (ha128 : a.val < 2 ^ 128)
    (es : List SV) (m : List (AV × SV)) (hwf : st.ledger.WF) (heff : st.ledger.effects = .array es)
    (hm : es[6]? = some (.map m)) :
    XRuns p (oracles H w) (receiveUnshielded color amount) s st
      ((assocGet (leftKey c) m).isNone ∨ effAmount m (leftKey c) + a.val < 2 ^ 64)
      (fun _ _ w' l => w' = st.private_ ∧
        l = { st.ledger with
          effects := .array (es.set 6 (.map (assocSet (leftKey c) (amountCell 6 (effAmount m (leftKey c) + a.val)) m))) })
      := by
  rw [receiveUnshielded_eq]
  have hreq : ∀ e, Agree s.next st.env e → ∃ req, Exec.request p e (receiveUnshieldedOps color amount) = some req ∧
      (oracles H w).ledger req st.ledger =
        if (assocGet (leftKey c) m).isNone ∨ effAmount m (leftKey c) + a.val < 2 ^ 64 then
          some ([], { st.ledger with
            effects := .array (es.set 6 (.map (assocSet (leftKey c) (amountCell 6 (effAmount m (leftKey c) + a.val)) m))) })
        else none := by
    intro e he
    obtain ⟨ks, hks, hkv, hok⟩ := tokenKey_left p e color cs c (hcs e he) hlen hc
    have h := Kernel.incUnshieldedInputs_spec H p e st.ledger es m (left color) amount ks (leftKey c) a hwf heff hm
      hks hkv hok (ha e he) ha128
    exact h
  have h := XRuns.ledgerOp (p := p) (O := oracles H w) (s := s) (st := st) (by simp [receiveUnshieldedOps]) hg hreq
  refine h.conseq ?_ ?_
  · split <;> simp_all
  · intro _ _ w' l ⟨hw, hl⟩
    refine ⟨hw, ?_⟩
    split at hl
    · simp at hl; exact hl.symm
    · simp at hl

end

/-! ## Sequences of claims and additions

Every effect-writing kernel request leaves the contract state and the call
context as they were and changes one slot of the effects; so does any
sequence of them. -/

/-- A request that changes only the effects: from a well-formed state, whatever
    it answers leaves the contract state and the call context unchanged. -/
def EffectsOnly (H : Hooks) (req : List (Op Fr)) : Prop :=
  ∀ σ σ' xs, σ.WF → ledgerOracle H req σ = some (xs, σ') → σ'.state = σ.state ∧ σ'.context = σ.context

theorem effectsOnly_of_eq {H : Hooks} {req : List (Op Fr)}
    (h : ∀ σ, σ.WF → ∃ eff : SV, ledgerOracle H req σ = some ([], { σ with effects := eff }) ∨
      ledgerOracle H req σ = none) : EffectsOnly H req := by
  intro σ σ' xs hwf hq
  obtain ⟨eff, h | h⟩ := h σ hwf <;> rw [h] at hq
  · simp at hq; obtain ⟨-, rfl⟩ := hq; exact ⟨rfl, rfl⟩
  · simp at hq

/-- The claims (slots 0 to 2) change only the effects. -/
theorem claimReq_effectsOnly (H : Hooks) {i : Nat} (hi : i ≤ 2) (key : Aligned Fr)
    (hkey : ∀ kv, AV.ofAligned key = some kv → ∃ x, x < 2 ^ 256 ∧ kv = ⟨[.bytes 32], [x]⟩) :
    EffectsOnly H (claimReq i key) := by
  apply effectsOnly_of_eq
  intro σ hwf
  have hwf' := hwf
  rw [LedgerState.WF] at hwf'
  cases hkv : AV.ofAligned key with
  | none =>
    refine ⟨.null, Or.inr ?_⟩
    exact ledgerOracle_of_toR_none H (o := .push false key) (by simp [claimReq]) (by simp [Op.toR, hkv]) σ
  | some kv =>
    obtain ⟨x, hx, rfl⟩ := hkey _ hkv
    -- the effects of a well-formed state are nine maps
    cases he : σ.effects with
    | array es =>
      rw [he] at hwf'
      cases hm : es[i]? with
      | none =>
        rw [decodeEffects_array] at hwf'
        have hl : es.length = 9 := by split at hwf' <;> simp_all
        rw [List.getElem?_eq_none_iff] at hm
        omega
      | some e =>
        cases e with
        | map m =>
          exact ⟨_, Or.inl (claimReq_spec H σ es m i key _ (by omega) hwf he hm hkv (effectEntry_hash hi hx))⟩
        | _ =>
          refine ⟨.null, Or.inr ?_⟩
          rw [decodeEffects_array] at hwf'
          split at hwf'
          · simp only [Option.map_eq_some_iff] at hwf'
            obtain ⟨es', hmap, hes⟩ := hwf'
            cases hes
            obtain ⟨y, hy, -⟩ := mapM_zipIdx_get slotDecode es 0 i es _ hmap hm
            simp [slotDecode] at hy
          · simp at hwf'
    | _ =>
      rw [he] at hwf'
      simp [decodeEffects] at hwf'

/-- Requests that change only the effects, in sequence, change only the effects. -/
theorem effectsOnly_chain {H : Hooks} :
    ∀ (reqs : List (List (Op Fr))) (σ σ' : LedgerState), σ.WF → (∀ r ∈ reqs, EffectsOnly H r) →
      reqs.foldlM (fun σ r => (ledgerOracle H r σ).map Prod.snd) σ = some σ' →
      σ'.state = σ.state ∧ σ'.context = σ.context ∧ σ'.WF
  | [], σ, σ', hwf, _, h => by simp at h; subst h; exact ⟨rfl, rfl, hwf⟩
  | r :: rs, σ, σ', hwf, hall, h => by
      simp only [List.foldlM_cons] at h
      cases hq : ledgerOracle H r σ with
      | none => simp [hq] at h
      | some res =>
        obtain ⟨xs, σ₁⟩ := res
        simp only [hq, Option.map_some, Option.bind_eq_bind, Option.bind_some] at h
        obtain ⟨hs₁, hc₁⟩ := hall r (List.mem_cons_self ..) σ σ₁ xs hwf hq
        have hwf₁ := ledgerOracle_wf hq
        obtain ⟨hs, hc, hw⟩ := effectsOnly_chain rs σ₁ σ' hwf₁ (fun r' hr' => hall r' (List.mem_cons_of_mem _ hr')) h
        exact ⟨hs.trans hs₁, hc.trans hc₁, hw⟩

/-- The additions (slots 4 to 8) change only the effects, for a key in its
    type's alignment (true of every key Damp writes: `effectKey_tokenType`,
    `effectKey_spend`, `bytes32_key`). -/
theorem addReq_effectsOnly (H : Hooks) {slot : Nat} (hs : 4 ≤ slot ∧ slot ≤ 8) (key : Aligned Fr) (a : Fr)
    (hamt : AV.ofFields [.bytes (amountWidth slot)] [a] = some ⟨[.bytes (amountWidth slot)], [a.val]⟩)
    (ha : a.val < 2 ^ (8 * amountWidth slot))
    (hkey : ∀ kv, AV.ofAligned key = some kv → effectKey slot kv = some kv ∨ effectKey slot kv = none) :
    EffectsOnly H (addReq slot key ⟨[.bytes (amountWidth slot)], [a]⟩) := by
  apply effectsOnly_of_eq
  intro σ hwf
  have hwf' := hwf
  rw [LedgerState.WF] at hwf'
  cases hkv : AV.ofAligned key with
  | none =>
    exact ⟨.null, Or.inr (ledgerOracle_of_toR_none H (o := .push false key) (by simp [addReq])
      (by simp [Op.toR, hkv]) σ)⟩
  | some kv =>
    cases he : σ.effects with
    | array es =>
      rw [he] at hwf'
      have hwf'' := hwf'
      rw [decodeEffects_array] at hwf''
      have hl : es.length = 9 := by split at hwf'' <;> simp_all
      cases hm : es[slot]? with
      | none =>
        rw [List.getElem?_eq_none_iff] at hm
        omega
      | some e =>
        cases e with
        | map m =>
          rcases hkey kv hkv with hk | hk
          · refine ⟨.array (es.set slot (.map (assocSet kv (amountCell slot (effAmount m kv + a.val)) m))), ?_⟩
            rw [addReq_spec H σ es m slot hs key kv a hwf he hm hkv hk ha hamt]
            split <;> simp
          · exact ⟨.null, Or.inr (addReq_badKey H σ es m slot hs key kv a hwf he hm hkv hk hamt)⟩
        | _ =>
          refine ⟨.null, Or.inr ?_⟩
          split at hwf''
          · simp only [Option.map_eq_some_iff] at hwf''
            obtain ⟨es', hmap, hes⟩ := hwf''
            cases hes
            obtain ⟨y, hy, -⟩ := mapM_zipIdx_get slotDecode es 0 slot es _ hmap hm
            simp [slotDecode] at hy
          · omega
    | _ =>
      rw [he] at hwf'
      simp [decodeEffects] at hwf'

/-- A call's claim changes only the effects. -/
theorem callClaimReq_effectsOnly (H : Hooks) (ks : List Fr)
    (hks : ∃ kv, AV.ofFields [.bytes 32, .bytes 32, .field] ks = some kv) :
    EffectsOnly H (callClaimReq ks) := by
  apply effectsOnly_of_eq
  intro σ hwf
  obtain ⟨kv, hkv⟩ := hks
  have hwf' := hwf
  rw [LedgerState.WF] at hwf'
  cases he : σ.effects with
  | array es =>
    rw [he] at hwf'
    have hwf'' := hwf'
    rw [decodeEffects_array] at hwf''
    have hl : es.length = 9 := by split at hwf'' <;> simp_all
    cases hm : es[3]? with
    | none =>
      rw [List.getElem?_eq_none_iff] at hm
      omega
    | some e =>
      cases e with
      | map m =>
        refine ⟨.array (es.set 3 (.map (assocSet ⟨alignContractCall, m.length :: kv.atoms⟩ .null m))), ?_⟩
        rw [callClaimReq_spec H σ es m ks kv hwf he hm hkv]
        split <;> simp
      | _ =>
        refine ⟨.null, Or.inr ?_⟩
        split at hwf''
        · simp only [Option.map_eq_some_iff] at hwf''
          obtain ⟨es', hmap, hes⟩ := hwf''
          cases hes
          obtain ⟨y, hy, -⟩ := mapM_zipIdx_get slotDecode es 0 3 es _ hmap hm
          simp [slotDecode] at hy
        · omega
  | _ =>
    rw [he] at hwf'
    simp [decodeEffects] at hwf'

/-! ## Compositions -/

/-- The effects after claiming `kv` in slot `i`. -/
def effClaim (es : List SV) (ikv : Nat × AV) : List SV :=
  match es[ikv.1]? with
  | some (.map m) => es.set ikv.1 (.map (assocSet ikv.2 .null m))
  | _ => es

/-- **Zswap claims in sequence** (what `receiveShielded`, `sendShielded`,
    `mergeCoin` and `mintShieldedToken` send, apart from their reads and the
    mint): each 32-byte key `x` claimed in its slot `i ≤ 2`, in order; never
    fails, and leaves the contract state and the call context unchanged. -/
theorem claims_compose (H : Hooks) :
    ∀ (cl : List (Nat × Nat)) (σ : LedgerState) (es : List SV), σ.WF → σ.effects = .array es →
      (∀ ix ∈ cl, ix.1 ≤ 2 ∧ ix.2 < 2 ^ 256) →
      ∀ (keys : List (Aligned Fr)), keys.length = cl.length →
        (∀ k ∈ keys.zip cl, AV.ofAligned k.1 = some ⟨[.bytes 32], [k.2.2]⟩) →
        (List.zipWith (fun k ix => claimReq ix.1 k) keys cl).foldlM (fun σ r => (ledgerOracle H r σ).map Prod.snd) σ =
          some { σ with effects := .array (cl.foldl (fun es ix => effClaim es (ix.1, ⟨[.bytes 32], [ix.2]⟩)) es) }
  | [], σ, es, _, he, _, keys, hk, _ => by
      cases keys with
      | nil => simp; cases σ; simp_all
      | cons => simp at hk
  | (i, x) :: cl, σ, es, hwf, he, hcl, keys, hk, hkeys => by
      cases keys with
      | nil => simp at hk
      | cons k keys =>
        have hix := hcl (i, x) (List.mem_cons_self ..)
        have hkv : AV.ofAligned k = some ⟨[.bytes 32], [x]⟩ := hkeys (k, (i, x)) (by simp)
        have hwf' := hwf
        rw [LedgerState.WF, he] at hwf'
        have hwf'' := hwf'
        rw [decodeEffects_array] at hwf''
        have hl : es.length = 9 := by split at hwf'' <;> simp_all
        have hil : i < es.length := by omega
        -- slot i holds a map
        obtain ⟨m, hm⟩ : ∃ m, es[i]? = some (.map m) := by
          cases hm : es[i]? with
          | none => rw [List.getElem?_eq_none_iff] at hm; omega
          | some e =>
            cases e with
            | map m => exact ⟨m, rfl⟩
            | _ =>
              split at hwf''
              · simp only [Option.map_eq_some_iff] at hwf''
                obtain ⟨es', hmap, hes⟩ := hwf''
                cases hes
                obtain ⟨y, hy, -⟩ := mapM_zipIdx_get slotDecode es 0 i es _ hmap hm
                simp [slotDecode] at hy
              · omega
        have h1 := claimReq_spec H σ es m i k ⟨[.bytes 32], [x]⟩ (by omega) hwf he hm hkv (effectEntry_hash hix.1 hix.2)
        have hwf₁ := ledgerOracle_wf h1
        have ih := claims_compose H cl _ _ hwf₁ rfl (fun ix h => hcl ix (List.mem_cons_of_mem _ h))
          keys (by simpa using hk) (fun kk h => hkeys kk (by simp [h]))
        simp only [List.zipWith_cons_cons, List.foldlM_cons, h1, Option.map_some, Option.bind_eq_bind,
          Option.bind_some]
        rw [ih]
        simp [effClaim, hm]

/-- The condition under which an addition of `a` to `kv` in a map `m` succeeds. -/
def addOk (m : List (AV × SV)) (kv : AV) (a : Nat) : Prop := (assocGet kv m).isNone ∨ effAmount m kv + a < 2 ^ 64

instance (m : List (AV × SV)) (kv : AV) (a : Nat) : Decidable (addOk m kv a) := by unfold addOk; infer_instance

/-- The map in slot `slot` after adding `a` to `kv`. -/
def addMap (slot : Nat) (m : List (AV × SV)) (kv : AV) (a : Nat) : SV :=
  .map (assocSet kv (amountCell slot (effAmount m kv + a)) m)

/-- **Two additions in different slots, in sequence**: they succeed exactly when
    each does on its own map, and then both slots are updated. -/
theorem addReq_seq (H : Hooks) (σ : LedgerState) (es : List SV) {i j : Nat} (hi : 4 ≤ i ∧ i ≤ 8) (hj : 4 ≤ j ∧ j ≤ 8)
    (hij : i ≠ j) (mi mj : List (AV × SV)) (hwf : σ.WF) (heff : σ.effects = .array es)
    (hmi : es[i]? = some (.map mi)) (hmj : es[j]? = some (.map mj))
    (ki kj : Aligned Fr) (kvi kvj : AV) (hki : AV.ofAligned ki = some kvi) (hkj : AV.ofAligned kj = some kvj)
    (hei : effectKey i kvi = some kvi) (hej : effectKey j kvj = some kvj)
    (ai aj : Fr) (hai : ai.val < 2 ^ (8 * amountWidth i)) (haj : aj.val < 2 ^ (8 * amountWidth j))
    (hami : AV.ofFields [.bytes (amountWidth i)] [ai] = some ⟨[.bytes (amountWidth i)], [ai.val]⟩)
    (hamj : AV.ofFields [.bytes (amountWidth j)] [aj] = some ⟨[.bytes (amountWidth j)], [aj.val]⟩) :
    (ledgerOracle H (addReq i ki ⟨[.bytes (amountWidth i)], [ai]⟩) σ).bind
        (fun r => ledgerOracle H (addReq j kj ⟨[.bytes (amountWidth j)], [aj]⟩) r.2) =
      if addOk mi kvi ai.val ∧ addOk mj kvj aj.val then
        some ([], { σ with effects := .array ((es.set i (addMap i mi kvi ai.val)).set j (addMap j mj kvj aj.val)) })
      else none := by
  rw [addReq_spec H σ es mi i hi ki kvi ai hwf heff hmi hki hei hai hami]
  by_cases h1 : (assocGet kvi mi).isNone ∨ effAmount mi kvi + ai.val < 2 ^ 64
  · simp only [h1, ite_true, Option.bind_some]
    have hq := addReq_spec H σ es mi i hi ki kvi ai hwf heff hmi hki hei hai hami
    rw [ite_eq_left_of_eq_true _ _ (eq_true h1)] at hq
    have hwf₁ := ledgerOracle_wf hq
    have hmj' : (es.set i (.map (assocSet kvi (amountCell i (effAmount mi kvi + ai.val)) mi)))[j]? = some (.map mj) := by
      rw [List.getElem?_set_ne hij]; exact hmj
    rw [addReq_spec H _ _ mj j hj kj kvj aj hwf₁ rfl hmj' hkj hej haj hamj]
    have h1' : assocGet kvi mi = none ∨ effAmount mi kvi + ai.val < 2 ^ 64 := by simpa using h1
    simp [addOk, addMap, h1']
  · simp only [h1, ite_false, Option.bind_none]
    have h1' : ¬ (assocGet kvi mi = none ∨ effAmount mi kvi + ai.val < 2 ^ 64) := by simpa using h1
    simp [addOk, h1']

/-- **`sendUnshielded c k r`, its two kernel requests** (to a recipient that is
    not this contract, whose `incUnshieldedInputs` is not asked): the outputs
    (slot 7) count `k` more of `(1, c, 0)` and the spends (slot 8) `k` more to
    `((1, c, 0), r)`. Both succeed exactly when each sum fits 64 bits or its
    entry is new; the contract state is unchanged. The keys are those
    `Kernel.incUnshieldedOutputs_spec` and `Kernel.claimUnshieldedCoinSpend_spec`
    send for `left c` (`tokenKey_left`); `r` must be a well-formed
    `PublicAddress` (otherwise the second request fails, `sendUnshielded_badRecipient`). -/
theorem sendUnshielded_requests (H : Hooks) (σ : LedgerState) (es : List SV) (m7 m8 : List (AV × SV))
    (hwf : σ.WF) (heff : σ.effects = .array es) (hm7 : es[7]? = some (.map m7)) (hm8 : es[8]? = some (.map m8))
    (c : Nat) (hc : c < 2 ^ 256) (r : List Nat) (hr : r.length = 3) (hpa : publicAddressOk r = true)
    (k7 k8 : Aligned Fr) (hk7 : AV.ofAligned k7 = some (leftKey c))
    (hk8 : AV.ofAligned k8 = some ⟨alignTokenType ++ alignPublicAddress, [1, c, 0] ++ r⟩)
    (a : Fr) (ha : a.val < 2 ^ 128) :
    (ledgerOracle H (addReq 7 k7 ⟨[.bytes 16], [a]⟩) σ).bind
        (fun q => ledgerOracle H (addReq 8 k8 ⟨[.bytes 16], [a]⟩) q.2) =
      if addOk m7 (leftKey c) a.val ∧ addOk m8 ⟨alignTokenType ++ alignPublicAddress, [1, c, 0] ++ r⟩ a.val then
        some ([], { σ with effects := .array ((es.set 7 (addMap 7 m7 (leftKey c) a.val)).set 8
          (addMap 8 m8 ⟨alignTokenType ++ alignPublicAddress, [1, c, 0] ++ r⟩ a.val)) })
      else none := by
  have htok : tokenTypeOk [1, c, 0] = true := by simp [tokenTypeOk, hashOk, hc]
  exact addReq_seq H σ es (i := 7) (j := 8) (by decide) (by decide) (by decide) m7 m8 hwf heff hm7 hm8 k7 k8 _ _
    hk7 hk8 (by simp [effectKey, leftKey, htok]) (by rw [effectKey_spend_left c hc r hr, hpa]; rfl)
    a a (by simpa [amountWidth] using ha) (by simpa [amountWidth] using ha) (ofFields_u128 ha) (ofFields_u128 ha)

/-- `sendUnshielded` to a recipient that is not a well-formed `PublicAddress`
    (an `Either` with both sides set): the spend's request fails. -/
theorem sendUnshielded_badRecipient (H : Hooks) (σ : LedgerState) (es : List SV) (m8 : List (AV × SV))
    (hwf : σ.WF) (heff : σ.effects = .array es) (hm8 : es[8]? = some (.map m8))
    (c : Nat) (hc : c < 2 ^ 256) (r : List Nat) (hr : r.length = 3) (hpa : publicAddressOk r = false)
    (k8 : Aligned Fr) (hk8 : AV.ofAligned k8 = some ⟨alignTokenType ++ alignPublicAddress, [1, c, 0] ++ r⟩)
    (a : Fr) (ha : a.val < 2 ^ 128) :
    ledgerOracle H (addReq 8 k8 ⟨[.bytes 16], [a]⟩) σ = none :=
  addReq_badKey H σ es m8 8 (by decide) k8 _ a hwf heff hm8 hk8
    (by rw [effectKey_spend_left c hc r hr, hpa]; rfl) (ofFields_u128 ha)

/-- **`mintUnshieldedToken d k r`, its two additions** (the mint in slot 5,
    keyed by the domain separator `d`; the spend in slot 8, keyed by the token
    type `t` the circuit derived and `r`): as `sendUnshielded_requests`. The
    `Kernel.self` read between them leaves the ledger unchanged
    (`Kernel.self_spec`). -/
theorem mintUnshielded_requests (H : Hooks) (σ : LedgerState) (es : List SV) (m5 m8 : List (AV × SV))
    (hwf : σ.WF) (heff : σ.effects = .array es) (hm5 : es[5]? = some (.map m5)) (hm8 : es[8]? = some (.map m8))
    (d : Nat) (hd : d < 2 ^ 256) (t : Nat) (ht : t < 2 ^ 256) (r : List Nat) (hr : r.length = 3)
    (hpa : publicAddressOk r = true)
    (k5 k8 : Aligned Fr) (hk5 : AV.ofAligned k5 = some ⟨[.bytes 32], [d]⟩)
    (hk8 : AV.ofAligned k8 = some ⟨alignTokenType ++ alignPublicAddress, [1, t, 0] ++ r⟩)
    (a : Fr) (ha : a.val < 2 ^ 64) (a' : Fr) (ha' : a'.val < 2 ^ 128) :
    (ledgerOracle H (addReq 5 k5 ⟨[.bytes 8], [a]⟩) σ).bind
        (fun q => ledgerOracle H (addReq 8 k8 ⟨[.bytes 16], [a']⟩) q.2) =
      if addOk m5 ⟨[.bytes 32], [d]⟩ a.val ∧ addOk m8 ⟨alignTokenType ++ alignPublicAddress, [1, t, 0] ++ r⟩ a'.val then
        some ([], { σ with effects := .array ((es.set 5 (addMap 5 m5 ⟨[.bytes 32], [d]⟩ a.val)).set 8
          (addMap 8 m8 ⟨alignTokenType ++ alignPublicAddress, [1, t, 0] ++ r⟩ a'.val)) })
      else none :=
  addReq_seq H σ es (i := 5) (j := 8) (by decide) (by decide) (by decide) m5 m8 hwf heff hm5 hm8 k5 k8 _ _
    hk5 hk8 (by simp [effectKey, AV.toHash, hd, AV.ofHash]) (by rw [effectKey_spend_left t ht r hr, hpa]; rfl)
    a a' (by simpa [amountWidth] using ha) (by simpa [amountWidth] using ha') (ofFields_u64 ha) (ofFields_u128 ha')

/-! ## Balance reads -/

/-- **`Kernel.balance t`** (`unshieldedBalance`): the contract's balance of the
    token type `t` (stored as `kv`) when the transaction started, from the call
    context's balance map (context slot 5): 0 when it has none, its amount read
    as `u128` otherwise; the ledger is unchanged. Sends and receives in this
    call do not change it (they write the effects, not the context). -/
theorem Kernel.balance_spec (H : Hooks) (p : Zkir.Prims) (env : Env) (σ : LedgerState) (t : TokenType)
    (ks : List Fr) (kv : AV) (hk : Expr.evalList p env (Value.toExprs t) = some ks)
    (hkv : AV.ofFields alignTokenType ks = some kv)
    (cfs : List SV) (bal : List (AV × SV)) (hctx : σ.context = .array cfs) (hb : cfs[5]? = some (.map bal))
    (hwf : σ.WF) :
    ∃ req, (emitted (Kernel.balance t)).bind (Exec.request p env) = some req ∧
      ledgerOracle H req σ =
        match assocGet kv bal with
        | none => some ([0], σ)
        | some (.cell w) => (fieldsOf [.bytes 16] w.atoms).map (·, σ)
        | some _ => none := by
  have he : Kernel.balance t = ledgerRead Uint128 (fun es =>
      [.dup 2, .idx true false [fieldKey 5], .dup 0, .push false (alignedOf t), .member, .branch 3, .pop,
       .push false ⟨[.bytes 16], [.const 0]⟩, .jmp 1, .idx true false [alignedOf t], .popeq true [.bytes 16] es]) := rfl
  rw [he, emitted_ledgerRead]
  rw [evalList_eq_mapM] at hk
  refine ⟨[.dup 2, .idx true false [⟨[.bytes 1], [Fr.ofInt 5]⟩], .dup 0, .push false ⟨alignTokenType, ks⟩, .member,
    .branch 3, .pop, .push false ⟨[.bytes 16], [Fr.ofInt 0]⟩, .jmp 1, .idx true false [⟨alignTokenType, ks⟩],
    .popeq true [.bytes 16] []], ?_, ?_⟩
  · simp [Exec.request, Op.mapM, Aligned.mapM, Exec.blank, fieldKey, Expr.eval, mapM_eval_readVars, alignedOf, hk]
    rfl
  · have hkey : AV.ofFields [.bytes 1] [Fr.ofInt 5] = some ⟨[.bytes 1], [5]⟩ := ofAligned_byteKey (i := 5) (by decide)
    have h00 : (Fr.ofInt 0).val = 0 := rfl
    have h0 : AV.ofFields [.bytes 16] [Fr.ofInt 0] = some ⟨[.bytes 16], [0]⟩ := by
      simp [AV.ofFields, atomWidth, atomOfFields, atomFits, h00]
    have hf0 : fieldsOf [.bytes 16] [0] = some [0] := by
      simp [fieldsOf, fieldsOfAtom]; exact ⟨by decide, rfl⟩
    rw [LedgerState.WF] at hwf
    obtain ⟨ctx, eff, st⟩ := σ
    simp only at hctx hwf ⊢
    subst hctx
    have hi := lt_of_getElem? hb
    have hb' := getElem_of_getElem? hb
    cases hg : assocGet kv bal with
    | none =>
      vm_simp [hkey, hkv, h0, hwf, hi, hb, hb', hg, AV.ofBool, readBack_cons, hf0]
    | some v =>
      cases v with
      | cell w =>
        cases hw : fieldsOf [.bytes 16] w.atoms with
        | none => vm_simp [hkey, hkv, h0, hwf, hi, hb, hb', hg, AV.ofBool, readBack_cons, hw]
        | some ys => vm_simp [hkey, hkv, h0, hwf, hi, hb, hb', hg, AV.ofBool, readBack_cons, hw]
      | _ => vm_simp [hkey, hkv, h0, hwf, hi, hb, hb', hg, AV.ofBool, readBack_cons]

end Damp.Ledger
