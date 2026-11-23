/-
The shielded token operations of `TokensRuns.lean` under a guard of either
value (`gb`): `mintShieldedToken_runsG`, `mergeCoin_runsG`,
`mergeCoinImmediate_runsG`, `sendShielded_runsG`,
`sendImmediateShielded_runsG`.

With the guard on, each is the theorem of `TokensRuns.lean`. With it off
(the `_off` theorems), nothing is asked of the witnesses or the ledger and
nothing changes: the call completes (every `require`, cast and subtraction
under the guard passes), the private state and the ledger are as they were,
and the result means what the circuit computes from the zeros an inactive
`kernel.self()` read gives (`selfOr false`): the hashes must evaluate there
too, and every request's operands must convert (the hypotheses on keys are
the same for both guard values). A checked cast or subtraction under a guard
that is off means 0 (`Runs.castTo`, `Runs.sub`).

In the combined statements, the hashes are taken over `selfOr gb selfFs`
(the address read, or zeros), the witness answers are needed only when
`gb`, and the result, the private state and the ledger are `if gb then …
else …`.
-/
import Damp.Proofs.Ledger.TokensRuns

namespace Damp.Ledger
open Damp.IR Damp.Impact

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

section
variable {ω : Type} (H : Hooks) (p : Zkir.Prims) (w : String → List Fr → ω → Option (List Fr × ω))

/-! ## `mintShieldedToken` -/

/-- **`mintShieldedToken` under a guard that is off**: completes, changes
    nothing, and returns the coin `(nFs, ts, a)`, `ts` the token type computed
    from a zero address. -/
theorem mintShieldedToken_off (domainSep : Bytes 32) (value : Uint64) (nonce : Bytes 32)
    (recipient : Either ZswapCoinPublicKey ContractAddress) {s : Build} {st : Exec.State ω LedgerState}
    (hg : GuardIs p s st.runState false)
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
    (ts : List Fr) (htt : phashFs p tokenTypeAlign (tokenTypePre dsFs (selfOr false selfFs)) = some ts)
    (cm : List Fr) (y : Nat) (hcm : phashFs p coinPreimageAlign (ccPre (nFs ++ ts ++ [a]) u rl rr) = some cm)
    (hy : AV.ofFields [.bytes 32] cm = some (hkey y)) :
    XRuns p (oracles H (Damp.Exec.liftWitness w)) (mintShieldedToken domainSep value nonce recipient) s st True
      (fun r e w' l => Value.Is p e r (nFs ++ ts ++ [a]) ∧ w' = st.private_ ∧ l = st.ledger) := by
  have hsl := fieldsOf_bytes32_length hself
  unfold mintShieldedToken
  -- 1. `kernel.self()`
  refine (XRuns.seq (ok₂ := True) (self_runs H p w hg cfs wa selfFs hctx hc0 hself hwf)
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
  refine (XRuns.seq (ok₂ := True)
    (XRuns.val (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (s := s₁) (st := st₁) roundTrip_coin "coin" hlen hcoinE)
    (fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind Grows.currentGuard fun _ => Grows.bind (Grows.nameGuard _) fun _ => Grows.bind (Grows.underGuard _ (Grows.ledgerRead _ _)) fun _ => Grows.bind (Grows.when_ _ (Grows.ledgerOp _ _)) fun _ => Grows.pure' _)
    fun coin s₂ st₂ hn₂ hgd₂ ha₂ hQ₂ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨-, hP₂, hL₂⟩ := hQ₂.holds
  have hC₂ : Stable s₂.next st₂.env (fun e => Value.Is p e coin (nFs ++ ts ++ [a])) := hQ₂.imp fun e h => h.1
  have hg₂ := GuardIs.later hg₁ ha₂ hn₂ hgd₂
  have hA₂ : Agree s.next st.env st₂.env := ha₁.trans (ha₂.mono hn₁)
  have hn₀₂ : s.next ≤ s₂.next := Nat.le_trans hn₁ hn₂
  -- 3. `Kernel.mintShielded domainSep value`, not run
  refine (XRuns.seq (ok₂ := True)
    (XRuns.condOp (p := p) (O := oracles H (Damp.Exec.liftWitness w)) rfl (by simp) hg₂ fun e he => by
      rw [hL₂, hL₁]
      exact Kernel.mintShielded_spec H p e st.ledger es m4 domainSep value dsFs (hkey d) a hwf heff hm4
        (hds e (hA₂.trans (he.mono hn₀₂))) hd (ha e (hA₂.trans (he.mono hn₀₂))) ha64)
    (fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind Grows.currentGuard fun _ => Grows.bind (Grows.nameGuard _) fun _ => Grows.bind (Grows.underGuard _ (Grows.ledgerRead _ _)) fun _ => Grows.bind (Grows.when_ _ (Grows.ledgerOp _ _)) fun _ => Grows.pure' _)
    fun _ s₃ st₃ hn₃ hgd₃ ha₃ hQ₃ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hP₃, -, hL₃⟩ := hQ₃.holds
  simp only [Bool.false_eq_true, ite_false] at hL₃
  have hg₃ := GuardIs.later hg₂ ha₃ hn₃ hgd₃
  have hA₃ : Agree s.next st.env st₃.env := hA₂.trans (ha₃.mono hn₀₂)
  have hn₀₃ : s.next ≤ s₃.next := Nat.le_trans hn₀₂ hn₃
  have hC₃ := hC₂.later ha₃ hn₃
  have hR₃ := hr.later hA₃ hn₀₃
  -- 4. `createZswapOutput coin recipient`, not asked
  refine (XRuns.seq (ok₂ := True)
    (XRuns.askWitness0_off (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (α := Unit) rfl "createZswapOutput" hg₃)
    (fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind Grows.currentGuard fun _ => Grows.bind (Grows.nameGuard _) fun _ => Grows.bind (Grows.underGuard _ (Grows.ledgerRead _ _)) fun _ => Grows.bind (Grows.when_ _ (Grows.ledgerOp _ _)) fun _ => Grows.pure' _)
    fun _ s₄ st₄ hn₄ hgd₄ ha₄ hQ₄ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hP₄, hL₄⟩ := hQ₄.holds
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
  have hLs₆ : st₆.ledger = st.ledger := by rw [hL₆, hL₅, hL₄, hL₃, hL₂, hL₁]
  -- 7. `Kernel.claimZswapCoinSpend cm`, not run
  refine (XRuns.seq (ok₂ := True)
    (XRuns.someOp (p := p) (O := oracles H (Damp.Exec.liftWitness w)) rfl (by simp) hg₆ fun e he => by
      rw [hLs₆]
      exact Kernel.claimZswapCoinSpend_spec H p e st.ledger es m2 cmv cm (hkey y) hwf heff hm2 (hCM₆ e he) hy)
    (fun _ => Grows.bind Grows.currentGuard fun _ => Grows.bind (Grows.nameGuard _) fun _ => Grows.bind (Grows.underGuard _ (Grows.ledgerRead _ _)) fun _ => Grows.bind (Grows.when_ _ (Grows.ledgerOp _ _)) fun _ => Grows.pure' _)
    fun _ s₇ st₇ hn₇ hgd₇ ha₇ hQ₇ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hP₇, hL₇⟩ := hQ₇.holds
  simp only [Bool.false_eq_true, ite_false] at hL₇
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
  have hgv : Stable s₈.next st₈.env (fun e => (guardAnd g notLeft.expr).eval p e = some (Fr.ofBool (false && !u))) :=
    fun e he => guardAnd_eval (by rw [hgg, ← hgd₈]; exact hg₈ e he) (hNL₈ e he)
  refine (XRuns.seq (ok₂ := True)
    (XRuns.lift (O := oracles H (Damp.Exec.liftWitness w)) (st := st₈) (Runs.nameGuard (p := p) (st := st₈.runState) hgv) (Quiet.nameGuard _))
    (fun _ => Grows.bind (Grows.underGuard _ (Grows.ledgerRead _ _)) fun _ => Grows.bind (Grows.when_ _ (Grows.ledgerOp _ _)) fun _ => Grows.pure' _)
    fun g' s₉ st₉ hn₉ hgd₉ ha₉ hQ₉ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨-, hP₉, hL₉⟩ := hQ₉.holds
  have hLs₉ : st₉.ledger = st.ledger := by rw [hL₉, hL₈, hL₇, hLs₆]
  have hgu : GuardIs p { s₉ with guard := g' } st₉.runState false := fun e he => by
    have := (hQ₉ e he).1; simp only [Bool.false_and] at this; exact this
  refine (XRuns.seq (ok₂ := True)
    (XRuns.underGuard (self_runs H p w hgu cfs wa selfFs (by rw [hLs₉]; exact hctx) hc0 hself
      (by rw [hLs₉]; exact hwf)))
    (fun _ => Grows.bind (Grows.when_ _ (Grows.ledgerOp _ _)) fun _ => Grows.pure' _)
    fun me s₁₀ st₁₀ hn₁₀ hgd₁₀ ha₁₀ hQ₁₀ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hP₁₀, hL₁₀, -, -⟩ := hQ₁₀.holds
  have hg₁₀ := GuardIs.later (GuardIs.later hg₈ ha₉ hn₉ hgd₉) ha₁₀ hn₁₀ hgd₁₀
  have hR₁₀ := ((((hR₅.later ha₆ hn₆).later ha₇ hn₇).later ha₈ hn₈).later ha₉ hn₉).later ha₁₀ hn₁₀
  have hcond : Stable s₁₀.next st₁₀.env (fun e => Boolean.Is p e
      (!. recipient.isLeft &&. (recipient.right.bytes ==. me.bytes)) (!u && decide (rr = [0, 0]))) := by
    intro e he
    have hp := hparts e (hR₁₀ e he)
    have hme := (hQ₁₀ e he).2.2.1
    have heq : Boolean.Is p e (recipient.right.bytes ==. me.bytes) (decide (rr = selfOr false selfFs)) :=
      valueEq_is (p := p) hp.2.2 hme (by rw [hrr, selfOr_length hsl])
    exact Boolean.and_is (Boolean.not_is (show Boolean.Is p e recipient.isLeft u from hp.1)) heq
  have hCM₁₀ := ((((hCM₆.later ha₇ hn₇).later ha₈ hn₈).later ha₉ hn₉).later ha₁₀ hn₁₀)
  have hLs₁₀ : st₁₀.ledger = st.ledger := by rw [hL₁₀, hLs₉]
  -- 9. `if% … then Kernel.claimZswapCoinReceive cm`, not run
  refine (XRuns.seq (ok₂ := True)
    (XRuns.when_someOp (p := p) (O := oracles H (Damp.Exec.liftWitness w)) rfl (by simp) hg₁₀ hcond fun e he => by
      rw [hLs₁₀]
      exact Kernel.claimZswapCoinReceive_spec H p e st.ledger es m1 cmv cm (hkey y) hwf heff hm1 (hCM₁₀ e he) hy)
    (fun _ => Grows.pure' _)
    fun _ s₁₁ st₁₁ hn₁₁ hgd₁₁ ha₁₁ hQ₁₁ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hP₁₁, hL₁₁⟩ := hQ₁₁.holds
  simp only [Bool.false_and, Bool.false_eq_true, ite_false] at hL₁₁
  refine XRuns.pure fun e he => ⟨?_, ?_, ?_⟩
  · exact ((((((((hC₅.later ha₆ hn₆).later ha₇ hn₇).later ha₈ hn₈).later ha₉ hn₉).later ha₁₀ hn₁₀).later ha₁₁
      hn₁₁)) e he)
  · rw [hP₁₁, hP₁₀, hP₉, hP₈, hP₇, hP₆, hP₅, hP₄, hP₃, hP₂, hP₁]
  · rw [hL₁₁, hLs₁₀]

/-- **`mintShieldedToken`, under a guard meaning `gb`**: with it on, as
    `mintShieldedToken_runs`; off, `mintShieldedToken_off`. The token type is
    computed from the address read (`selfOr gb selfFs`). -/
theorem mintShieldedToken_runsG (domainSep : Bytes 32) (value : Uint64) (nonce : Bytes 32)
    (recipient : Either ZswapCoinPublicKey ContractAddress) {s : Build} {st : Exec.State ω LedgerState} {gb : Bool}
    (hg : GuardIs p s st.runState gb)
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
    (ts : List Fr) (htt : phashFs p tokenTypeAlign (tokenTypePre dsFs (selfOr gb selfFs)) = some ts)
    (cm : List Fr) (y : Nat) (hcm : phashFs p coinPreimageAlign (ccPre (nFs ++ ts ++ [a]) u rl rr) = some cm)
    (hy : AV.ofFields [.bytes 32] cm = some (hkey y))
    (ω₁ : ω) (hw₁ : gb = true → w "createZswapOutput" ((nFs ++ ts ++ [a]) ++ (Fr.ofBool u :: rl ++ rr)) st.private_ =
      some ([], ω₁)) :
    XRuns p (oracles H (Damp.Exec.liftWitness w)) (mintShieldedToken domainSep value nonce recipient) s st
      (gb = true → addOk m4 (hkey d) a.val)
      (fun r e w' l => Value.Is p e r (nFs ++ ts ++ [a]) ∧ w' = (if gb then ω₁ else st.private_) ∧
        l = (if gb then { st.ledger with effects := .array (mintSEffects es m1 m2 m4 (hkey d) a.val y
          (!u && decide (rr = selfFs))) } else st.ledger)) := by
  cases gb with
  | true =>
    exact (mintShieldedToken_runs H p w domainSep value nonce recipient hg dsFs hds d hd a ha ha64 nFs hnl hn u rl rr
      hrl hrr hsh hr cfs wa selfFs hctx hc0 hself hwf es m1 m2 m4 heff hm1 hm2 hm4 ts htt cm y hcm hy ω₁
      (hw₁ rfl)).conseq (by simp) fun _ _ _ _ h => by simpa using h
  | false =>
    exact (mintShieldedToken_off H p w domainSep value nonce recipient hg dsFs hds d hd a ha ha64 nFs hnl hn u rl rr
      hrl hrr hsh hr cfs wa selfFs hctx hc0 hself hwf es m1 m2 m4 heff hm1 hm2 hm4 ts htt cm y hcm hy).conseq
      (by simp) fun _ _ _ _ h => by simpa using h

/-! ## `mergeCoin` -/

/-- **`mergeCoin a b` under a guard that is off**: completes, changes nothing,
    and returns the coin `(nn, ac, 0)` (the checked cast of the sum means 0). -/
theorem mergeCoin_off (a b : QualifiedShieldedCoinInfo) {s : Build} {st : Exec.State ω LedgerState}
    (hg : GuardIs p s st.runState false) (an ac bn bc : List Fr) (av ai bv bi : Fr)
    (hanl : a.nonce.limbs.length = 2) (hacl : ac.length = 2) (hbcl : bc.length = 2)
    (hav : av.val < 2 ^ 128) (hbv : bv.val < 2 ^ 128)
    (ha : Stable s.next st.env (fun e => QCoinIs p e a an ac av ai))
    (hb : Stable s.next st.env (fun e => QCoinIs p e b bn bc bv bi))
    (cfs : List SV) (wa : AV) (selfFs : List Fr) (hctx : st.ledger.context = .array cfs)
    (hc0 : cfs[0]? = some (.cell wa)) (hself : fieldsOf [.bytes 32] wa.atoms = some selfFs) (hwf : st.ledger.WF)
    (es : List SV) (m0 m1 m2 : List (AV × SV)) (heff : st.ledger.effects = .array es)
    (hm0 : es[0]? = some (.map m0)) (hm1 : es[1]? = some (.map m1)) (hm2 : es[2]? = some (.map m2))
    (nfa nfb : List Fr) (xa xb : Nat)
    (hnfa : phashFs p coinPreimageAlign (cnPre (an ++ ac ++ [av]) (selfOr false selfFs)) = some nfa)
    (hxa : AV.ofFields [.bytes 32] nfa = some (hkey xa))
    (hnfb : phashFs p coinPreimageAlign (cnPre (bn ++ bc ++ [bv]) (selfOr false selfFs)) = some nfb)
    (hxb : AV.ofFields [.bytes 32] nfb = some (hkey xb))
    (cm : List Fr) (y : Nat)
    (hcm : phashFs p coinPreimageAlign (ccPre (derivedNonceFs p "midnight:kernel:nonce_evolve" an ++ ac ++
      [Fr.ofNat 0]) false [0, 0] (selfOr false selfFs)) = some cm)
    (hy : AV.ofFields [.bytes 32] cm = some (hkey y)) :
    XRuns p (oracles H (Damp.Exec.liftWitness w)) (mergeCoin a b) s st True
      (fun r e w' l => Value.Is p e r (derivedNonceFs p "midnight:kernel:nonce_evolve" an ++ ac ++ [Fr.ofNat 0]) ∧
        w' = st.private_ ∧ l = st.ledger) := by
  have hsl := fieldsOf_bytes32_length hself
  let σ := st.ledger
  let nn := derivedNonceFs p "midnight:kernel:nonce_evolve" an
  let vv := av.val + bv.val
  let sF := selfOr false selfFs
  -- 1. `const selfAddr ← Kernel.self`
  have h1 : XRuns p (oracles H (Damp.Exec.liftWitness w)) (valM Kernel.self "selfAddr") s st True
      (fun r e w' l => Value.Is p e r sF ∧ w' = st.private_ ∧ l = σ ∧ Value.Shaped r) := by
    unfold valM
    refine (XRuns.seq (ok₂ := True) (self_runs H p w hg cfs wa selfFs hctx hc0 hself hwf)
      (fun _ => Grows.val _ _) fun x s₁ st₁ hn₁ hgd₁ ha₁ hQ₁ => ?_).conseq (by simp) fun _ _ _ _ h => h
    obtain ⟨hw₁, hl₁, -, hsh₁⟩ := hQ₁.holds
    have hlen : (Value.toExprs x).length = Value.width ContractAddress := ContractAddress.shaped_len hsh₁
    exact ((XRuns.val (p := p) (O := oracles H (Damp.Exec.liftWitness w)) roundTrip_contractAddress "selfAddr" hlen
      (hQ₁.imp fun e h => h.2.2.1)).addResult (val_shaped x "selfAddr" s₁ hlen)).conseq Iff.rfl
      fun r e w' l h => ⟨h.1.1, h.1.2.1.trans hw₁, h.1.2.2.trans hl₁, h.2⟩
  unfold mergeCoin
  refine (XRuns.seq (ok₂ := True) h1
    (fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.require _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.castTo _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _)
    fun selfAddr s₁ st₁ hn₁ hgd₁ ha₁ hQ₁ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨-, hP₁, hL₁, hshS⟩ := hQ₁.holds
  have hS₁ : Stable s₁.next st₁.env (fun e => Value.Is p e selfAddr sF) := hQ₁.imp fun e h => h.1
  have hg₁ := GuardIs.later hg ha₁ hn₁ hgd₁
  have ha₁' := ha.later ha₁ hn₁
  have hb₁' := hb.later ha₁ hn₁
  -- 2. `createZswapInput a`, not asked
  refine (XRuns.seq (ok₂ := True)
    (XRuns.askWitness0_off (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (α := Unit) rfl "createZswapInput" hg₁)
    (fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.require _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.castTo _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _)
    fun _ s₂ st₂ hn₂ hgd₂ ha₂ hQ₂ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hP₂, hL₂⟩ := hQ₂.holds
  have hg₂ := GuardIs.later hg₁ ha₂ hn₂ hgd₂
  have hS₂ := hS₁.later ha₂ hn₂
  have ha₂' := ha₁'.later ha₂ hn₂
  have hb₂' := hb₁'.later ha₂ hn₂
  -- 3. `claimZswapNullifier (coinNullifier a selfAddr)`, not run
  refine (XRuns.seq (ok₂ := True)
    (XRuns.someOp (p := p) (O := oracles H (Damp.Exec.liftWitness w)) rfl (by simp) hg₂ fun e he => by
      rw [hL₂, hL₁]
      exact Kernel.claimZswapNullifier_spec H p e σ es m0 _ nfa (hkey xa) hwf heff hm0
        (coinNullifier_is (ha₂' e he).down (hS₂ e he) hnfa) hxa)
    (fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.require _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.castTo _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _)
    fun _ s₃ st₃ hn₃ hgd₃ ha₃ hQ₃ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hP₃, hL₃⟩ := hQ₃.holds
  simp only [Bool.false_eq_true, ite_false] at hL₃
  have hg₃ := GuardIs.later hg₂ ha₃ hn₃ hgd₃
  have hS₃ := hS₂.later ha₃ hn₃
  have ha₃' := ha₂'.later ha₃ hn₃
  have hb₃' := hb₂'.later ha₃ hn₃
  -- 4. `createZswapInput b`, not asked
  refine (XRuns.seq (ok₂ := True)
    (XRuns.askWitness0_off (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (α := Unit) rfl "createZswapInput" hg₃)
    (fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.require _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.castTo _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _)
    fun _ s₄ st₄ hn₄ hgd₄ ha₄ hQ₄ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hP₄, hL₄⟩ := hQ₄.holds
  have hg₄ := GuardIs.later hg₃ ha₄ hn₄ hgd₄
  have hS₄ := hS₃.later ha₄ hn₄
  have ha₄' := ha₃'.later ha₄ hn₄
  have hb₄' := hb₃'.later ha₄ hn₄
  -- 5. `claimZswapNullifier (coinNullifier b selfAddr)`, not run
  refine (XRuns.seq (ok₂ := True)
    (XRuns.someOp (p := p) (O := oracles H (Damp.Exec.liftWitness w)) rfl (by simp) hg₄ fun e he => by
      rw [hL₄, hL₃, hL₂, hL₁]
      exact Kernel.claimZswapNullifier_spec H p e σ es m0 _ nfb (hkey xb) hwf heff hm0
        (coinNullifier_is (hb₄' e he).down (hS₄ e he) hnfb) hxb)
    (fun _ => Grows.bind (Grows.require _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.castTo _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _)
    fun _ s₅ st₅ hn₅ hgd₅ ha₅ hQ₅ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hP₅, hL₅⟩ := hQ₅.holds
  simp only [Bool.false_eq_true, ite_false] at hL₅
  have hg₅ := GuardIs.later hg₄ ha₅ hn₅ hgd₅
  have hS₅ := hS₄.later ha₅ hn₅
  have ha₅' := ha₄'.later ha₅ hn₅
  have hb₅' := hb₄'.later ha₅ hn₅
  -- 6. `require (a.color ==. b.color)`, passes
  have hcolor : Stable s₅.next st₅.env (fun e => Boolean.Is p e (a.color ==. b.color) (decide (ac = bc))) :=
    fun e he => valueEq_is (p := p) (ha₅' e he).color (hb₅' e he).color (by rw [hacl, hbcl])
  refine (XRuns.seq (ok₂ := True)
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
  refine (XRuns.seq (ok₂ := True)
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
  -- 8. `(a.value + b.value).castTo (2^128 - 1)`, means 0
  have hsum : Stable s₇.next st₇.env (fun e => Uint.Means p e (a.value + b.value) vv) := fun e he =>
    Uint.add_means (by decide) (uint128_means p (ha₇' e he).value hav) (uint128_means p (hb₇' e he).value hbv)
  refine (XRuns.seq (ok₂ := True)
    (XRuns.lift (O := oracles H (Damp.Exec.liftWitness w)) (st := st₇) (Runs.castTo (p := p) (st := st₇.runState) uint128_bound hg₇ hsum)
      (Quiet.castTo _ _))
    (fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _)
    fun value s₈ st₈ hn₈ hgd₈ ha₈ hQ₈ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨-, hP₈, hL₈⟩ := hQ₈.holds
  have hV₈ : Stable s₈.next st₈.env (fun e => Uint.Means p e value 0) := hQ₈.imp fun e h => by
    simpa using h.1
  have hg₈ := GuardIs.later hg₇ ha₈ hn₈ hgd₈
  have hS₈ := hS₇.later ha₈ hn₈
  have ha₈' := ha₇'.later ha₈ hn₈
  have hN₈ := hN₇.later ha₈ hn₈
  have hcoin : Stable s₈.next st₈.env (fun e => Value.Is p e
      ({ nonce := nonce, color := a.color, value := value } : ShieldedCoinInfo) (nn ++ ac ++ [Fr.ofNat 0])) := by
    intro e he
    unfold Value.Is
    show Expr.evalList p e (nonce.limbs ++ (a.color.limbs ++ ([value.expr] ++ []))) = _
    rw [show nn ++ ac ++ [Fr.ofNat 0] = nn ++ (ac ++ [Fr.ofNat 0]) by simp]
    exact evalList_append_some (hN₈ e he) (evalList_append_some (ha₈' e he).color
      (by simp [Expr.evalList, (hV₈ e he).eval]))
  -- 9. `createZswapOutput newCoin (right selfAddr)`, not asked
  refine (XRuns.seq (ok₂ := True)
    (XRuns.askWitness0_off (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (α := Unit) rfl "createZswapOutput" hg₈)
    (fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _)
    fun _ s₉ st₉ hn₉ hgd₉ ha₉ hQ₉ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hP₉, hL₉⟩ := hQ₉.holds
  have hg₉ := GuardIs.later hg₈ ha₉ hn₉ hgd₉
  have hcoin₉ := hcoin.later ha₉ hn₉
  have hS₉ := hS₈.later ha₉ hn₉
  have hshR : (Value.toExprs (right selfAddr : Either ZswapCoinPublicKey ContractAddress).left).length = 2 ∧
      (Value.toExprs (right selfAddr : Either ZswapCoinPublicKey ContractAddress).right).length = 2 :=
    ⟨rfl, ContractAddress.shaped_len hshS⟩
  -- 10. `const cm := coinCommitment newCoin (right selfAddr)`
  refine (XRuns.seq (ok₂ := True)
    (XRuns.val (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (s := s₉) (st := st₉) roundTrip_bytes (xs := cm) "cm" rfl
      fun e he => coinCommitment_is (hcoin₉ e he) hshR rfl (right_self_is p (hS₉ e he)) hcm)
    (fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _)
    fun cmv s₁₀ st₁₀ hn₁₀ hgd₁₀ ha₁₀ hQ₁₀ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨-, hP₁₀, hL₁₀⟩ := hQ₁₀.holds
  have hC₁₀ : Stable s₁₀.next st₁₀.env (fun e => Value.Is p e cmv cm) := hQ₁₀.imp fun e h => h.1
  have hg₁₀ := GuardIs.later hg₉ ha₁₀ hn₁₀ hgd₁₀
  have hcoin₁₀ := hcoin₉.later ha₁₀ hn₁₀
  have hLs : st₁₀.ledger = σ := by rw [hL₁₀, hL₉, hL₈, hL₇, hL₆, hL₅, hL₄, hL₃, hL₂, hL₁]
  -- 11. `claimZswapCoinSpend cm`, not run
  refine (XRuns.seq (ok₂ := True)
    (XRuns.someOp (p := p) (O := oracles H (Damp.Exec.liftWitness w)) rfl (by simp) hg₁₀ fun e he => by
      rw [hLs]
      exact Kernel.claimZswapCoinSpend_spec H p e σ es m2 cmv cm (hkey y) hwf heff hm2 (hC₁₀ e he) hy)
    (fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _)
    fun _ s₁₁ st₁₁ hn₁₁ hgd₁₁ ha₁₁ hQ₁₁ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hP₁₁, hL₁₁⟩ := hQ₁₁.holds
  simp only [Bool.false_eq_true, ite_false] at hL₁₁
  have hg₁₁ := GuardIs.later hg₁₀ ha₁₁ hn₁₁ hgd₁₁
  -- 12. `claimZswapCoinReceive cm`, not run
  refine (XRuns.seq (ok₂ := True)
    (XRuns.someOp (p := p) (O := oracles H (Damp.Exec.liftWitness w)) rfl (by simp) hg₁₁ fun e he => by
      rw [hL₁₁, hLs]
      exact Kernel.claimZswapCoinReceive_spec H p e σ es m1 cmv cm (hkey y) hwf heff hm1
        ((hC₁₀.later ha₁₁ hn₁₁) e he) hy)
    (fun _ => Grows.pure' _)
    fun _ s₁₂ st₁₂ hn₁₂ hgd₁₂ ha₁₂ hQ₁₂ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hP₁₂, hL₁₂⟩ := hQ₁₂.holds
  simp only [Bool.false_eq_true, ite_false] at hL₁₂
  -- 13. `return newCoin`
  refine XRuns.pure fun e he => ⟨((hcoin₁₀.later ha₁₁ hn₁₁).later ha₁₂ hn₁₂) e he, ?_, ?_⟩
  · rw [hP₁₂, hP₁₁, hP₁₀, hP₉, hP₈, hP₇, hP₆, hP₅, hP₄, hP₃, hP₂, hP₁]
  · rw [hL₁₂, hL₁₁, hLs]

/-- **`mergeCoin a b`, under a guard meaning `gb`**: with it on, as
    `mergeCoin_runs`; off, `mergeCoin_off`. -/
theorem mergeCoin_runsG (a b : QualifiedShieldedCoinInfo) {s : Build} {st : Exec.State ω LedgerState} {gb : Bool}
    (hg : GuardIs p s st.runState gb) (an ac bn bc : List Fr) (av ai bv bi : Fr)
    (hanl : a.nonce.limbs.length = 2) (hacl : ac.length = 2) (hbcl : bc.length = 2)
    (hav : av.val < 2 ^ 128) (hbv : bv.val < 2 ^ 128)
    (ha : Stable s.next st.env (fun e => QCoinIs p e a an ac av ai))
    (hb : Stable s.next st.env (fun e => QCoinIs p e b bn bc bv bi))
    (cfs : List SV) (wa : AV) (selfFs : List Fr) (hctx : st.ledger.context = .array cfs)
    (hc0 : cfs[0]? = some (.cell wa)) (hself : fieldsOf [.bytes 32] wa.atoms = some selfFs) (hwf : st.ledger.WF)
    (es : List SV) (m0 m1 m2 : List (AV × SV)) (heff : st.ledger.effects = .array es)
    (hm0 : es[0]? = some (.map m0)) (hm1 : es[1]? = some (.map m1)) (hm2 : es[2]? = some (.map m2))
    (nfa nfb : List Fr) (xa xb : Nat)
    (hnfa : phashFs p coinPreimageAlign (cnPre (an ++ ac ++ [av]) (selfOr gb selfFs)) = some nfa)
    (hxa : AV.ofFields [.bytes 32] nfa = some (hkey xa))
    (hnfb : phashFs p coinPreimageAlign (cnPre (bn ++ bc ++ [bv]) (selfOr gb selfFs)) = some nfb)
    (hxb : AV.ofFields [.bytes 32] nfb = some (hkey xb))
    (cm : List Fr) (y : Nat)
    (hcm : phashFs p coinPreimageAlign (ccPre (derivedNonceFs p "midnight:kernel:nonce_evolve" an ++ ac ++
      [Fr.ofNat (if gb then av.val + bv.val else 0)]) false [0, 0] (selfOr gb selfFs)) = some cm)
    (hy : AV.ofFields [.bytes 32] cm = some (hkey y))
    (ω₁ ω₂ ω₃ : ω)
    (hw₁ : gb = true → w "createZswapInput" (an ++ ac ++ [av, ai]) st.private_ = some ([], ω₁))
    (hw₂ : gb = true → w "createZswapInput" (bn ++ bc ++ [bv, bi]) ω₁ = some ([], ω₂))
    (hw₃ : gb = true → w "createZswapOutput" ((derivedNonceFs p "midnight:kernel:nonce_evolve" an ++ ac ++
      [Fr.ofNat (av.val + bv.val)]) ++ (Fr.ofBool false :: [0, 0] ++ selfFs)) ω₂ = some ([], ω₃)) :
    XRuns p (oracles H (Damp.Exec.liftWitness w)) (mergeCoin a b) s st (gb = true → ac = bc ∧ av.val + bv.val < 2 ^ 128)
      (fun r e w' l => Value.Is p e r (derivedNonceFs p "midnight:kernel:nonce_evolve" an ++ ac ++
          [Fr.ofNat (if gb then av.val + bv.val else 0)]) ∧ w' = (if gb then ω₃ else st.private_) ∧
        l = (if gb then { st.ledger with effects := .array (mergeEffects es m0 m1 m2 xa xb y) } else st.ledger)) := by
  cases gb with
  | true =>
    exact (mergeCoin_runs H p w a b hg an ac bn bc av ai bv bi hanl hacl hbcl hav hbv ha hb cfs wa selfFs hctx hc0
      hself hwf es m0 m1 m2 heff hm0 hm1 hm2 nfa nfb xa xb (by simpa [selfOr] using hnfa) hxa
      (by simpa [selfOr] using hnfb) hxb cm y (by simpa [selfOr] using hcm) hy ω₁ ω₂ ω₃ (hw₁ rfl) (hw₂ rfl)
      (hw₃ rfl)).conseq (by simp) fun _ _ _ _ h => by simpa using h
  | false =>
    exact (mergeCoin_off H p w a b hg an ac bn bc av ai bv bi hanl hacl hbcl hav hbv ha hb cfs wa selfFs hctx hc0
      hself hwf es m0 m1 m2 heff hm0 hm1 hm2 nfa nfb xa xb hnfa hxa hnfb hxb cm y (by simpa using hcm) hy).conseq
      (by simp) fun _ _ _ _ h => by simpa using h

/-- **`mergeCoinImmediate a b`, under a guard meaning `gb`**: `mergeCoin_runsG`
    with the second coin at Merkle index 0. -/
theorem mergeCoinImmediate_runsG (a : QualifiedShieldedCoinInfo) (b : ShieldedCoinInfo) {s : Build}
    {st : Exec.State ω LedgerState} {gb : Bool}
    (hg : GuardIs p s st.runState gb) (an ac bn bc : List Fr) (av ai bv : Fr)
    (hanl : a.nonce.limbs.length = 2) (hacl : ac.length = 2) (hbcl : bc.length = 2)
    (hav : av.val < 2 ^ 128) (hbv : bv.val < 2 ^ 128)
    (ha : Stable s.next st.env (fun e => QCoinIs p e a an ac av ai))
    (hb : Stable s.next st.env (fun e => CoinIs p e b bn bc bv))
    (cfs : List SV) (wa : AV) (selfFs : List Fr) (hctx : st.ledger.context = .array cfs)
    (hc0 : cfs[0]? = some (.cell wa)) (hself : fieldsOf [.bytes 32] wa.atoms = some selfFs) (hwf : st.ledger.WF)
    (es : List SV) (m0 m1 m2 : List (AV × SV)) (heff : st.ledger.effects = .array es)
    (hm0 : es[0]? = some (.map m0)) (hm1 : es[1]? = some (.map m1)) (hm2 : es[2]? = some (.map m2))
    (nfa nfb : List Fr) (xa xb : Nat)
    (hnfa : phashFs p coinPreimageAlign (cnPre (an ++ ac ++ [av]) (selfOr gb selfFs)) = some nfa)
    (hxa : AV.ofFields [.bytes 32] nfa = some (hkey xa))
    (hnfb : phashFs p coinPreimageAlign (cnPre (bn ++ bc ++ [bv]) (selfOr gb selfFs)) = some nfb)
    (hxb : AV.ofFields [.bytes 32] nfb = some (hkey xb))
    (cm : List Fr) (y : Nat)
    (hcm : phashFs p coinPreimageAlign (ccPre (derivedNonceFs p "midnight:kernel:nonce_evolve" an ++ ac ++
      [Fr.ofNat (if gb then av.val + bv.val else 0)]) false [0, 0] (selfOr gb selfFs)) = some cm)
    (hy : AV.ofFields [.bytes 32] cm = some (hkey y))
    (ω₁ ω₂ ω₃ : ω)
    (hw₁ : gb = true → w "createZswapInput" (an ++ ac ++ [av, ai]) st.private_ = some ([], ω₁))
    (hw₂ : gb = true → w "createZswapInput" (bn ++ bc ++ [bv, 0]) ω₁ = some ([], ω₂))
    (hw₃ : gb = true → w "createZswapOutput" ((derivedNonceFs p "midnight:kernel:nonce_evolve" an ++ ac ++
      [Fr.ofNat (av.val + bv.val)]) ++ (Fr.ofBool false :: [0, 0] ++ selfFs)) ω₂ = some ([], ω₃)) :
    XRuns p (oracles H (Damp.Exec.liftWitness w)) (mergeCoinImmediate a b) s st (gb = true → ac = bc ∧ av.val + bv.val < 2 ^ 128)
      (fun r e w' l => Value.Is p e r (derivedNonceFs p "midnight:kernel:nonce_evolve" an ++ ac ++
          [Fr.ofNat (if gb then av.val + bv.val else 0)]) ∧ w' = (if gb then ω₃ else st.private_) ∧
        l = (if gb then { st.ledger with effects := .array (mergeEffects es m0 m1 m2 xa xb y) } else st.ledger)) :=
  mergeCoin_runsG H p w a { nonce := b.nonce, color := b.color, value := b.value, mt_index := 0 } hg an ac bn bc av ai
    bv 0 hanl hacl hbcl hav hbv ha
    (hb.imp fun e h => ⟨h.nonce, h.color, h.value, by
      show (Uint.capped 18446744073709551615 (.const 0)).eval p e = some 0
      rw [Uint.capped_eval uint64_bound]; rfl⟩)
    cfs wa selfFs hctx hc0 hself hwf es m0 m1 m2 heff hm0 hm1 hm2 nfa nfb xa xb hnfa hxa hnfb hxb cm y hcm hy
    ω₁ ω₂ ω₃ hw₁ hw₂ hw₃

/-! ## `sendShielded` -/

/-- **`sendShielded input recipient value` under a guard that is off**:
    completes, changes nothing, and returns `(none, outFs)`: the checked
    subtraction means 0, so the `cond` takes the no-change branch. -/
theorem sendShielded_off (input : QualifiedShieldedCoinInfo) (recipient : Either ZswapCoinPublicKey ContractAddress)
    (value : Uint128) {s : Build} {st : Exec.State ω LedgerState} (hg : GuardIs p s st.runState false)
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
    (nf : List Fr) (x : Nat)
    (hnf : phashFs p coinPreimageAlign (cnPre (n ++ c ++ [v]) (selfOr false selfFs)) = some nf)
    (hx : AV.ofFields [.bytes 32] nf = some (hkey x))
    (cm : List Fr) (y : Nat)
    (hcm : phashFs p coinPreimageAlign (ccPre (derivedNonceFs p "midnight:kernel:nonce_evolve" n ++ c ++
      [Fr.ofNat k]) u rl rr) = some cm)
    (hy : AV.ofFields [.bytes 32] cm = some (hkey y))
    (cm₂ : List Fr) (z : Nat)
    (hcm₂ : phashFs p coinPreimageAlign (ccPre (derivedNonceFs p "midnight:kernel:nonce_evolve/2" n ++ c ++
      [Fr.ofNat 0]) false [0, 0] (selfOr false selfFs)) = some cm₂)
    (hz : AV.ofFields [.bytes 32] cm₂ = some (hkey z)) :
    XRuns p (oracles H (Damp.Exec.liftWitness w)) (sendShielded input recipient value) s st True
      (fun r e w' l => Value.Is p e r ((Fr.ofBool false :: List.replicate (Value.width ShieldedCoinInfo) 0) ++
            (derivedNonceFs p "midnight:kernel:nonce_evolve" n ++ c ++ [Fr.ofNat k])) ∧
        w' = st.private_ ∧ l = st.ledger) := by
  have hsl := fieldsOf_bytes32_length hself
  let σ := st.ledger
  let outFs := derivedNonceFs p "midnight:kernel:nonce_evolve" n ++ c ++ [Fr.ofNat k]
  let chFs := derivedNonceFs p "midnight:kernel:nonce_evolve/2" n ++ c ++ [Fr.ofNat 0]
  let sF := selfOr false selfFs
  -- 1. `const selfAddr ← Kernel.self`
  have h1 : XRuns p (oracles H (Damp.Exec.liftWitness w)) (valM Kernel.self "selfAddr") s st True
      (fun r e w' l => Value.Is p e r sF ∧ w' = st.private_ ∧ l = σ ∧ Value.Shaped r) := by
    unfold valM
    refine (XRuns.seq (ok₂ := True) (self_runs H p w hg cfs wa selfFs hctx hc0 hself hwf)
      (fun _ => Grows.val _ _) fun x s₁ st₁ hn₁ hgd₁ ha₁ hQ₁ => ?_).conseq (by simp) fun _ _ _ _ h => h
    obtain ⟨hw₁, hl₁, -, hsh₁⟩ := hQ₁.holds
    have hlen : (Value.toExprs x).length = Value.width ContractAddress := ContractAddress.shaped_len hsh₁
    exact ((XRuns.val (p := p) (O := oracles H (Damp.Exec.liftWitness w)) roundTrip_contractAddress "selfAddr" hlen
      (hQ₁.imp fun e h => h.2.2.1)).addResult (val_shaped x "selfAddr" s₁ hlen)).conseq Iff.rfl
      fun r e w' l h => ⟨h.1.1, h.1.2.1.trans hw₁, h.1.2.2.trans hl₁, h.2⟩
  unfold sendShielded
  refine (XRuns.seq (ok₂ := True) h1
    (fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.valM (Grows.sub _ _) _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.when_ _ (Grows.ledgerOp _ _)) fun _ => Grows.cond _ (Grows.pure' _) (Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _))
    fun selfAddr s₁ st₁ hn₁ hgd₁ ha₁ hQ₁ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨-, hP₁, hL₁, hshS⟩ := hQ₁.holds
  have hS₁ : Stable s₁.next st₁.env (fun e => Value.Is p e selfAddr sF) := hQ₁.imp fun e h => h.1
  have hg₁ := GuardIs.later hg ha₁ hn₁ hgd₁
  have hin₁ := hin.later ha₁ hn₁
  -- 2. `createZswapInput input`, not asked
  refine (XRuns.seq (ok₂ := True)
    (XRuns.askWitness0_off (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (α := Unit) rfl "createZswapInput" hg₁)
    (fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.valM (Grows.sub _ _) _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.when_ _ (Grows.ledgerOp _ _)) fun _ => Grows.cond _ (Grows.pure' _) (Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _))
    fun _ s₂ st₂ hn₂ hgd₂ ha₂ hQ₂ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hP₂, hL₂⟩ := hQ₂.holds
  have hg₂ := GuardIs.later hg₁ ha₂ hn₂ hgd₂
  have hS₂ := hS₁.later ha₂ hn₂
  have hin₂ := hin₁.later ha₂ hn₂
  -- 3. `claimZswapNullifier (coinNullifier input selfAddr)`, not run
  refine (XRuns.seq (ok₂ := True)
    (XRuns.someOp (p := p) (O := oracles H (Damp.Exec.liftWitness w)) rfl (by simp) hg₂ fun e he => by
      rw [hL₂, hL₁]
      exact Kernel.claimZswapNullifier_spec H p e σ es m0 _ nf (hkey x) hwf heff hm0
        (coinNullifier_is (hin₂ e he).down (hS₂ e he) hnf) hx)
    (fun _ => Grows.bind (Grows.valM (Grows.sub _ _) _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.when_ _ (Grows.ledgerOp _ _)) fun _ => Grows.cond _ (Grows.pure' _) (Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _))
    fun _ s₃ st₃ hn₃ hgd₃ ha₃ hQ₃ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hP₃, hL₃⟩ := hQ₃.holds
  simp only [Bool.false_eq_true, ite_false] at hL₃
  have hg₃ := GuardIs.later hg₂ ha₃ hn₃ hgd₃
  have hA₃ : Agree s.next st.env st₃.env := ha₁.trans ((ha₂.mono hn₁).trans (ha₃.mono (Nat.le_trans hn₁ hn₂)))
  have hn₀₃ : s.next ≤ s₃.next := Nat.le_trans hn₁ (Nat.le_trans hn₂ hn₃)
  have hin₃ := hin₂.later ha₃ hn₃
  have hk₃ := hk.later hA₃ hn₀₃
  -- 4. `const change ← input.value.sub value`, means 0
  have h4 : XRuns p (oracles H (Damp.Exec.liftWitness w)) (valM (input.value.sub value) "change") s₃ st₃ True
      (fun r e w' l => Uint.Means p e r 0 ∧ w' = st₃.private_ ∧ l = st₃.ledger) := by
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
  have hCh₄ : Stable s₄.next st₄.env (fun e => Uint.Means p e change 0) := hQ₄.imp fun e h => h.1
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
  -- 6. `createZswapOutput output recipient`, not asked
  refine (XRuns.seq (ok₂ := True)
    (XRuns.askWitness0_off (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (α := Unit) rfl "createZswapOutput" hg₅)
    (fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.when_ _ (Grows.ledgerOp _ _)) fun _ => Grows.cond _ (Grows.pure' _) (Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _))
    fun _ s₆ st₆ hn₆ hgd₆ ha₆ hQ₆ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hP₆, hL₆⟩ := hQ₆.holds
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
  have hLs₇ : st₇.ledger = σ := by rw [hL₇, hL₆, hL₅, hL₄, hL₃, hL₂, hL₁]
  -- 8. `Kernel.claimZswapCoinSpend cm`, not run
  refine (XRuns.seq (ok₂ := True)
    (XRuns.someOp (p := p) (O := oracles H (Damp.Exec.liftWitness w)) rfl (by simp) hg₇ fun e he => by
      rw [hLs₇]
      exact Kernel.claimZswapCoinSpend_spec H p e σ es m2 cmv cm (hkey y) hwf heff hm2 (hCM₇ e he) hy)
    (fun _ => Grows.bind (Grows.when_ _ (Grows.ledgerOp _ _)) fun _ => Grows.cond _ (Grows.pure' _) (Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _))
    fun _ s₈ st₈ hn₈ hgd₈ ha₈ hQ₈ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hP₈, hL₈⟩ := hQ₈.holds
  simp only [Bool.false_eq_true, ite_false] at hL₈
  have hg₈ := GuardIs.later hg₇ ha₈ hn₈ hgd₈
  have hparts : ∀ e, Value.Is p e recipient (Fr.ofBool u :: rl ++ rr) →
      recipient.isLeft.expr.eval p e = some (Fr.ofBool u) ∧ Value.Is p e recipient.left rl ∧
        Value.Is p e recipient.right rr := fun e h => either_is (by rw [hsh.1, hrl]) h
  have hR₈ := (hR₆.later ha₇ hn₇).later ha₈ hn₈
  have hS₈ := ((((((hS₂.later ha₃ hn₃).later ha₄ hn₄).later ha₅ hn₅).later ha₆ hn₆).later ha₇ hn₇).later ha₈ hn₈)
  have hcond : Stable s₈.next st₈.env (fun e => Boolean.Is p e
      (!. recipient.isLeft &&. (recipient.right.bytes ==. selfAddr.bytes)) (!u && decide (rr = sF))) := by
    intro e he
    have hp := hparts e (hR₈ e he)
    have heq : Boolean.Is p e (recipient.right.bytes ==. selfAddr.bytes) (decide (rr = sF)) :=
      valueEq_is (p := p) hp.2.2 (hS₈ e he) (by rw [hrr, selfOr_length hsl])
    exact Boolean.and_is (Boolean.not_is (show Boolean.Is p e recipient.isLeft u from hp.1)) heq
  have hCM₈ := hCM₇.later ha₈ hn₈
  -- 9. `if% … then Kernel.claimZswapCoinReceive cm`, not run
  refine (XRuns.seq (ok₂ := True)
    (XRuns.when_someOp (p := p) (O := oracles H (Damp.Exec.liftWitness w)) rfl (by simp) hg₈ hcond fun e he => by
      rw [hL₈, hLs₇]
      exact Kernel.claimZswapCoinReceive_spec H p e σ es m1 cmv cm (hkey y) hwf heff hm1 (hCM₈ e he) hy)
    (fun _ => Grows.cond _ (Grows.pure' _) (Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _))
    fun _ s₉ st₉ hn₉ hgd₉ ha₉ hQ₉ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hP₉, hL₉⟩ := hQ₉.holds
  simp only [Bool.false_and, Bool.false_eq_true, ite_false] at hL₉
  have hLs₉ : st₉.ledger = σ := by rw [hL₉, hL₈, hLs₇]
  have hg₉ := GuardIs.later hg₈ ha₉ hn₉ hgd₉
  have hPs₉ : st₉.private_ = st.private_ := by rw [hP₉, hP₈, hP₇, hP₆, hP₅, hP₄, hP₃, hP₂, hP₁]
  have hA₉ : Agree s₅.next st₅.env st₉.env :=
    ha₆.trans ((ha₇.mono hn₆).trans ((ha₈.mono (Nat.le_trans hn₆ hn₇)).trans
      (ha₉.mono (Nat.le_trans hn₆ (Nat.le_trans hn₇ hn₈)))))
  have hn₅₉ : s₅.next ≤ s₉.next := Nat.le_trans hn₆ (Nat.le_trans hn₇ (Nat.le_trans hn₈ hn₉))
  have hCh₉ := (hCh₄.later ha₅ hn₅).later hA₉ hn₅₉
  have hin₉ := (hin₄.later ha₅ hn₅).later hA₉ hn₅₉
  have hO₉ := hO₅.later hA₉ hn₅₉
  have hS₉ := hS₈.later ha₉ hn₉
  have hc : Stable s₉.next st₉.env (fun e => Boolean.Is p e (change ==. (0 : Uint128)) (decide ((0 : Nat) = 0))) :=
    fun e he => cmpEq_means (hCh₉ e he) (Uint.numeral_means (by decide) uint128_bound)
  let noneFs := Fr.ofBool false :: List.replicate (Value.width ShieldedCoinInfo) 0
  have hshR : (Value.toExprs (right selfAddr : Either ZswapCoinPublicKey ContractAddress).left).length = 2 ∧
      (Value.toExprs (right selfAddr : Either ZswapCoinPublicKey ContractAddress).right).length = 2 :=
    ⟨rfl, ContractAddress.shaped_len hshS⟩
  -- 10. `cond (change ==. 0) (pure (none, output)) (…)`: both branches under guards that are off
  refine (XRuns.cond (α := ShieldedSendResult) (gb := false) (cb := decide ((0 : Nat) = 0))
    (Qt := fun a env w' l => Value.Is p env a (noneFs ++ (outFs ++ [])) ∧ w' = st.private_ ∧ l = σ)
    (Qe := fun a b env w' l => Value.Is p env a (noneFs ++ (outFs ++ [])) ∧
      Value.Is p env b ((Fr.ofBool true :: chFs) ++ (outFs ++ [])) ∧ w' = st.private_ ∧ l = σ)
    (okt := True) (oke := True) hg₉ hc (Grows.pure' _) (Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.askWitness _ _ _) fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _) ?_ ?_).conseq (by simp) ?_
  · intro s' st' ctx
    refine XRuns.pure fun e he => ⟨?_, ctx.2.2.1.trans hPs₉, ctx.2.2.2.1.trans hLs₉⟩
    unfold Value.Is
    exact evalList_append_some (Maybe.none_is roundTrip_coin) (evalList_append_some ((ctx.transfer hO₉) e he) rfl)
  · intro a s' st' hn' hA' hgd' hQt
    obtain ⟨-, hPt, hLt⟩ := hQt.holds
    have hin' := hin₉.later hA' hn'
    have hCh' := hCh₉.later hA' hn'
    have hS' := hS₉.later hA' hn'
    have hg'' : GuardIs p s' st'.runState false := by simpa using hgd'
    -- e1. `const changeCoin := …`
    have hcc : Stable s'.next st'.env (fun e => Value.Is p e
        ({ nonce := upgradeFromTransient (transientHash (#v[Field.ofString "midnight:kernel:nonce_evolve/2",
            degradeToTransient input.nonce] : Vector Field 2)), color := input.color, value := change } :
          ShieldedCoinInfo) chFs) := by
      intro e he
      unfold Value.Is
      show Expr.evalList p e (_ ++ (input.color.limbs ++ ([change.expr] ++ []))) = _
      rw [show chFs = derivedNonceFs p "midnight:kernel:nonce_evolve/2" n ++ (c ++ [Fr.ofNat 0]) by simp [chFs]]
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
    -- e2. `createZswapOutput changeCoin (right selfAddr)`, not asked
    refine (XRuns.seq (ok₂ := True)
      (XRuns.askWitness0_off (p := p) (O := oracles H (Damp.Exec.liftWitness w)) (α := Unit) rfl "createZswapOutput" hgu₁)
      (fun _ => Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _)
      fun _ t₂ u₂ hm₂ hgt₂ hb₂ hR₂ => ?_).conseq (by simp) fun _ _ _ _ h => h
    obtain ⟨hQP₂, hQL₂⟩ := hR₂.holds
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
    have hLu₃ : u₃.ledger = σ := by rw [hQL₃, hQL₂, hQL₁, hLt]
    -- e4, e5. the two claims, not run
    refine (XRuns.seq (ok₂ := True)
      (XRuns.someOp (p := p) (O := oracles H (Damp.Exec.liftWitness w)) rfl (by simp) hgu₃ fun e he => by
        rw [hLu₃]
        exact Kernel.claimZswapCoinSpend_spec H p e σ es m2 cmv₂ cm₂ (hkey z) hwf heff hm2 (hCM₃ e he) hz)
      (fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _)
      fun _ t₄ u₄ hm₄ hgt₄ hb₄ hR₄ => ?_).conseq (by simp) fun _ _ _ _ h => h
    obtain ⟨hQP₄, hQL₄⟩ := hR₄.holds
    simp only [Bool.false_eq_true, ite_false] at hQL₄
    have hgu₄ := GuardIs.later hgu₃ hb₄ hm₄ hgt₄
    have hCM₄ := hCM₃.later hb₄ hm₄
    refine (XRuns.seq (ok₂ := True)
      (XRuns.someOp (p := p) (O := oracles H (Damp.Exec.liftWitness w)) rfl (by simp) hgu₄ fun e he => by
        rw [hQL₄, hLu₃]
        exact Kernel.claimZswapCoinReceive_spec H p e σ es m1 cmv₂ cm₂ (hkey z) hwf heff hm1 (hCM₄ e he) hz)
      (fun _ => Grows.pure' _)
      fun _ t₅ u₅ hm₅ hgt₅ hb₅ hR₅ => ?_).conseq (by simp) fun _ _ _ _ h => h
    obtain ⟨hQP₅, hQL₅⟩ := hR₅.holds
    simp only [Bool.false_eq_true, ite_false] at hQL₅
    have hCC₅ := ((hCC₂.later hb₃ hm₃).later hb₄ hm₄).later hb₅ hm₅
    have hO₅' := ((((hO₉.later hA' hn').later hb₁ hm₁).later hb₂ hm₂).later hb₃ hm₃).later hb₄ hm₄ |>.later hb₅ hm₅
    refine XRuns.pure fun e he => ⟨?_, ?_, ?_, ?_⟩
    · exact (((((hQt.imp fun e h => h.1).later hb₁ hm₁).later hb₂ hm₂).later hb₃ hm₃).later hb₄ hm₄).later hb₅ hm₅
        e he
    · unfold Value.Is
      exact evalList_append_some (Maybe.some_is (hCC₅ e he)) (evalList_append_some (hO₅' e he) rfl)
    · rw [hQP₅, hQP₄, hQP₃, hQP₂, hQP₁, hPt]
    · rw [hQL₅, hQL₄, hLu₃]
  · intro r env w' l ⟨a, b, hrab, ⟨ha', hb', hw', hl'⟩, hc'⟩
    have hla : (Value.toExprs a).length = Value.width ShieldedSendResult := by
      rw [← Damp.evalList_length ha', Value.width_sendResult, Value.width_maybe, Value.width_coin]
      simp [noneFs, outFs, derivedNonceFs, hcl, Value.width_coin]
    have hlb : (Value.toExprs b).length = Value.width ShieldedSendResult := by
      rw [← Damp.evalList_length hb', Value.width_sendResult, Value.width_maybe, Value.width_coin]
      simp [chFs, outFs, derivedNonceFs, hcl]
    have hsel := select_is (p := p) roundTrip_sendResult hc' hla hlb ha' hb'
    rw [hrab]
    refine ⟨?_, hw', hl'⟩
    simp only [decide_true, ite_true] at hsel
    have : (Fr.ofBool false :: List.replicate (Value.width ShieldedCoinInfo) 0) ++
        (derivedNonceFs p "midnight:kernel:nonce_evolve" n ++ c ++ [Fr.ofNat k]) = noneFs ++ (outFs ++ []) := by
      simp [noneFs, outFs]
    rw [this]; exact hsel

/-- **`sendShielded input recipient value`, under a guard meaning `gb`**: with
    it on, as `sendShielded_runs`; off, `sendShielded_off`. The change is
    `chg = if gb then v - k else 0`; the result, `(none, sent)` when `chg = 0`,
    `(some change, sent)` otherwise. -/
theorem sendShielded_runsG (input : QualifiedShieldedCoinInfo) (recipient : Either ZswapCoinPublicKey ContractAddress)
    (value : Uint128) {s : Build} {st : Exec.State ω LedgerState} {gb : Bool} (hg : GuardIs p s st.runState gb)
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
    (nf : List Fr) (x : Nat)
    (hnf : phashFs p coinPreimageAlign (cnPre (n ++ c ++ [v]) (selfOr gb selfFs)) = some nf)
    (hx : AV.ofFields [.bytes 32] nf = some (hkey x))
    (cm : List Fr) (y : Nat)
    (hcm : phashFs p coinPreimageAlign (ccPre (derivedNonceFs p "midnight:kernel:nonce_evolve" n ++ c ++
      [Fr.ofNat k]) u rl rr) = some cm)
    (hy : AV.ofFields [.bytes 32] cm = some (hkey y))
    (cm₂ : List Fr) (z : Nat)
    (hcm₂ : phashFs p coinPreimageAlign (ccPre (derivedNonceFs p "midnight:kernel:nonce_evolve/2" n ++ c ++
      [Fr.ofNat (if gb then v.val - k else 0)]) false [0, 0] (selfOr gb selfFs)) = some cm₂)
    (hz : AV.ofFields [.bytes 32] cm₂ = some (hkey z))
    (ω₁ ω₂ ω₃ : ω)
    (hw₁ : gb = true → w "createZswapInput" (n ++ c ++ [v, i]) st.private_ = some ([], ω₁))
    (hw₂ : gb = true → w "createZswapOutput" ((derivedNonceFs p "midnight:kernel:nonce_evolve" n ++ c ++ [Fr.ofNat k]) ++
      (Fr.ofBool u :: rl ++ rr)) ω₁ = some ([], ω₂))
    (hw₃ : gb = true → v.val - k ≠ 0 → w "createZswapOutput" ((derivedNonceFs p "midnight:kernel:nonce_evolve/2" n ++
      c ++ [Fr.ofNat (v.val - k)]) ++ (Fr.ofBool false :: [0, 0] ++ selfFs)) ω₂ = some ([], ω₃)) :
    XRuns p (oracles H (Damp.Exec.liftWitness w)) (sendShielded input recipient value) s st (gb = true → k ≤ v.val)
      (fun r e w' l => Value.Is p e r (if (if gb then v.val - k else 0) = 0
          then (Fr.ofBool false :: List.replicate (Value.width ShieldedCoinInfo) 0) ++
            (derivedNonceFs p "midnight:kernel:nonce_evolve" n ++ c ++ [Fr.ofNat k])
          else (Fr.ofBool true :: (derivedNonceFs p "midnight:kernel:nonce_evolve/2" n ++ c ++
            [Fr.ofNat (v.val - k)])) ++ (derivedNonceFs p "midnight:kernel:nonce_evolve" n ++ c ++ [Fr.ofNat k])) ∧
        w' = (if gb then (if v.val - k = 0 then ω₂ else ω₃) else st.private_) ∧
        l = (if gb then { st.ledger with effects := .array (sendSEffects es m0 m1 m2 x y z (!u && decide (rr = selfFs))
          (!decide (v.val - k = 0))) } else st.ledger)) := by
  cases gb with
  | true =>
    exact (sendShielded_runs H p w input recipient value hg n c v i hnl hcl hv hin k hk u rl rr hrl hrr hsh hr cfs wa
      selfFs hctx hc0 hself hwf es m0 m1 m2 heff hm0 hm1 hm2 nf x (by simpa [selfOr] using hnf) hx cm y hcm hy cm₂ z
      (by simpa [selfOr] using hcm₂) hz ω₁ ω₂ ω₃ (hw₁ rfl) (hw₂ rfl) (hw₃ rfl)).conseq (by simp)
      fun _ _ _ _ h => by simpa using h
  | false =>
    exact (sendShielded_off H p w input recipient value hg n c v i hnl hcl hv hin k hk u rl rr hrl hrr hsh hr cfs wa
      selfFs hctx hc0 hself hwf es m0 m1 m2 heff hm0 hm1 hm2 nf x hnf hx cm y hcm hy cm₂ z
      (by simpa using hcm₂) hz).conseq (by simp) fun _ _ _ _ h => by simpa using h

/-- **`sendImmediateShielded input recipient value`, under a guard meaning
    `gb`**: `sendShielded_runsG` of the coin with Merkle index 0. -/
theorem sendImmediateShielded_runsG (input : ShieldedCoinInfo) (recipient : Either ZswapCoinPublicKey ContractAddress)
    (value : Uint128) {s : Build} {st : Exec.State ω LedgerState} {gb : Bool} (hg : GuardIs p s st.runState gb)
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
    (nf : List Fr) (x : Nat)
    (hnf : phashFs p coinPreimageAlign (cnPre (n ++ c ++ [v]) (selfOr gb selfFs)) = some nf)
    (hx : AV.ofFields [.bytes 32] nf = some (hkey x))
    (cm : List Fr) (y : Nat)
    (hcm : phashFs p coinPreimageAlign (ccPre (derivedNonceFs p "midnight:kernel:nonce_evolve" n ++ c ++
      [Fr.ofNat k]) u rl rr) = some cm)
    (hy : AV.ofFields [.bytes 32] cm = some (hkey y))
    (cm₂ : List Fr) (z : Nat)
    (hcm₂ : phashFs p coinPreimageAlign (ccPre (derivedNonceFs p "midnight:kernel:nonce_evolve/2" n ++ c ++
      [Fr.ofNat (if gb then v.val - k else 0)]) false [0, 0] (selfOr gb selfFs)) = some cm₂)
    (hz : AV.ofFields [.bytes 32] cm₂ = some (hkey z))
    (ω₁ ω₂ ω₃ : ω)
    (hw₁ : gb = true → w "createZswapInput" (n ++ c ++ [v, 0]) st.private_ = some ([], ω₁))
    (hw₂ : gb = true → w "createZswapOutput" ((derivedNonceFs p "midnight:kernel:nonce_evolve" n ++ c ++ [Fr.ofNat k]) ++
      (Fr.ofBool u :: rl ++ rr)) ω₁ = some ([], ω₂))
    (hw₃ : gb = true → v.val - k ≠ 0 → w "createZswapOutput" ((derivedNonceFs p "midnight:kernel:nonce_evolve/2" n ++
      c ++ [Fr.ofNat (v.val - k)]) ++ (Fr.ofBool false :: [0, 0] ++ selfFs)) ω₂ = some ([], ω₃)) :
    XRuns p (oracles H (Damp.Exec.liftWitness w)) (sendImmediateShielded input recipient value) s st (gb = true → k ≤ v.val)
      (fun r e w' l => Value.Is p e r (if (if gb then v.val - k else 0) = 0
          then (Fr.ofBool false :: List.replicate (Value.width ShieldedCoinInfo) 0) ++
            (derivedNonceFs p "midnight:kernel:nonce_evolve" n ++ c ++ [Fr.ofNat k])
          else (Fr.ofBool true :: (derivedNonceFs p "midnight:kernel:nonce_evolve/2" n ++ c ++
            [Fr.ofNat (v.val - k)])) ++ (derivedNonceFs p "midnight:kernel:nonce_evolve" n ++ c ++ [Fr.ofNat k])) ∧
        w' = (if gb then (if v.val - k = 0 then ω₂ else ω₃) else st.private_) ∧
        l = (if gb then { st.ledger with effects := .array (sendSEffects es m0 m1 m2 x y z (!u && decide (rr = selfFs))
          (!decide (v.val - k = 0))) } else st.ledger)) :=
  sendShielded_runsG H p w { nonce := input.nonce, color := input.color, value := input.value, mt_index := 0 } recipient
    value hg n c v 0 hnl hcl hv
    (hin.imp fun e h => ⟨h.nonce, h.color, h.value, by
      show (Uint.capped 18446744073709551615 (.const 0)).eval p e = some 0
      rw [Uint.capped_eval uint64_bound]; rfl⟩)
    k hk u rl rr hrl hrr hsh hr cfs wa selfFs hctx hc0 hself hwf es m0 m1 m2 heff hm0 hm1 hm2 nf x hnf hx cm y hcm hy
    cm₂ z hcm₂ hz ω₁ ω₂ ω₃ hw₁ hw₂ hw₃

end

end Damp.Ledger
