import Damp
import Damp.Proofs.Ledger.TokensRuns
import Damp.Proofs.Interface.CallLogic
import Damp.Proofs.Ledger.Executor
import Examples.Tokens
import Examples.Calls

/-!
Contract-level theorems about a token circuit and a calling circuit, in the
style of `Examples/LedgerProofs.lean`, but stated for the circuit a successful
build ships (`buildCore`, at any level, with or without `--ledger-opt`) and
ending with the ZKIR it emits accepting the proof data, both via
`build_correct`:

* `deposit_shipped` (`Examples/Tokens.lean`, `tokens.deposit`): `receiveShielded`
  (a `kernel.self()` read, a `const`, the zero-width built-in witness
  `createZswapOutput`, a coin commitment, the Zswap claim) and a `Cell.write`
  of a structure.
* `bump_shipped` (`Examples/Calls.lean`, `caller.bump`): a ledger read, a
  cross-contract call (`XRuns.contractCall`), a `const`, a `Cell.write`, under
  the call assumption (`CallIsolated`, run by `runC`).

Nothing is assumed about hashes: the coin commitment is what `p` gives
(`phashFs`), the call's commitment `p.transientHash` of what it hashes.
-/
namespace Examples.TokenProofs
open Damp Damp.IR Damp.Ledger

set_option linter.unusedSimpArgs false

/-! ## From the circuit to what the build ships -/

/-- What `build_correct` gives for one circuit, run against the modelled
    ledger: the shipped circuit completes exactly when the original does, with
    the same outputs, private transcript, private state and ledger state; and
    the ZKIR shipped for it accepts what the executor records. -/
theorem shipped_run {c : Contract} {level : OptLevel} {ledgerOpt : Bool} {shipped : Contract}
    {srcs : List (Circuit × Zkir.IrSource)} (hb : c.buildCore level ledgerOpt = .ok (shipped, srcs))
    {p : Zkir.Prims} (hp : level.SoundAt p) {circ : Circuit} (hc : circ ∈ c.allCircuits) {ω : Type} (H : Hooks)
    (w : String → List Fr → ω → Option (List Fr × ω)) (xs : List Fr) (w₀ : ω) (σ : LedgerState) (hσ : σ.WF) :
    ∃ src, (buildPassWith level ledgerOpt circ, src) ∈ srcs ∧
      (Exec.run p (oracles H w) (buildPassWith level ledgerOpt circ) xs w₀ σ).map Exec.Result.ledgerObservable =
        (Exec.run p (oracles H w) circ xs w₀ σ).map Exec.Result.ledgerObservable ∧
      ∀ r, Exec.run p (oracles H w) (buildPassWith level ledgerOpt circ) xs w₀ σ = some r →
        src.run p xs r.priv r.pub = some { outputs := r.outputs, groups := r.groups } := by
  obtain ⟨-, -, -, h4⟩ := build_correct hb
  obtain ⟨src, hm, hs⟩ := h4 circ hc
  refine ⟨src, hm, ?_, fun r hr => (ShippedAs.base hs).accepted p _ xs w₀ σ r hr⟩
  cases ledgerOpt with
  | false =>
    have e := congrArg (Option.map fun (o : List Fr × List Fr × List Fr × List Fr × ω × LedgerState) =>
      (o.1, o.2.1, o.2.2.2.2.1, o.2.2.2.2.2)) (hs.exec_same p hp (oracles H w) xs w₀ σ)
    have hf : (Exec.Result.ledgerObservable : Exec.Result ω LedgerState → _) =
        fun x => (x.outputs, x.priv, x.private_, x.ledger) := rfl
    rw [hf]
    simpa [Option.map_map, Function.comp_def, Exec.Result.observable] using e
  | true => exact hs.exec_ledger p hp H w xs w₀ σ hσ

/-- The executor's verdict on a circuit, transferred to what the build ships. -/
theorem shipped_of {c : Contract} {level : OptLevel} {ledgerOpt : Bool} {shipped : Contract}
    {srcs : List (Circuit × Zkir.IrSource)} (hb : c.buildCore level ledgerOpt = .ok (shipped, srcs))
    {p : Zkir.Prims} (hp : level.SoundAt p) {circ : Circuit} (hc : circ ∈ c.allCircuits) {ω : Type} (H : Hooks)
    (w : String → List Fr → ω → Option (List Fr × ω)) (xs : List Fr) (w₀ : ω) (σ : LedgerState) (hσ : σ.WF)
    {ok : Prop} {P : List Fr → ω → LedgerState → Prop}
    (h : ((Exec.run p (oracles H w) circ xs w₀ σ).isSome = true ↔ ok) ∧
      ∀ r, Exec.run p (oracles H w) circ xs w₀ σ = some r → P r.outputs r.private_ r.ledger) :
    ∃ src, (buildPassWith level ledgerOpt circ, src) ∈ srcs ∧
      ((∃ r, Exec.run p (oracles H w) (buildPassWith level ledgerOpt circ) xs w₀ σ = some r) ↔ ok) ∧
      ∀ r, Exec.run p (oracles H w) (buildPassWith level ledgerOpt circ) xs w₀ σ = some r →
        P r.outputs r.private_ r.ledger ∧ src.run p xs r.priv r.pub = some { outputs := r.outputs, groups := r.groups } := by
  obtain ⟨src, hm, he, hacc⟩ := shipped_run hb hp hc H w xs w₀ σ hσ
  refine ⟨src, hm, ?_, fun r hr => ⟨?_, hacc r hr⟩⟩
  · rw [← h.1]
    constructor
    · rintro ⟨r, hr⟩
      rw [hr] at he
      cases hu : Exec.run p (oracles H w) circ xs w₀ σ <;> simp_all
    · intro hs
      obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.1 hs
      rw [hr'] at he
      cases ho : Exec.run p (oracles H w) (buildPassWith level ledgerOpt circ) xs w₀ σ with
      | none => simp [ho] at he
      | some r => exact ⟨r, rfl⟩
  · rw [hr] at he
    cases hu : Exec.run p (oracles H w) circ xs w₀ σ with
    | none => simp [hu] at he
    | some r' =>
      rw [hu] at he
      simp only [Option.map_some, Option.some.injEq, Exec.Result.ledgerObservable, Prod.mk.injEq] at he
      obtain ⟨e1, -, e3, e4⟩ := he
      rw [e1, e3, e4]; exact h.2 r' hu

/-! ## Shared facts -/

theorem disclose_is {α : Type} [Value α] (hrt : Value.RoundTrip α) {p : Zkir.Prims} {e : Env} {x : α} {xs : List Fr}
    (hl : (Value.toExprs x).length = Value.width α) (h : Value.Is p e x xs) : Value.Is p e (disclose x) xs := by
  unfold Value.Is disclose
  rw [hrt _ (by simpa using hl) p e, evalList_map_disclose]; exact h

theorem guardIs_top {ω σ : Type} {p : Zkir.Prims} {s : Build} {st : Exec.State ω σ} (h : s.guard = .const 1) :
    GuardIs p s st.runState true :=
  fun e _ => by rw [h]; exact guard_one_is

theorem setField_WF {σ : LedgerState} {fields : List SV} (hst : σ.state = .array fields) (hwf : σ.WF)
    (i : Nat) (v : SV) : (σ.setField i v).WF := by
  simpa [LedgerState.WF, LedgerState.setField, hst] using hwf

/-! ## `tokens.deposit` -/

section Deposit
open Examples.Tokens
variable {ω : Type} (p : Zkir.Prims) (H : Hooks) (w : String → List Fr → ω → Option (List Fr × ω))

/-- The ledger after `deposit coin`: the commitment `x` claimed as received
    (effects slot 1), and `last` (field 1) holding the coin, stored as `v`. -/
def depositLedger (σ : LedgerState) (es : List SV) (m : List (AV × SV)) (x : Nat) (v : AV) : LedgerState :=
  ({ σ with effects := .array (es.set 1 (.map (assocSet ⟨[.bytes 32], [x]⟩ .null m))) } : LedgerState).setField 1
    (.cell v)

/-- The body of `tokens.deposit`, for a coin meaning `xs`. -/
theorem deposit_runs (coin : ShieldedCoinInfo) (xs : List Fr) (env : Env) (ω₀ : ω) (σ : LedgerState)
    (hcoin : Stable 5 env (fun e => Value.Is p e coin xs)) (hcl : (Value.toExprs coin).length = 5)
    (cfs : List SV) (wa : AV) (selfFs : List Fr) (hctx : σ.context = .array cfs)
    (hc0 : cfs[0]? = some (.cell wa)) (hself : fieldsOf [.bytes 32] wa.atoms = some selfFs) (hwf : σ.WF)
    (es : List SV) (m : List (AV × SV)) (heff : σ.effects = .array es) (hm : es[1]? = some (.map m))
    (fields : List SV) (hst : σ.state = .array fields) (hfl : 1 < fields.length)
    (cm : List Fr) (hcm : phashFs p coinPreimageAlign (ccPre xs false [0, 0] selfFs) = some cm)
    (x : Nat) (hx : AV.ofFields [.bytes 32] cm = some ⟨[.bytes 32], [x]⟩)
    (v : AV) (hv : AV.ofFields (alignOf ShieldedCoinInfo) xs = some v) :
    XRuns p (oracles H w) (deposit coin) { next := 5 } (Exec.State.start env ω₀ σ)
      (∃ w', w "createZswapOutput" (xs ++ (Fr.ofBool false :: [0, 0] ++ selfFs)) ω₀ = some ([], w'))
      (fun r e w' l => Value.Is p e r [] ∧
        w "createZswapOutput" (xs ++ (Fr.ofBool false :: [0, 0] ++ selfFs)) ω₀ = some ([], w') ∧
        l = depositLedger σ es m x v) := by
  have hd : Stable 5 env (fun e => Value.Is p e (disclose coin) xs) :=
    hcoin.imp fun e h => disclose_is roundTrip_coin (by rw [hcl]; rfl) h
  have h1 := receiveShielded_runs H p w (disclose coin) (s := { next := 5 }) (st := Exec.State.start env ω₀ σ)
    (gb := true) (guardIs_top rfl) xs hd cfs wa selfFs hctx hc0 hself hwf es m heff hm cm
    (by simpa [selfOr] using hcm) x hx
  let σ₁ : LedgerState := { σ with effects := .array (es.set 1 (.map (assocSet ⟨[.bytes 32], [x]⟩ .null m))) }
  have hwf₁ : σ₁.WF := claimed_wf H (by decide) hx hwf heff hm
  have hst₁ : σ₁.state = .array fields := hst
  unfold deposit
  refine (XRuns.seq (ok₂ := True) h1 (fun _ => Grows.ledgerOp _ _) fun u s₁ st₁ hn₁ hgd₁ ha₁ hQ₁ => ?_).conseq
    (by simp [Exec.State.start]) fun _ _ _ _ h => h
  have hQ := hQ₁.holds
  simp only [ite_true] at hQ
  obtain ⟨hw₁, hl₁⟩ := hQ
  have hreq : ∀ e, Agree s₁.next st₁.env e → ∃ req, Exec.request p e
      [.push false (fieldKey last.index), .push true (alignedOf (disclose coin)), .ins false 1] = some req ∧
      (oracles H w).ledger req st₁.ledger = some ([], σ₁.setField 1 (.cell v)) := by
    intro e he
    rw [hl₁]
    exact op_req' (Cell.write_spec H last p e σ₁ fields (disclose coin) xs v hst₁ hfl (by decide) hwf₁
      ((hd.later ha₁ hn₁) e he) hv)
  refine (XRuns.ledgerOp (p := p) (O := oracles H w) (s := s₁) (st := st₁) (by simp) (guardIs_top (by rw [hgd₁]))
    hreq).conseq (by simp) fun _ _ w' l h => ⟨rfl, ?_, ?_⟩
  · rw [h.1]; exact hw₁
  · simp only [Option.some.injEq, Prod.mk.injEq, true_and] at h; exact h.2.symm

theorem deposit_ranges : CircuitFnSpec.ranges (ShieldedCoinInfo → CircuitM Unit) = Value.ranges ShieldedCoinInfo := by
  show Value.ranges ShieldedCoinInfo ++ [] = _; rw [List.append_nil]

theorem deposit_ranges_length : (Value.ranges ShieldedCoinInfo).length = 5 := Value.width_coin

/-- `tokens.deposit` before optimization, through `mkCircuit_exec_of_XRuns`. -/
theorem deposit_exec (xs : List Fr) (ω₀ : ω) (σ : LedgerState)
    (cfs : List SV) (wa : AV) (selfFs : List Fr) (hctx : σ.context = .array cfs)
    (hc0 : cfs[0]? = some (.cell wa)) (hself : fieldsOf [.bytes 32] wa.atoms = some selfFs) (hwf : σ.WF)
    (es : List SV) (m : List (AV × SV)) (heff : σ.effects = .array es) (hm : es[1]? = some (.map m))
    (fields : List SV) (hst : σ.state = .array fields) (hfl : 1 < fields.length)
    (cm : List Fr) (hcm : phashFs p coinPreimageAlign (ccPre xs false [0, 0] selfFs) = some cm)
    (x : Nat) (hx : AV.ofFields [.bytes 32] cm = some ⟨[.bytes 32], [x]⟩)
    (v : AV) (hv : AV.ofFields (alignOf ShieldedCoinInfo) xs = some v) :
    ((Exec.run p (oracles H w) deposit.circuit xs ω₀ σ).isSome = true ↔
      xs.length = 5 ∧ rangesHold (Value.ranges ShieldedCoinInfo) xs = true ∧
      ∃ w', w "createZswapOutput" (xs ++ (Fr.ofBool false :: [0, 0] ++ selfFs)) ω₀ = some ([], w')) ∧
    ∀ r, Exec.run p (oracles H w) deposit.circuit xs ω₀ σ = some r →
      r.outputs = [] ∧ w "createZswapOutput" (xs ++ (Fr.ofBool false :: [0, 0] ++ selfFs)) ω₀ = some ([], r.private_) ∧
      r.ledger = depositLedger σ es m x v := by
  show ((Exec.run p (oracles H w) (mkCircuit "deposit" ["coin"] deposit) xs ω₀ σ).isSome = true ↔ _) ∧ ∀ r,
    Exec.run p (oracles H w) (mkCircuit "deposit" ["coin"] deposit) xs ω₀ σ = some r → _
  by_cases hin : xs.length = 5 ∧ rangesHold (Value.ranges ShieldedCoinInfo) xs = true
  · let env : Env := fun v => xs.getD v 0
    have hW : Value.width ShieldedCoinInfo = 5 := Value.width_coin
    have hcoin : Stable 5 env (fun e => Value.Is p e
        (Value.ofExprs (argVars 0 (Value.width ShieldedCoinInfo)) : ShieldedCoinInfo) xs) := by
      intro e he
      have h := arg_is (p := p) roundTrip_coin e 0
      have hm : (List.range' 0 (Value.width ShieldedCoinInfo)).map e = xs := by
        rw [hW]
        have : (List.range' 0 5).map env = xs := by
          rw [range'_map_getD xs 0 5 (by omega)]; simp [List.take_of_length_le (Nat.le_of_eq hin.1)]
        rw [← this]
        exact List.map_congr_left fun v hv => (he v (by have := List.mem_range'_1.1 hv; omega)).symm
      rwa [hm] at h
    have hcl : (Value.toExprs (Value.ofExprs (argVars 0 (Value.width ShieldedCoinInfo)) : ShieldedCoinInfo)).length = 5 := by
      rw [← Damp.evalList_length hcoin.holds, hin.1]
    obtain ⟨h1, h2⟩ := mkCircuit_exec_of_XRuns (p := p) (O := oracles H w) "deposit" ["coin"] deposit
      (xs := xs) (w := ω₀) (l := σ) (outs := [])
      (ok := ∃ w', w "createZswapOutput" (xs ++ (Fr.ofBool false :: [0, 0] ++ selfFs)) ω₀ = some ([], w'))
      (P := fun w' l => w "createZswapOutput" (xs ++ (Fr.ofBool false :: [0, 0] ++ selfFs)) ω₀ = some ([], w') ∧
        l = depositLedger σ es m x v)
      (by rw [deposit_ranges, deposit_ranges_length, hin.1]) (by rw [deposit_ranges]; exact hin.2)
      (by
        have e1 : (CircuitFnSpec.ranges (ShieldedCoinInfo → CircuitM Unit)).length = Value.width ShieldedCoinInfo := by
          rw [deposit_ranges]; rfl
        show XRuns p (oracles H w) (deposit (Value.ofExprs ((argVars 0 (CircuitFnSpec.ranges
          (ShieldedCoinInfo → CircuitM Unit)).length).take (Value.width ShieldedCoinInfo))))
          { next := (CircuitFnSpec.ranges (ShieldedCoinInfo → CircuitM Unit)).length } _ _ _
        rw [e1, List.take_of_length_le (by simp [argVars])]
        rw [hW] at hcoin ⊢
        exact (deposit_runs p H w _ xs env ω₀ σ hcoin hcl cfs wa selfFs hctx hc0 hself hwf es m heff hm fields hst
          hfl cm hcm x hx v hv).conseq Iff.rfl fun r e w' l h => ⟨h.1, h.2⟩)
    refine ⟨h1.trans (by simp [hin]), fun r hr => ?_⟩
    obtain ⟨e1, e2, e3⟩ := h2 r hr
    exact ⟨e1, e2, e3⟩
  · have hnone : Exec.run p (oracles H w) (mkCircuit "deposit" ["coin"] deposit) xs ω₀ σ = none := by
      rw [mkCircuit_exec]; split
      · rename_i h
        rw [deposit_ranges, deposit_ranges_length] at h
        exact absurd ⟨h.1, h.2⟩ hin
      · rfl
    rw [hnone]
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff, reduceCtorEq, false_implies, implies_true, and_true]
    exact fun h => hin ⟨h.1, h.2.1⟩

/-- **`tokens.deposit`, as a build ships it.** For any successful build of
    the `tokens` contract (any level the hash functions `p` suit, with or
    without `--ledger-opt`), every input list `xs` and every well-formed ledger
    state whose call context holds the contract's address (limbs `selfFs`),
    with the coin commitment of `xs` sent to this contract hashing to `cm`
    (whatever `p` computes: the 32-byte atom `x`) and `xs` stored as `v`: the
    executor running the shipped circuit against the modelled VM completes
    exactly when `xs` is a well-formed `ShieldedCoinInfo` (5 inputs passing
    their range checks) and the built-in witness `createZswapOutput` accepts the
    output `(xs, right(self))`; it then returns nothing, leaves the private
    state the witness left, and the ledger is `depositLedger`: the commitment
    claimed as received (effects slot 1) and `last` holding the coin; nothing
    else changes. And the ZKIR shipped for the circuit accepts the proof data
    the executor recorded. -/
theorem deposit_shipped {level : OptLevel} {ledgerOpt : Bool} {shipped : Contract}
    {srcs : List (Circuit × Zkir.IrSource)} (hb : Examples.Tokens.contract.buildCore level ledgerOpt = .ok (shipped, srcs))
    (hp : level.SoundAt p) (xs : List Fr) (ω₀ : ω) (σ : LedgerState)
    (cfs : List SV) (wa : AV) (selfFs : List Fr) (hctx : σ.context = .array cfs)
    (hc0 : cfs[0]? = some (.cell wa)) (hself : fieldsOf [.bytes 32] wa.atoms = some selfFs) (hwf : σ.WF)
    (es : List SV) (m : List (AV × SV)) (heff : σ.effects = .array es) (hm : es[1]? = some (.map m))
    (fields : List SV) (hst : σ.state = .array fields) (hfl : 1 < fields.length)
    (cm : List Fr) (hcm : phashFs p coinPreimageAlign (ccPre xs false [0, 0] selfFs) = some cm)
    (x : Nat) (hx : AV.ofFields [.bytes 32] cm = some ⟨[.bytes 32], [x]⟩)
    (v : AV) (hv : AV.ofFields (alignOf ShieldedCoinInfo) xs = some v) :
    ∃ src, (buildPassWith level ledgerOpt deposit.circuit, src) ∈ srcs ∧
      ((∃ r, Exec.run p (oracles H w) (buildPassWith level ledgerOpt deposit.circuit) xs ω₀ σ = some r) ↔
        xs.length = 5 ∧ rangesHold (Value.ranges ShieldedCoinInfo) xs = true ∧
        ∃ w', w "createZswapOutput" (xs ++ (Fr.ofBool false :: [0, 0] ++ selfFs)) ω₀ = some ([], w')) ∧
      ∀ r, Exec.run p (oracles H w) (buildPassWith level ledgerOpt deposit.circuit) xs ω₀ σ = some r →
        (r.outputs = [] ∧
          w "createZswapOutput" (xs ++ (Fr.ofBool false :: [0, 0] ++ selfFs)) ω₀ = some ([], r.private_) ∧
          r.ledger = depositLedger σ es m x v) ∧
        src.run p xs r.priv r.pub = some { outputs := r.outputs, groups := r.groups } :=
  shipped_of hb hp (by simp [Examples.Tokens.contract, Contract.allCircuits]) H w xs ω₀ σ hwf
    (P := fun o w' l => o = [] ∧ w "createZswapOutput" (xs ++ (Fr.ofBool false :: [0, 0] ++ selfFs)) ω₀ = some ([], w') ∧
      l = depositLedger σ es m x v)
    (deposit_exec p H w xs ω₀ σ cfs wa selfFs hctx hc0 hself hwf es m heff hm fields hst hfl cm hcm x hx v hv)

end Deposit

/-! ## `caller.bump`: a cross-contract call -/

section Caller
open Examples.Caller
variable {ω : Type} (p : Zkir.Prims) (H : Hooks) (w : String → List Fr → ω → Option (List Fr × ω))

theorem roundTrip_adder : Value.RoundTrip Adder := fun es h => by
  show ExprsEquiv (es.take (byteLimbs 32)) es
  rw [show byteLimbs 32 = es.length from h.symm, List.take_length]; exact ExprsEquiv.refl _

theorem atomFits_field (y : Fr) : atomFits .field y.val = true := by
  have hy : y.val < 2 ^ 256 := Nat.lt_trans y.isLt (by decide)
  unfold atomFits byteLen
  by_cases h0 : y.val = 0
  · simp [h0]
  · have := (Nat.log2_lt (n := y.val) h0).2 hy
    simp only [h0, ↓reduceIte, decide_eq_true_eq]
    omega

theorem ofFields_field (y : Fr) : AV.ofFields (alignOf Field) [y] = some ⟨[.field], [y.val]⟩ := by
  simp [alignOf, Value.tys, Value.shape, Shape.tys, Ty.align, AV.ofFields, atomWidth, atomOfFields, atomFits_field]

/-- The ledger after `caller.bump`: the call claimed (effects slot 3,
    `claimedCall`) and `last` (field 2) holding the result `y`. -/
def bumpLedger (σ : LedgerState) (es : List SV) (m : List (AV × SV)) (kv : AV) (y : Fr) : LedgerState :=
  (claimedCall σ es m kv).setField 2 (.cell ⟨[.field], [y.val]⟩)

/-- The witness oracle with the calls answered by `c` (`Oracles.withCalls`). -/
abbrev callsBy (c : String → List Fr → ω → Option (List Fr × ω)) : String → List Fr → ω → Option (List Fr × ω) :=
  fun n => if Exec.isCallName n then c n else w n

/-- The body of `caller.bump`, the call answered by `c`. -/
theorem bump_runs (c : String → List Fr → ω → Option (List Fr × ω)) (xv : Fr) (env : Env) (ω₀ ω₁ : ω)
    (σ : LedgerState) (hX : Stable 1 env (fun e => e 0 = xv)) (fields : List SV) (aw : AV) (refFs : List Fr)
    (hst : σ.state = .array fields) (hf0 : fields[0]? = some (.cell aw)) (hfl : 2 < fields.length)
    (href : fieldsOf [.bytes 32] aw.atoms = some refFs) (hwf : σ.WF)
    (es : List SV) (m : List (AV × SV)) (heff : σ.effects = .array es) (hm : es[3]? = some (.map m))
    (y rand : Fr) (hans : c (callWitnessName "Adder" "addTo") (refFs ++ [xv]) ω₀ = some ([y, rand], ω₁))
    (kv : AV) (hkv : AV.ofFields [.bytes 32, .bytes 32, .field]
      (refFs ++ entryPointFs "addTo" ++ [commFs p rand [xv] [y]]) = some kv) :
    XRuns p (oracles H (callsBy w c)) (bump (Value.ofExprs [.var 0])) { next := 1 } (Exec.State.start env ω₀ σ)
      (m.length < 2 ^ 64)
      (fun r e w' l => Value.Is p e r [y] ∧ w' = ω₁ ∧ l = bumpLedger σ es m kv y) := by
  have hrefl := fieldsOf_bytes32_length href
  unfold bump
  -- `(← adder.read)`
  have h1 := (XRuns.ledgerRead (p := p) (O := oracles H (callsBy w c)) (s := { next := 1 })
    (st := Exec.State.start env ω₀ σ) (α := Adder) roundTrip_adder
    (mk := fun es => [.dup 0, .idx false false [fieldKey 0], .popeq false (alignOf Adder) es])
    (ReadOps.popeq_last [.dup 0, .idx false false [fieldKey 0]] false _) (by decide) (guardIs_top rfl)
    (res := some (refFs, σ)) (fun e _ => read_req' (Cell.read_spec H adder p e σ fields aw refFs hst hf0 (by decide) hwf
      href))).conseq (ok' := True) ⟨fun _ => trivial, fun _ => ⟨_, _, rfl, hrefl⟩⟩
    (Q' := fun r e w' l => w' = ω₀ ∧ l = σ ∧ Value.Is p e r refFs)
    (fun r e w' l ⟨hw, ys, hy, hi⟩ => by
      simp only [Option.some.injEq, Prod.mk.injEq] at hy; obtain ⟨rfl, rfl⟩ := hy; exact ⟨hw, rfl, hi⟩)
  refine (XRuns.seq (ok₂ := m.length < 2 ^ 64) h1 (fun _ => Grows.bind (Grows.bind (Grows.contractCall _ _ _ _ _)
      fun _ => Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _)
    fun a s₁ st₁ hn₁ hgd₁ ha₁ hQ₁ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hw₁, hl₁, -⟩ := hQ₁.holds
  have hg₁ : GuardIs p s₁ st₁.runState true := guardIs_top (by rw [hgd₁])
  -- `a.addTo (disclose x)`: the call
  have hargs : Stable s₁.next st₁.env (fun e => Expr.evalList p e
      (Value.toExprs (disclose (Value.ofExprs [.var 0] : Field)) ++ []) = some [xv]) :=
    (hX.later ha₁ hn₁).imp fun e h => by
      simp [disclose, Value.toExprs, Value.ofExprs, Expr.evalList, Expr.eval, h]
  have hcall := XRuns.contractCall (p := p) roundTrip_field "Adder" "addTo" (ref := a.bytes.limbs)
    (args := Value.toExprs (disclose (Value.ofExprs [.var 0] : Field)) ++ []) (oracles H (callsBy w c)) H rfl
    (s := s₁) (st := st₁) hg₁ (refFs := refFs) (hQ₁.imp fun e h => h.2.2) hargs (resFs := [y]) (rand := rand)
    (w' := ω₁) (by
      rw [hw₁]
      show callsBy w c (callWitnessName "Adder" "addTo") (refFs ++ [xv]) ω₀ = _
      simp only [callsBy, isCallName_callWitnessName, ite_true]; exact hans) rfl rfl (kv := kv) hkv es m (by rw [hl₁]; exact hwf)
    (by rw [hl₁]; exact heff) hm
  rw [hl₁] at hcall
  -- `const r ← …`
  refine (XRuns.seq (ok₂ := True) (XRuns.seq (ok₂ := True) hcall (fun _ => Grows.val _ _)
      fun b s₂ st₂ hn₂ hgd₂ ha₂ hQ₂ => (XRuns.val (p := p) (O := oracles H (callsBy w c)) (s := s₂) (st := st₂)
        roundTrip_field "r" rfl (hQ₂.imp fun e h => h.1)).conseq (ok' := True) Iff.rfl
        (Q' := fun r e w' l => Value.Is p e r [y] ∧ w' = ω₁ ∧ l = claimedCall σ es m kv ∧ m.length < 2 ^ 64)
        fun r e w' l h => ⟨h.1, h.2.1.trans hQ₂.holds.2.1, h.2.2.trans hQ₂.holds.2.2.1, hQ₂.holds.2.2.2⟩)
    (fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _)
    fun r s₃ st₃ hn₃ hgd₃ ha₃ hQ₃ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hr₃, hw₃, hl₃, hlen⟩ := hQ₃.holds
  have hg₃ : GuardIs p s₃ st₃.runState true := guardIs_top (by rw [hgd₃, hgd₁])
  -- `last.write r`
  have hwf₁ : (claimedCall σ es m kv).WF := by
    have := callClaimReq_spec H σ es m _ kv hwf heff hm hkv
    simp only [hlen, ite_true] at this
    exact ledgerOracle_wf this
  have hreq : ∀ e, Agree s₃.next st₃.env e → ∃ req, Exec.request p e
      [.push false (fieldKey last.index), .push true (alignedOf r), .ins false 1] = some req ∧
      (oracles H (callsBy w c)).ledger req st₃.ledger = some ([], bumpLedger σ es m kv y) := by
    intro e he
    rw [hl₃]
    exact op_req' (Cell.write_spec H last p e (claimedCall σ es m kv) fields r [y] ⟨[.field], [y.val]⟩ hst hfl
      (by decide) hwf₁ ((hQ₃ e he).1) (ofFields_field y))
  refine (XRuns.seq (ok₂ := True) (XRuns.ledgerOp (p := p) (O := oracles H (callsBy w c)) (s := s₃) (st := st₃)
      (by simp) hg₃ hreq) (fun _ => Grows.pure' _) fun u s₄ st₄ hn₄ hgd₄ ha₄ hQ₄ => ?_).conseq (by simp)
    fun _ _ _ _ h => h
  obtain ⟨hw₄, hl₄⟩ := hQ₄.holds
  simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hl₄
  exact XRuns.pure fun e he => ⟨((hQ₃.later ha₄ hn₄) e he).1, hw₄.trans hw₃, hl₄.symm⟩

/-- `caller.bump` before optimization. -/
theorem bump_exec (c : String → List Fr → ω → Option (List Fr × ω)) (xv : Fr) (ω₀ ω₁ : ω)
    (σ : LedgerState) (fields : List SV) (aw : AV) (refFs : List Fr)
    (hst : σ.state = .array fields) (hf0 : fields[0]? = some (.cell aw)) (hfl : 2 < fields.length)
    (href : fieldsOf [.bytes 32] aw.atoms = some refFs) (hwf : σ.WF)
    (es : List SV) (m : List (AV × SV)) (heff : σ.effects = .array es) (hm : es[3]? = some (.map m))
    (y rand : Fr) (hans : c (callWitnessName "Adder" "addTo") (refFs ++ [xv]) ω₀ = some ([y, rand], ω₁))
    (kv : AV) (hkv : AV.ofFields [.bytes 32, .bytes 32, .field]
      (refFs ++ entryPointFs "addTo" ++ [commFs p rand [xv] [y]]) = some kv) :
    ((Exec.run p (oracles H (callsBy w c)) bump.circuit [xv] ω₀ σ).isSome = true ↔ m.length < 2 ^ 64) ∧
    ∀ r, Exec.run p (oracles H (callsBy w c)) bump.circuit [xv] ω₀ σ = some r →
      r.outputs = [y] ∧ r.private_ = ω₁ ∧ r.ledger = bumpLedger σ es m kv y := by
  have hX : Stable 1 (fun v => [xv].getD v 0) (fun e => e 0 = xv) := fun e he => (he 0 (by decide)).symm
  obtain ⟨h1, h2⟩ := mkCircuit_exec_of_XRuns (p := p) (O := oracles H (callsBy w c)) "bump" ["x"] bump
    (xs := [xv]) (w := ω₀) (l := σ) (outs := [y]) (ok := m.length < 2 ^ 64)
    (P := fun w' l => w' = ω₁ ∧ l = bumpLedger σ es m kv y) rfl rfl
    (bump_runs p H w c xv _ ω₀ ω₁ σ hX fields aw refFs hst hf0 hfl href hwf es m heff hm y rand hans kv hkv)
  exact ⟨h1, fun r hr => ⟨(h2 r hr).1, (h2 r hr).2.1, (h2 r hr).2.2⟩⟩

/-- **`caller.bump`, as a build ships it, under the call assumption.** For
    any successful build of the `caller` contract (any level the hash
    functions `p` suit, with or without `--ledger-opt`), any call oracle `C`
    that is isolated (`CallIsolated C c`: the callee neither sees nor changes
    the caller's ledger state) and answers the call `adder.addTo(x)` with the
    result `y` and opening `rand` (and private state `ω₁`), and any well-formed
    ledger state whose `adder` cell holds an address with limbs `refFs`, `kv`
    being the call's claim (the address, `addTo`'s entry point, and the
    communication commitment `p.transientHash [rand, x, y]`) as the VM stores
    it: the general executor (`runC`, the callee run by `C`) on the shipped
    circuit completes exactly when fewer than `2^64` calls were claimed
    before; it then returns `y`, leaves the private state `ω₁`, and the ledger
    is `bumpLedger`: the call claimed in effects slot 3 and `last` holding `y`,
    nothing else changed; and the ZKIR shipped for the circuit accepts the
    proof data the executor recorded. -/
theorem bump_shipped {level : OptLevel} {ledgerOpt : Bool} {shipped : Contract}
    {srcs : List (Circuit × Zkir.IrSource)} (hb : Examples.Caller.contract.buildCore level ledgerOpt = .ok (shipped, srcs))
    (hp : level.SoundAt p) (C : Exec.CallOracle ω LedgerState) (c : String → List Fr → ω → Option (List Fr × ω))
    (hC : Exec.CallIsolated C c) (xv : Fr) (ω₀ ω₁ : ω)
    (σ : LedgerState) (fields : List SV) (aw : AV) (refFs : List Fr)
    (hst : σ.state = .array fields) (hf0 : fields[0]? = some (.cell aw)) (hfl : 2 < fields.length)
    (href : fieldsOf [.bytes 32] aw.atoms = some refFs) (hwf : σ.WF)
    (es : List SV) (m : List (AV × SV)) (heff : σ.effects = .array es) (hm : es[3]? = some (.map m))
    (y rand : Fr) (hans : c (callWitnessName "Adder" "addTo") (refFs ++ [xv]) ω₀ = some ([y, rand], ω₁))
    (kv : AV) (hkv : AV.ofFields [.bytes 32, .bytes 32, .field]
      (refFs ++ entryPointFs "addTo" ++ [commFs p rand [xv] [y]]) = some kv) :
    ∃ src, (buildPassWith level ledgerOpt bump.circuit, src) ∈ srcs ∧
      ((∃ r, Exec.runC p C (oracles H w) (buildPassWith level ledgerOpt bump.circuit) [xv] ω₀ σ = some r) ↔
        m.length < 2 ^ 64) ∧
      ∀ r, Exec.runC p C (oracles H w) (buildPassWith level ledgerOpt bump.circuit) [xv] ω₀ σ = some r →
        (r.outputs = [y] ∧ r.private_ = ω₁ ∧ r.ledger = bumpLedger σ es m kv y) ∧
        src.run p [xv] r.priv r.pub = some { outputs := r.outputs, groups := r.groups } := by
  simp only [Exec.runC_eq_run hC, oracles_withCalls]
  exact shipped_of hb hp (by simp [Examples.Caller.contract, Contract.allCircuits]) H (callsBy w c) [xv] ω₀ σ hwf
    (P := fun o w' l => o = [y] ∧ w' = ω₁ ∧ l = bumpLedger σ es m kv y)
    (bump_exec p H w c xv ω₀ ω₁ σ fields aw refFs hst hf0 hfl href hwf es m heff hm y rand hans kv hkv)

end Caller

end Examples.TokenProofs
