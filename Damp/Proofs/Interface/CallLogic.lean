/-
A cross-contract call (`contractCall`, `Damp/Lang/Calls.lean`) described by the
executor logic `XRuns`, against the modelled ledger.

A call is a witness statement with a reserved name (`call:<Interface>.<circuit>`)
whose answer is the callee's results and a random opening, the communication
commitment (a transient hash of the opening, the arguments and the results), and
the kernel claim `Kernel.claimContractCall`, which records the call in effects
slot 3. `XRuns.contractCall` takes the call oracle's answer as given (the
oracle `O`'s witness function at the call's name: under the call assumption
`CallIsolated C c` of `Damp/Proofs/Ledger/Calls.lean` that is `c`, via
`runC_eq_run` and `Oracles.withCalls`), and says: the call completes exactly when
the claimed-calls set has fewer than `2^64` entries; the result means the
callee's results; the private state is the one the oracle returned; and the
ledger differs from the one before only in effects slot 3, which gets the key
`(n, address, entry point, commitment)`, `n` the number of claims before.

Nothing is assumed about the transient hash: the commitment is
`p.transientHash (opening :: arguments ++ results)`, whatever that is.
-/
import Damp.Proofs.Interface.TokenLogic
import Damp.Proofs.Ledger.Effects
import Damp.Proofs.Ledger.Calls
import Damp.Proofs.Interface.Bytes
import Damp.Lang.Calls

namespace Damp
open IR Damp.Ledger

set_option linter.unusedSimpArgs false

theorem evalList_map_disclose {p : Zkir.Prims} {env : Env} : ∀ es : List Expr,
    Expr.evalList p env (es.map .disclose) = Expr.evalList p env es
  | [] => rfl
  | e :: es => by simp [Expr.evalList, Expr.eval, evalList_map_disclose es]

/-- A call's witness name is a call's (`Exec.isCallName`): under the call
    assumption the call oracle answers it. -/
theorem isCallName_callWitnessName (iface circuit : String) :
    Exec.isCallName (callWitnessName iface circuit) = true := by
  simp [Exec.isCallName, callWitnessName]
  exact List.prefix_append _ _

/-- The witness oracle with calls answered by `c` answers a call's name with `c`. -/
theorem withCalls_witness_call {ω σ : Type} (O : Exec.Oracles ω σ) (c : String → List Fr → ω → Option (List Fr × ω))
    (iface circuit : String) :
    (O.withCalls c).witness (callWitnessName iface circuit) = c (callWitnessName iface circuit) := by
  simp [Exec.Oracles.withCalls, isCallName_callWitnessName]

/-- The field elements of a circuit's entry point (`entryPoint`): the limbs of
    the SHA-256 hash `entryPointHash` computes. -/
def entryPointFs (circuit : String) : List Fr :=
  Bytes.limbVals (byteLimbs 32) (Bytes.numOf ((entryPointHash circuit).take 32))

theorem entryPoint_is {p : Zkir.Prims} {env : Env} (circuit : String) :
    Expr.evalList p env (entryPoint circuit).limbs = some (entryPointFs circuit) :=
  Bytes.ofBytes_is 32 _

/-- The communication commitment of a call with opening `rand`, arguments
    `argFs` and results `resFs`. -/
def commFs (p : Zkir.Prims) (rand : Fr) (argFs resFs : List Fr) : Fr := p.transientHash (rand :: argFs ++ resFs)

/-- The effects after a call is claimed: slot 3 gets `(m.length, kv)`. -/
def claimedCall (σ : LedgerState) (es : List SV) (m : List (AV × SV)) (kv : AV) : LedgerState :=
  { σ with effects := .array (es.set 3 (.map (assocSet ⟨alignContractCall, m.length :: kv.atoms⟩ .null m))) }

section
variable {ω : Type} {p : Zkir.Prims}

theorem Grows.contractCall (ρ : Type) [Value ρ] (iface circuit : String) (ref args : List Expr) :
    Grows (contractCall ρ iface circuit ref args) := by
  unfold Damp.contractCall
  exact Grows.bind (Grows.askWitness _ _ _) fun a => by
    obtain ⟨r, rd⟩ := a
    exact Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _

/-- **A cross-contract call**, under a guard that holds, the address meaning
    `refFs` and the arguments `argFs`, with the call oracle (`O.witness` at the
    call's name) answering the results `resFs` and the opening `rand`, which
    pass the range checks of the result type and of a field element, and the
    private state `w'`. Let `kv` be the claim's triple (address, entry point,
    commitment) as the VM stores it. Then the call completes exactly when fewer
    than `2^64` calls were claimed before; its result means `resFs`; the
    private state is `w'`; and the ledger is the one before with only effects
    slot 3 changed: `(m.length, kv)` added (`claimedCall`). -/
theorem XRuns.contractCall {ρ : Type} [Value ρ] (hrt : Value.RoundTrip ρ) (iface circuit : String)
    {ref args : List Expr} (O : Exec.Oracles ω LedgerState) (H : Hooks) (hO : O.ledger = ledgerOracle H)
    {s : Build} {st : Exec.State ω LedgerState} (hg : GuardIs p s st.runState true)
    {refFs argFs : List Fr} (href : Stable s.next st.env (fun e => Expr.evalList p e ref = some refFs))
    (hargs : Stable s.next st.env (fun e => Expr.evalList p e args = some argFs))
    {resFs : List Fr} {rand : Fr} {w' : ω}
    (hans : O.witness (callWitnessName iface circuit) (refFs ++ argFs) st.private_ = some (resFs ++ [rand], w'))
    (hlen : resFs.length = Value.width ρ) (hrng : rangesHold (Value.ranges (ρ × Field)) (resFs ++ [rand]) = true)
    {kv : AV} (hkv : AV.ofFields [.bytes 32, .bytes 32, .field]
      (refFs ++ entryPointFs circuit ++ [commFs p rand argFs resFs]) = some kv)
    (es : List SV) (m : List (AV × SV)) (hwf : st.ledger.WF) (heff : st.ledger.effects = .array es)
    (hm : es[3]? = some (.map m)) :
    XRuns p O (contractCall ρ iface circuit ref args) s st (m.length < 2 ^ 64)
      (fun r e w l => Value.Is p e r resFs ∧ w = w' ∧ l = claimedCall st.ledger es m kv ∧ m.length < 2 ^ 64) := by
  have hrtp : Value.RoundTrip (ρ × Field) := roundTrip_prod hrt roundTrip_field
  have hwp : Value.width (ρ × Field) = Value.width ρ + 1 := by rw [Value.width_prod]; rfl
  have hav : Expr.evalList p st.env (ref ++ args) = some (refFs ++ argFs) :=
    evalList_append_some href.holds hargs.holds
  unfold Damp.contractCall
  -- the call's witness
  have h1 := (XRuns.askWitness (p := p) (O := O) (s := s) (st := st) hrtp (callWitnessName iface circuit)
    (by rw [hwp]; omega) hg hav).addResult (askWitness_shaped (callWitnessName iface circuit) (ρ × Field) (ref ++ args) s)
  refine (XRuns.seq (ok₂ := m.length < 2 ^ 64) h1
    (fun a => by
      obtain ⟨r, rd⟩ := a
      exact Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _)
    fun a s₁ st₁ hn₁ hgd₁ ha₁ hQ₁ => ?_).conseq
    ⟨fun h => h.2, fun h => ⟨⟨_, _, hans, by simp [hlen, hwp], hrng⟩, h⟩⟩ fun _ _ _ _ h => h
  obtain ⟨r, rd⟩ := a
  obtain ⟨⟨hl₁, ys, hy, -, -⟩, es₀, hes₀, hpair⟩ := hQ₁.holds
  rw [hans] at hy
  simp only [Option.some.injEq, Prod.mk.injEq] at hy
  obtain ⟨rfl, rfl⟩ := hy
  have hg₁ := GuardIs.later hg ha₁ hn₁ hgd₁
  have hA₁ : Stable s₁.next st₁.env (fun e => Expr.evalList p e es₀ = some (resFs ++ [rand])) :=
    hQ₁.imp fun e h => by
      obtain ⟨⟨-, ys, hy, -, hi⟩, -⟩ := h
      rw [hans] at hy
      simp only [Option.some.injEq, Prod.mk.injEq] at hy
      obtain ⟨rfl, -⟩ := hy
      rw [hpair] at hi
      unfold Value.Is at hi
      rw [hrtp es₀ hes₀ p e] at hi
      exact hi
  have hparts : ∀ e, Expr.evalList p e es₀ = some (resFs ++ [rand]) →
      Value.Is p e r resFs ∧ Value.Is p e rd [rand] := by
    intro e he
    have := prod_ofExprs_is (p := p) (env := e) hrt roundTrip_field (by rw [hes₀, hwp]; rfl) he
    rw [← hpair] at this
    simpa [List.take_left' hlen, List.drop_left' hlen] using this
  -- the results, disclosed
  have hres : ∀ e, Value.Is p e r resFs →
      Expr.evalList p e ((Value.toExprs r).map Expr.disclose) = some resFs := by
    intro e h; rw [evalList_map_disclose]; exact h
  have hrlen : ((Value.toExprs r).map Expr.disclose).length = Value.width ρ := by
    have h0 := (hparts st₁.env (hA₁.holds)).1
    unfold Value.Is at h0
    rw [List.length_map, ← evalList_length h0, hlen]
  -- `comm := transientHash (rand :: args ++ results)`
  have hcomm : Stable s₁.next st₁.env (fun e => Value.Is p e
      (⟨.hash (.disclose rd.expr :: args ++ (Value.toExprs r).map Expr.disclose)⟩ : Field)
      [commFs p rand argFs resFs]) := by
    have hargs₁ := hargs.later ha₁ hn₁
    intro e he
    have ⟨hr, hd⟩ := hparts e (hA₁ e he)
    have hrd : rd.expr.eval p e = some rand := by
      unfold Value.Is at hd; simp [Value.toExprs, Expr.evalList] at hd
      cases h : rd.expr.eval p e <;> simp_all
    simp only [Value.Is, Value.toExprs, Expr.evalList, Expr.eval]
    rw [show (Expr.disclose rd.expr :: args ++ (Value.toExprs r).map Expr.disclose) =
      [Expr.disclose rd.expr] ++ args ++ (Value.toExprs r).map Expr.disclose from rfl]
    rw [evalList_append_some (evalList_append_some
      (show Expr.evalList p e [Expr.disclose rd.expr] = some [rand] by simp [Expr.evalList, Expr.eval, hrd])
      (hargs₁ e he))
      (hres e hr)]
    rfl
  refine (XRuns.seq (ok₂ := m.length < 2 ^ 64) (XRuns.val (p := p) (O := O) (s := s₁) (st := st₁) roundTrip_field
      "comm" rfl hcomm) (fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.pure' _)
    fun cm s₂ st₂ hn₂ hgd₂ ha₂ hQ₂ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨-, hw₂, hl₂⟩ := hQ₂.holds
  have hg₂ := GuardIs.later hg₁ ha₂ hn₂ hgd₂
  -- the claim
  have hreq : ∀ e, Agree s₂.next st₂.env e → ∃ req, Exec.request p e
      [.swap 0, .idx true true [fieldKey 3], .dup 0, .size,
       .push false { align := [.bytes 32, .bytes 32, .field],
                     vals := (⟨⟨ref⟩⟩ : ContractAddress).bytes.limbs ++ (entryPoint circuit).limbs ++ [cm.expr] },
       .concatCached 160, .pushNull false, .ins true 2, .swap 0] = some req ∧
      O.ledger req st₂.ledger = if m.length < 2 ^ 64 then some ([], claimedCall st.ledger es m kv) else none := by
    intro e he
    have hc := (hQ₂ e he).1
    have hce : cm.expr.eval p e = some (commFs p rand argFs resFs) := by
      unfold Value.Is at hc; simp [Value.toExprs, Expr.evalList] at hc
      cases h : cm.expr.eval p e <;> simp_all
    have hk : Expr.evalList p e ((⟨⟨ref⟩⟩ : ContractAddress).bytes.limbs ++ (entryPoint circuit).limbs ++ [cm.expr]) =
        some (refFs ++ entryPointFs circuit ++ [commFs p rand argFs resFs]) :=
      evalList_append_some (evalList_append_some ((href.later ha₁ hn₁).later ha₂ hn₂ e he) (entryPoint_is circuit))
        (by simp [Expr.evalList, hce])
    rw [hO, hl₂, hl₁]
    exact Kernel.claimContractCall_spec H p e st.ledger es m ⟨⟨ref⟩⟩ (entryPoint circuit) cm _ kv hwf heff hm hk hkv
  refine (XRuns.seq (ok₂ := True) (XRuns.ledgerOp (p := p) (O := O) (s := s₂) (st := st₂) (by simp) hg₂ hreq)
    (fun _ => Grows.pure' _) fun u s₃ st₃ hn₃ hgd₃ ha₃ hQ₃ => ?_).conseq
    ⟨fun h => by
      obtain ⟨⟨l, hl⟩, -⟩ := h
      by_cases hc : m.length < 2 ^ 64
      · exact hc
      · simp [hc] at hl,
     fun h => ⟨⟨claimedCall st.ledger es m kv, by simp [h]⟩, trivial⟩⟩ fun _ _ _ _ h => h
  obtain ⟨hw₃, hres₃⟩ := hQ₃.holds
  refine XRuns.pure fun e he => ⟨?_, ?_, ?_, ?_⟩
  · unfold Value.Is
    rw [hrt _ hrlen p e, hres e (hparts e ((hA₁.later ha₂ hn₂ |>.later ha₃ hn₃) e he)).1]
  · rw [hw₃, hw₂]
  · by_cases hc : m.length < 2 ^ 64
    · simp [hc] at hres₃; exact hres₃.symm
    · simp [hc] at hres₃
  · by_cases hc : m.length < 2 ^ 64
    · exact hc
    · simp [hc] at hres₃

end

end Damp
