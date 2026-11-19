import Damp
import Damp.Proofs.Interface.LedgerLogic
import Damp.Proofs.Ledger.Limbs
import Damp.Proofs.Ledger.Executor
import Examples.Vault
import Examples.Counter
import Damp.Proofs.Optimize.Pipeline

/-!
Contract-level theorems about two real ledger circuits, written in the surface
syntax, run by the executor (`Exec.run`) against the validated model of
Midnight's ledger VM (`oracles H w`, `Damp/Ledger/`), proved about the circuit
the build ships (`c.circuit.optimize`), and ending with the ZKIR emitted for it
accepting the proof data the executor recorded.

* `spend_shipped` (`Examples/Vault.lean`): a witness (the key), a persistent
  hash, a read of a `Cell (Bytes 32)` (two limbs), an equality `require`, a
  `Counter.increment` that may overflow, two more reads and a `Uint`
  comparison.
* `bump_shipped` (`Examples/Counter.lean`): ledger operations under `if%`
  (`when_`) guards that may be off, nested, and a `require` under a guard.

The proofs use the executor logic of `Damp/Proofs/Interface/LedgerLogic.lean`
(`XRuns`), the per-operation specifications of `Damp/Proofs/Ledger/` and the
pure rules of `Damp/Proofs/Interface/` (lifted with `XRuns.lift`); the step
from the circuit to the shipped one is `Exec.optimize_correct`, and the ZKIR
step `Exec.run_accepted_by_zkir`.
-/
namespace Examples.LedgerProofs
open Damp Damp.IR Damp.Ledger

set_option linter.unusedSimpArgs false

/-- The persistent hash's two limbs (high first), as the IR computes them. -/
def phashLimbs (p : Zkir.Prims) (align : List Zkir.AlignAtom) (xs : List Fr) : Option (List Fr) := do
  let d ← p.persistentHash align xs
  match Zkir.bytesToNatives d with
  | [lo, hi] => some [hi, lo]
  | _ => none

theorem disclose_persistentHash_is {p : Zkir.Prims} {e : Env} {α : Type} [Value α] {x : α} {xs hs : List Fr}
    (hx : Value.Is p e x xs) (hh : phashLimbs p ((Value.tys α).map Ty.align) xs = some hs) :
    Value.Is p e (disclose (persistentHash x)) hs := by
  unfold phashLimbs at hh
  unfold Value.Is at hx ⊢
  cases hd : p.persistentHash ((Value.tys α).map Ty.align) xs with
  | none => simp [hd] at hh
  | some d =>
    simp only [hd, Option.bind_eq_bind, Option.bind_some] at hh
    split at hh
    · rename_i lo hi heq
      simp only [Option.some.injEq] at hh
      subst hh
      simp [disclose, persistentHash, Value.toExprs, Value.ofExprs, byteLimbs, Expr.evalList, Expr.eval, hx, hd,
        heq]
    · simp at hh

theorem guardIs_top {ω σ : Type} {p : Zkir.Prims} {s : Build} {st : Exec.State ω σ} (h : s.guard = .const 1) :
    GuardIs p s st.runState true :=
  fun e _ => by rw [h]; exact guard_one_is

theorem uint_means_of_is {p : Zkir.Prims} {e : Env} {m x : Nat} {a : Uint m} (hm : m ≤ Uint.maxBound)
    (hx : x ≤ m) (h : Value.Is p e a [Fr.ofNat x]) : Uint.Means p e a x := by
  refine ⟨hm, hx, ?_⟩
  simp only [Value.Is, Value.toExprs, Expr.evalList] at h
  cases hr : a.expr.eval p e <;> simp [hr, Option.bind] at h
  rw [h]

theorem fieldsOf_bytes32 {X : Nat} (hX : X < 2 ^ 256) : fieldsOf [.bytes 32] [X] = some (Bytes.limbVals 2 X) := by
  simp [fieldsOf, fieldsOfAtom, Nat.mod_eq_of_lt hX, Bytes.limbVals]

theorem fieldsOf_small {k X : Nat} (hk : k ≤ 31) (hX : X < 2 ^ (8 * k)) :
    fieldsOf [.bytes k] [X] = some [Fr.ofNat X] := by
  have hm : X < Fr.modulus := Nat.lt_of_lt_of_le hX (Nat.le_of_lt (Nat.lt_of_le_of_lt
    (Nat.pow_le_pow_right (by decide) (by omega : 8 * k ≤ 248)) (by decide)))
  have hn : ¬ k > 31 := by omega
  simp [fieldsOf, fieldsOfAtom, hn, hm]
  exact Fr.ext (Nat.mod_eq_of_lt hm).symm

theorem read_req {α : Type} [Value α] {p : Zkir.Prims} {mk : List Expr → List (Impact.Op Expr)} {e : Env}
    {R : List (Impact.Op Fr) → Prop}
    (h : ∃ req, (emitted (ledgerRead α mk)).bind (Exec.request p e) = some req ∧ R req) :
    ∃ req, Exec.request p e (mk (readVars α)) = some req ∧ R req := by
  rw [emitted_ledgerRead] at h; exact h

theorem op_req {p : Zkir.Prims} {ops : List (Impact.Op Expr)} {e : Env} {R : List (Impact.Op Fr) → Prop}
    (h : ∃ req, (emitted (ledgerOp [] ops)).bind (Exec.request p e) = some req ∧ R req) :
    ∃ req, Exec.request p e ops = some req ∧ R req := h

theorem LedgerState.setField_WF {σ : LedgerState} {fields : List SV} (hst : σ.state = .array fields) (hwf : σ.WF)
    (i : Nat) (v : SV) : (σ.setField i v).WF := by
  simpa [LedgerState.WF, LedgerState.setField, hst] using hwf

theorem alignOf_uint32 : alignOf Uint32 = [.bytes 4] := by
  have : bitLen 4294967295 = 32 := by
    unfold bitLen; simp only [show (4294967295 : Nat) ≠ 0 by decide, ↓reduceIte]
    rw [(Nat.log2_eq_iff (k := 31) (by decide)).2 (by decide)]
  simp [alignOf, Value.tys, Value.shape, Shape.tys, Ty.align, this]

theorem phashLimbs_length {p : Zkir.Prims} {a : List Zkir.AlignAtom} {xs hs : List Fr}
    (h : phashLimbs p a xs = some hs) : hs.length = 2 := by
  unfold phashLimbs at h
  cases hd : p.persistentHash a xs with
  | none => simp [hd] at h
  | some d =>
    simp only [hd, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; rfl
    · simp at h

theorem amount_eval (p : Zkir.Prims) (e : Env) :
    Expr.eval p e (disclose (Value.ofExprs [.var 0] : Uint16)).expr = some (e 0) := by
  simp [disclose, Value.toExprs, Value.ofExprs, Uint.capped_eval (show 65535 ≤ Uint.maxBound by decide), Expr.eval]

/-- Optimizing does not change whether the executor completes. -/
theorem run_optimize_isSome {ω σ : Type} (p : Zkir.Prims) (O : Exec.Oracles ω σ) (c : Circuit) (xs : List Fr)
    (w : ω) (l : σ) :
    (∃ r, Exec.run p O c.optimize xs w l = some r) ↔ (Exec.run p O c xs w l).isSome = true := by
  have hopt := Exec.optimize_correct p O c xs w l
  constructor
  · rintro ⟨r, hr⟩
    rw [hr] at hopt
    cases hu : Exec.run p O c xs w l <;> simp_all
  · intro h
    obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.1 h
    rw [hr'] at hopt
    cases ho : Exec.run p O c.optimize xs w l with
    | none => simp [ho] at hopt
    | some r => exact ⟨r, rfl⟩

/-- Nor what it returns and leaves behind. -/
theorem run_optimize_some {ω σ : Type} (p : Zkir.Prims) (O : Exec.Oracles ω σ) (c : Circuit) (xs : List Fr)
    (w : ω) (l : σ) (r : Exec.Result ω σ) (hr : Exec.run p O c.optimize xs w l = some r) :
    ∃ r', Exec.run p O c xs w l = some r' ∧ r.outputs = r'.outputs ∧ r.private_ = r'.private_ ∧
      r.ledger = r'.ledger := by
  have hopt := Exec.optimize_correct p O c xs w l
  rw [hr] at hopt
  cases hu : Exec.run p O c xs w l with
  | none => simp [hu] at hopt
  | some r' =>
    rw [hu] at hopt
    simp only [Option.map_some, Option.some.injEq, Exec.Result.observable, Prod.mk.injEq] at hopt
    exact ⟨r', rfl, hopt.1, hopt.2.2.2.2.1, hopt.2.2.2.2.2⟩

section Vault
open Examples.Vault
variable {ω : Type} (p : Zkir.Prims) (H : Hooks) (wit : String → List Fr → ω → Option (List Fr × ω))

/-- The body of `vault.spend`, described by `XRuns`, step by step. -/
theorem spend_runs (amt : Fr) (hamt : amt.val ≤ 65535) (ω₀ ω₁ : ω) (ks hk : List Fr)
    (hw : wit "key" [] ω₀ = some (ks, ω₁)) (hkl : ks.length = 2)
    (hkr : rangesHold (Value.ranges (Bytes 32)) ks = true)
    (hh : phashLimbs p [.bytes 32] ks = some hk)
    (σ : LedgerState) (ow lw : AV) (sa : List Zkir.AlignAtom) (X L n : Nat)
    (hst : σ.state = .array [.cell ow, .cell lw, .cell ⟨sa, [n]⟩]) (hwf : σ.WF)
    (how : ow.atoms = [X]) (hX : X < 2 ^ 256) (hlw : lw.atoms = [L]) (hL : L < 2 ^ 32) (hn : n < 2 ^ 64) :
    XRuns p (oracles H wit) (spend (Value.ofExprs [.var 0])) { next := 1 }
      (Exec.State.start (fun v => [amt].getD v 0) ω₀ σ)
      (hk = Bytes.limbVals 2 X ∧ n + amt.val < 2 ^ 64 ∧ n + amt.val ≤ L)
      (fun r e w l => Value.Is p e r [] ∧ w = ω₁ ∧ l = σ.setField 2 (.cell (AV.ofU64 (n + amt.val)))) := by
  have hA : Stable 1 (fun v => [amt].getD v 0) (fun e => e 0 = amt) := fun e he => (he 0 (by decide)).symm
  -- 1. `(← key)`
  have h1 := (XRuns.askWitness (p := p) (O := oracles H wit) (s := { next := 1 })
    (st := (Exec.State.start (fun v => [amt].getD v 0) ω₀ σ))
    roundTrip_bytes "key" (α := Bytes 32) (args := []) (argVals := []) (by decide) (guardIs_top rfl) rfl).conseq
    (ok' := True) ⟨fun _ => trivial, fun _ => ⟨ks, ω₁, by simp [oracles, Exec.State.start, hw],
      by rw [hkl]; rfl, hkr⟩⟩
    (Q' := fun r e w l => l = σ ∧ w = ω₁ ∧ Value.Is p e r ks)
    (fun r e w l ⟨hl, ys, hy, _, hi⟩ => by
      simp only [oracles, Exec.State.start, hw, Option.some.injEq, Prod.mk.injEq] at hy hl
      obtain ⟨rfl, rfl⟩ := hy
      exact ⟨hl, rfl, hi⟩)
  refine XRuns.bind' h1 (Grows.bind (Grows.val _ _) fun _ => Grows.bind (Grows.ledgerRead _ _) fun _ =>
    Grows.bind (Grows.require _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ =>
    Grows.bind (Grows.ledgerRead _ _) fun _ => Grows.bind (Grows.ledgerRead _ _) fun _ => Grows.require _ _)
    fun st₁ ha₁ hQ₁ => ?_
  have hg1 := (show Grows key from Grows.askWitness "key" (Bytes 32) []) { next := 1 }
  generalize key.run { next := 1 } = q₁ at hQ₁ hg1 ⊢
  obtain ⟨k, s₁⟩ := q₁
  obtain ⟨hn1, hgd1, -⟩ := hg1
  simp only at hQ₁ hn1 hgd1 ⊢
  obtain ⟨hl1, hw1, -⟩ := hQ₁.holds
  have hA1 : Stable s₁.next st₁.env (fun e => e 0 = amt) := (hA.transfer ha₁).mono hn1
  -- 2. `const h := disclose (persistentHash k)`
  have h2 := XRuns.lift (O := oracles H wit) (st := st₁)
    (Runs.val (p := p) (s := s₁) (st := st₁.runState) roundTrip_bytes (x := disclose (persistentHash k)) (xs := hk) "h"
      rfl (hQ₁.imp fun e h => disclose_persistentHash_is h.2.2 hh)) (Quiet.val _ _)
  refine XRuns.bind' h2 (Grows.bind (Grows.ledgerRead _ _) fun _ =>
    Grows.bind (Grows.require _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ =>
    Grows.bind (Grows.ledgerRead _ _) fun _ => Grows.bind (Grows.ledgerRead _ _) fun _ => Grows.require _ _)
    fun st₂ ha₂ hQ₂ => ?_
  have hg2 := Grows.val (disclose (persistentHash k)) "h" s₁
  generalize (Damp.val (disclose (persistentHash k)) "h").run s₁ = q₂ at hQ₂ hg2 ⊢
  obtain ⟨h, s₂⟩ := q₂
  obtain ⟨hn2, hgd2, -⟩ := hg2
  simp only at hQ₂ hn2 hgd2 ⊢
  obtain ⟨-, hw2, hl2⟩ := hQ₂.holds
  have hA2 := (hA1.transfer ha₂).mono hn2
  -- 3. `(← owner.read)`
  have h3 := (XRuns.ledgerRead (p := p) (O := oracles H wit) (s := s₂) (st := st₂) (α := Bytes 32) roundTrip_bytes
    (mk := fun es => [.dup 0, .idx false false [fieldKey 0], .popeq false (alignOf (Bytes 32)) es])
    (ReadOps.popeq_last [.dup 0, .idx false false [fieldKey 0]] false _) (by decide) (guardIs_top (by rw [hgd2, hgd1]))
    (res := some (Bytes.limbVals 2 X, σ)) (fun e _ => by
      have := Cell.read_spec H owner p e σ _ ow (Bytes.limbVals 2 X) hst rfl (by decide) hwf
        (by rw [how]; exact fieldsOf_bytes32 hX)
      rw [hl2, hl1]; exact read_req this)).conseq (ok' := True)
    ⟨fun _ => trivial, fun _ => ⟨_, _, rfl, by simp [Bytes.limbVals]; rfl⟩⟩
    (Q' := fun r e w l => w = st₂.private_ ∧ l = σ ∧ Value.Is p e r (Bytes.limbVals 2 X))
    (fun r e w l ⟨hw, ys, hy, hi⟩ => by
      simp only [Option.some.injEq, Prod.mk.injEq] at hy; obtain ⟨rfl, rfl⟩ := hy; exact ⟨hw, rfl, hi⟩)
  refine XRuns.bind' h3 (Grows.bind (Grows.require _ _) fun _ => Grows.bind (Grows.ledgerOp _ _) fun _ =>
    Grows.bind (Grows.ledgerRead _ _) fun _ => Grows.bind (Grows.ledgerRead _ _) fun _ => Grows.require _ _)
    fun st₃ ha₃ hQ₃ => ?_
  have hg3 := (show Grows owner.read from Grows.ledgerRead _ _) s₂
  generalize owner.read.run s₂ = q₃ at hQ₃ hg3 ⊢
  obtain ⟨o, s₃⟩ := q₃
  obtain ⟨hn3, hgd3, -⟩ := hg3
  simp only at hQ₃ hn3 hgd3 ⊢
  obtain ⟨hw3, hl3, -⟩ := hQ₃.holds
  have hA3 := (hA2.transfer ha₃).mono hn3
  have hh3 := ((hQ₂.imp fun e h => h.1).transfer ha₃).mono hn3
  -- 4. `require (h ==. owner) "not owner"`
  have hkl2 := phashLimbs_length hh
  have hc4 : Stable s₃.next st₃.env (fun e => Boolean.Is p e (h ==. o) (decide (hk = Bytes.limbVals 2 X))) :=
    (hh3.and (hQ₃.imp fun e h => h.2.2)).imp fun e hh =>
      valueEq_means (by rw [← evalList_length hh.1, hkl2]; rfl)
        (by rw [← evalList_length hh.2]; simp [Bytes.limbVals]; rfl) hh.1 hh.2
  have h4 := XRuns.lift (O := oracles H wit) (st := st₃)
    (Runs.require_top (p := p) (st := st₃.runState) "not owner" (by rw [hgd3, hgd2, hgd1]) hc4) (Quiet.require _ _)
  refine (XRuns.bind (ok₂ := n + amt.val < 2 ^ 64 ∧ n + amt.val ≤ L) h4
    (Grows.bind (Grows.ledgerOp _ _) fun _ =>
    Grows.bind (Grows.ledgerRead _ _) fun _ => Grows.bind (Grows.ledgerRead _ _) fun _ => Grows.require _ _)
    fun st₄ ha₄ hQ₄ => ?_).conseq (by simp) (fun _ _ _ _ h => h)
  have hg4 := Grows.require (h ==. o) "not owner" s₃
  generalize (Damp.require (h ==. o) "not owner").run s₃ = q₄ at hQ₄ hg4 ⊢
  obtain ⟨u, s₄⟩ := q₄
  obtain ⟨hn4, hgd4, -⟩ := hg4
  simp only at hQ₄ hn4 hgd4 ⊢
  obtain ⟨-, hw4, hl4⟩ := hQ₄.holds
  have hA4 := (hA3.transfer ha₄).mono hn4
  -- 5. `spent.increment (disclose amount)`
  let σ' := σ.setField 2 (.cell (AV.ofU64 (n + amt.val)))
  have h5 := XRuns.ledgerOp (p := p) (O := oracles H wit) (s := s₄) (st := st₄)
    (ops := [.idx false true spent.path, .addi (disclose (Value.ofExprs [.var 0] : Uint16)).expr,
      .ins true spent.path.length]) (by simp) (guardIs_top (by rw [hgd4, hgd3, hgd2, hgd1]))
    (res := if n + amt.val < 2 ^ 64 then some ([], σ') else none) (fun e he => by
      have := Counter.increment_spec H spent p e σ _ sa n (disclose (Value.ofExprs [.var 0] : Uint16)) amt rfl hst
        rfl hn (by decide) hwf (by rw [amount_eval, hA4 e he]) (by omega)
      rw [hl4, hl3]; exact op_req this)
  refine (XRuns.bind (ok₂ := n + amt.val ≤ L) h5
    (Grows.bind (Grows.ledgerRead _ _) fun _ => Grows.bind (Grows.ledgerRead _ _) fun _ => Grows.require _ _)
    fun st₅ ha₅ hQ₅ => ?_).conseq
    ⟨fun ⟨⟨l, hl⟩, h⟩ => ⟨by split at hl <;> simp_all, h⟩, fun ⟨hc, h⟩ => ⟨⟨σ', by simp [hc]⟩, h⟩⟩
    (fun _ _ _ _ h => h)
  have hg5 := Grows.ledgerOp [] [.idx false true spent.path, .addi (disclose (Value.ofExprs [.var 0] : Uint16)).expr,
      .ins true spent.path.length] s₄
  generalize (Damp.ledgerOp [] [.idx false true spent.path, .addi (disclose (Value.ofExprs [.var 0] : Uint16)).expr,
      .ins true spent.path.length]).run s₄ = q₅ at hQ₅ hg5 ⊢
  obtain ⟨u, s₅⟩ := q₅
  obtain ⟨hn5, hgd5, -⟩ := hg5
  simp only at hQ₅ hn5 hgd5 ⊢
  obtain ⟨hw5, hres⟩ := hQ₅.holds
  have hov : n + amt.val < 2 ^ 64 := by
    rcases Nat.lt_or_ge (n + amt.val) (2 ^ 64) with hc | hc
    · exact hc
    · simp [Nat.not_lt.2 hc] at hres
  have hl5 : st₅.ledger = σ' := by simp [hov] at hres; exact hres.symm
  have hst' : σ'.state = .array [.cell ow, .cell lw, .cell (AV.ofU64 (n + amt.val))] := by
    simp [σ', LedgerState.setField, hst]
  have hwf' : σ'.WF := LedgerState.setField_WF hst hwf _ _
  -- 6. `(← spent.read)`
  have h6 := (XRuns.ledgerRead (p := p) (O := oracles H wit) (s := s₅) (st := st₅) (α := Uint64)
    (roundTrip_uint (by decide))
    (mk := fun es => [.dup 0, .idx false false spent.path, .popeq true [.bytes 8] es])
    (ReadOps.popeq_last [.dup 0, .idx false false spent.path] true _) (by decide) (guardIs_top (by rw [hgd5, hgd4, hgd3, hgd2, hgd1]))
    (res := some ([Fr.ofNat (n + amt.val)], σ')) (fun e _ => by
      have := Counter.read_spec H spent p e σ' _ [.bytes 8] (n + amt.val) rfl hst' rfl hov (by decide) hwf'
      rw [hl5]; exact read_req this)).conseq (ok' := True)
    ⟨fun _ => trivial, fun _ => ⟨_, _, rfl, rfl⟩⟩
    (Q' := fun r e w l => w = st₅.private_ ∧ l = σ' ∧ Value.Is p e r [Fr.ofNat (n + amt.val)])
    (fun r e w l ⟨hw, ys, hy, hi⟩ => by
      simp only [Option.some.injEq, Prod.mk.injEq] at hy; obtain ⟨rfl, rfl⟩ := hy; exact ⟨hw, rfl, hi⟩)
  refine XRuns.bind' h6 (Grows.bind (Grows.ledgerRead _ _) fun _ => Grows.require _ _) fun st₆ ha₆ hQ₆ => ?_
  have hg6 := (show Grows spent.read from Grows.ledgerRead _ _) s₅
  generalize spent.read.run s₅ = q₆ at hQ₆ hg6 ⊢
  obtain ⟨a, s₆⟩ := q₆
  obtain ⟨hn6, hgd6, -⟩ := hg6
  simp only at hQ₆ hn6 hgd6 ⊢
  obtain ⟨hw6, hl6, -⟩ := hQ₆.holds
  -- 7. `(← limit.read)`
  have h7 := (XRuns.ledgerRead (p := p) (O := oracles H wit) (s := s₆) (st := st₆) (α := Uint32)
    (roundTrip_uint (by decide))
    (mk := fun es => [.dup 0, .idx false false [fieldKey 1], .popeq false (alignOf Uint32) es])
    (ReadOps.popeq_last [.dup 0, .idx false false [fieldKey 1]] false _) (by decide) (guardIs_top (by rw [hgd6, hgd5, hgd4, hgd3, hgd2, hgd1]))
    (res := some ([Fr.ofNat L], σ')) (fun e _ => by
      have := Cell.read_spec H limit p e σ' _ lw [Fr.ofNat L] hst' rfl (by decide) hwf'
        (by rw [hlw, alignOf_uint32]; exact fieldsOf_small (by decide) hL)
      rw [hl6]; exact read_req this)).conseq (ok' := True)
    ⟨fun _ => trivial, fun _ => ⟨_, _, rfl, rfl⟩⟩
    (Q' := fun r e w l => w = st₆.private_ ∧ l = σ' ∧ Value.Is p e r [Fr.ofNat L])
    (fun r e w l ⟨hw, ys, hy, hi⟩ => by
      simp only [Option.some.injEq, Prod.mk.injEq] at hy; obtain ⟨rfl, rfl⟩ := hy; exact ⟨hw, rfl, hi⟩)
  refine XRuns.bind' h7 (Grows.require _ _) fun st₇ ha₇ hQ₇ => ?_
  have hg7 := (show Grows limit.read from Grows.ledgerRead _ _) s₆
  generalize limit.read.run s₆ = q₇ at hQ₇ hg7 ⊢
  obtain ⟨b, s₇⟩ := q₇
  obtain ⟨hn7, hgd7, -⟩ := hg7
  simp only at hQ₇ hn7 hgd7 ⊢
  obtain ⟨hw7, hl7, -⟩ := hQ₇.holds
  -- 8. `require (a <=. b) "over limit"`
  have ha7 := ((hQ₆.imp fun e h => h.2.2).transfer ha₇).mono hn7
  have hc8 : Stable s₇.next st₇.env (fun e => Boolean.Is p e (a <=. b) (decide (n + amt.val ≤ L))) :=
    (ha7.and (hQ₇.imp fun e h => h.2.2)).imp fun e hh =>
      cmpLe_means (uint_means_of_is (by decide) (by omega) hh.1) (uint_means_of_is (by decide) (by omega) hh.2)
  have h8 := XRuns.lift (O := oracles H wit) (st := st₇)
    (Runs.require_top (p := p) (st := st₇.runState) "over limit" (by rw [hgd7, hgd6, hgd5, hgd4, hgd3, hgd2, hgd1])
      hc8) (Quiet.require _ _)
  refine h8.conseq (by simp) fun r e w l hq => ⟨rfl, ?_, ?_⟩
  · rw [hq.2.1, hw7, hw6, hw5, hw4, hw3, hw2, hw1]
  · rw [hq.2.2, hl7]

theorem spend_ranges : CircuitFnSpec.ranges (Uint16 → CircuitM Unit) = [some (uintRange 65535)] := by
  simp [Value.ranges, Value.shape, Shape.ranges_prim, ranges_uint]

/-- `vault.spend` before optimization, through `mkCircuit_exec_of_XRuns`. -/
theorem spend_exec (amt : Fr) (ω₀ ω₁ : ω) (ks hk : List Fr)
    (hw : wit "key" [] ω₀ = some (ks, ω₁)) (hkl : ks.length = 2)
    (hkr : rangesHold (Value.ranges (Bytes 32)) ks = true)
    (hh : phashLimbs p [.bytes 32] ks = some hk)
    (σ : LedgerState) (ow lw : AV) (sa : List Zkir.AlignAtom) (X L n : Nat)
    (hst : σ.state = .array [.cell ow, .cell lw, .cell ⟨sa, [n]⟩]) (hwf : σ.WF)
    (how : ow.atoms = [X]) (hX : X < 2 ^ 256) (hlw : lw.atoms = [L]) (hL : L < 2 ^ 32) (hn : n < 2 ^ 64) :
    ((Exec.run p (oracles H wit) spend.circuit [amt] ω₀ σ).isSome = true ↔
      amt.val ≤ 65535 ∧ hk = Bytes.limbVals 2 X ∧ n + amt.val < 2 ^ 64 ∧ n + amt.val ≤ L) ∧
    ∀ r, Exec.run p (oracles H wit) spend.circuit [amt] ω₀ σ = some r →
      r.outputs = [] ∧ r.private_ = ω₁ ∧ r.ledger = σ.setField 2 (.cell (AV.ofU64 (n + amt.val))) := by
  have hrh : rangesHold (CircuitFnSpec.ranges (Uint16 → CircuitM Unit)) [amt] = decide (amt.val ≤ 65535) := by
    rw [spend_ranges]
    simp [rangesHold, uintRange_holds (show (65535 : Nat) < 2 ^ 254 by decide)]
  show ((Exec.run p (oracles H wit) (mkCircuit "spend" ["amount"] spend) [amt] ω₀ σ).isSome = true ↔ _) ∧ ∀ r,
    Exec.run p (oracles H wit) (mkCircuit "spend" ["amount"] spend) [amt] ω₀ σ = some r → _
  by_cases hamt : amt.val ≤ 65535
  · obtain ⟨h1, h2⟩ := mkCircuit_exec_of_XRuns (p := p) (O := oracles H wit) "spend" ["amount"] spend
      (xs := [amt]) (w := ω₀) (l := σ) (outs := [])
      (P := fun w l => w = ω₁ ∧ l = σ.setField 2 (.cell (AV.ofU64 (n + amt.val))))
      (by rw [spend_ranges]; rfl) (by rw [hrh]; simpa using hamt)
      (by rw [spend_ranges]; exact (spend_runs p H wit amt hamt ω₀ ω₁ ks hk hw hkl hkr hh σ ow lw sa X L n hst hwf
        how hX hlw hL hn))
    exact ⟨h1.trans (by simp [hamt]), fun r hr => ⟨(h2 r hr).1, (h2 r hr).2⟩⟩
  · have hnone : Exec.run p (oracles H wit) (mkCircuit "spend" ["amount"] spend) [amt] ω₀ σ = none := by
      rw [mkCircuit_exec]; split
      · rename_i h; rw [hrh] at h; simp [hamt] at h
      · rfl
    rw [hnone]; simp [hamt]

/-- **`vault.spend`, as shipped.** For every amount, key and ledger state
    holding a 32-byte owner `X`, a 32-bit limit `L` and a 64-bit counter `n`:
    the executor, running the optimized circuit (what the build ships) with the
    witness answering the key `ks` (whose persistent hash has limbs `hk`) and
    the ledger modelled by the VM, completes exactly when the amount is a
    `Uint16`, the key hashes to the owner, and `n + amount` neither overflows
    64 bits nor exceeds the limit; it then returns nothing, leaves the private
    state the witness left, sets the counter to `n + amount` and changes nothing
    else in the ledger; and the ZKIR emitted for the shipped circuit accepts the
    proof data it recorded. -/
theorem spend_shipped (amt : Fr) (ω₀ ω₁ : ω) (ks hk : List Fr)
    (hw : wit "key" [] ω₀ = some (ks, ω₁)) (hkl : ks.length = 2)
    (hkr : rangesHold (Value.ranges (Bytes 32)) ks = true)
    (hh : phashLimbs p [.bytes 32] ks = some hk)
    (σ : LedgerState) (ow lw : AV) (sa : List Zkir.AlignAtom) (X L n : Nat)
    (hst : σ.state = .array [.cell ow, .cell lw, .cell ⟨sa, [n]⟩]) (hwf : σ.WF)
    (how : ow.atoms = [X]) (hX : X < 2 ^ 256) (hlw : lw.atoms = [L]) (hL : L < 2 ^ 32) (hn : n < 2 ^ 64) :
    ((∃ r, Exec.run p (oracles H wit) spend.circuit.optimize [amt] ω₀ σ = some r) ↔
      amt.val ≤ 65535 ∧ hk = Bytes.limbVals 2 X ∧ n + amt.val < 2 ^ 64 ∧ n + amt.val ≤ L) ∧
    ∀ r, Exec.run p (oracles H wit) spend.circuit.optimize [amt] ω₀ σ = some r →
      r.outputs = [] ∧ r.private_ = ω₁ ∧ r.ledger = σ.setField 2 (.cell (AV.ofU64 (n + amt.val))) ∧
      ∀ src, Emit.circuit spend.circuit.optimize = .ok src →
        src.run p [amt] r.priv r.pub = some { outputs := r.outputs, groups := r.groups } := by
  obtain ⟨h1, h2⟩ := spend_exec p H wit amt ω₀ ω₁ ks hk hw hkl hkr hh σ ow lw sa X L n hst hwf how hX hlw hL hn
  refine ⟨(run_optimize_isSome p _ _ _ _ _).trans h1, fun r hr => ?_⟩
  obtain ⟨r', hu, ho, hpr, hl⟩ := run_optimize_some p _ _ _ _ _ r hr
  obtain ⟨e1, e2, e3⟩ := h2 r' hu
  exact ⟨ho.trans e1, hpr.trans e2, hl.trans e3, fun src hsrc =>
    Exec.run_accepted_by_zkir p (oracles H wit) spend.circuit src hsrc [amt] ω₀ σ r hr⟩

end Vault

section Counter
open Examples.Counter
variable {ω : Type} (p : Zkir.Prims) (H : Hooks) (wit : String → List Fr → ω → Option (List Fr × ω))

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

theorem GuardIs.step {ω σ : Type} {p : Zkir.Prims} {g : Bool} {s s₁ : Build} {st st₁ : Exec.State ω σ}
    (hgd : GuardIs p s st.runState g) (ha : Agree s.next st.env st₁.env) (hn : s.next ≤ s₁.next)
    (hg : s₁.guard = s.guard) : GuardIs p s₁ st₁.runState g := by
  intro e he; rw [hg]; exact (hgd.transfer ha).mono hn e he

theorem disclose_boolean_is {p : Zkir.Prims} {e : Env} {b : Boolean} {u : Bool} (h : Boolean.Is p e b u) :
    Boolean.Is p e (disclose b) u := by
  simpa [disclose, Boolean.Is, Value.toExprs, Value.ofExprs, Expr.eval] using h

/-- The ledger after `bump`'s branch: unchanged when `go` is false; otherwise
    the counter is `n + x`, and `total` is `x` unless `stop`. -/
def bumpLedger (σ : LedgerState) (n x : Nat) (g t : Bool) : LedgerState :=
  if g then
    if t then σ.setField 0 (.cell (AV.ofU64 (n + x)))
    else (σ.setField 0 (.cell (AV.ofU64 (n + x)))).setField 1 (.cell ⟨[.field], [x]⟩)
  else σ

theorem field_eval (p : Zkir.Prims) (e : Env) :
    Expr.evalList p e (Value.toExprs (Uint.toField (disclose (Value.ofExprs [.var 0] : Uint16)))) = some [e 0] := by
  simp [Uint.toField, disclose, Value.toExprs, Value.ofExprs, Uint.capped_eval (show 65535 ≤ Uint.maxBound by decide),
    Expr.evalList, Expr.eval]

/-- The branch of `bump`, under a guard meaning `g`. -/
theorem bump_branch (x : Fr) (hx : x.val ≤ 65535) (g t : Bool) (σ : LedgerState) (a : List Zkir.AlignAtom)
    (n : Nat) (tot capv : SV) (hst : σ.state = .array [.cell ⟨a, [n]⟩, tot, capv]) (hwf : σ.WF) (hn : n < 2 ^ 64)
    (s : Build) (st : Exec.State ω LedgerState) (hgd : GuardIs p s st.runState g) (hl : st.ledger = σ)
    (hX : Stable s.next st.env (fun e => e 0 = x))
    (hT : Stable s.next st.env (fun e => Boolean.Is p e (Value.ofExprs [.var 2] : Boolean) t))
    (hXm : Stable s.next st.env (fun e => Uint.Means p e (Value.ofExprs [.var 0] : Uint16) x.val)) :
    XRuns p (oracles H wit) (do
        count.increment (disclose (Value.ofExprs [.var 0] : Uint16))
        when_ (!.(disclose (Value.ofExprs [.var 2] : Boolean)))
          (total.write (Uint.toField (disclose (Value.ofExprs [.var 0] : Uint16))))
        require ((Value.ofExprs [.var 0] : Uint16) <. 500) "too big") s st
      (g = true → n + x.val < 2 ^ 64 ∧ x.val < 500)
      (fun _ _ w l => w = st.private_ ∧ l = bumpLedger σ n x.val g t ∧ (g = true → n + x.val < 2 ^ 64)) := by
  let σ₁ := σ.setField 0 (.cell (AV.ofU64 (n + x.val)))
  have hst₁ : σ₁.state = .array [.cell (AV.ofU64 (n + x.val)), tot, capv] := by
    simp [σ₁, LedgerState.setField, hst]
  have hwf₁ : σ₁.WF := LedgerState.setField_WF hst hwf _ _
  have hinc := fun e (he : Agree s.next st.env e) => Counter.increment_spec H count p e σ _ a n
    (disclose (Value.ofExprs [.var 0] : Uint16)) x rfl hst rfl hn (by decide) hwf
    (by rw [amount_eval, hX e he]) (by omega)
  have hwr := fun e (σ' : LedgerState) (fs : List SV) (hs : σ'.state = .array fs) (hi : 1 < fs.length)
      (hw : σ'.WF) (he : e 0 = x) =>
    Cell.write_spec H total p e σ' fs (Uint.toField (disclose (Value.ofExprs [.var 0] : Uint16))) [x]
      ⟨[.field], [x.val]⟩ hs hi (by decide) hw (by rw [field_eval, he])
      (ofFields_field x)
  have hS : Stable s.next st.env (fun e => Boolean.Is p e (!.(disclose (Value.ofExprs [.var 2] : Boolean))) (!t)) :=
    hT.imp fun e h => Boolean.not_is (disclose_boolean_is h)
  have hops : [Impact.Op.idx false true count.path, .addi (disclose (Value.ofExprs [.var 0] : Uint16)).expr,
      .ins true count.path.length] ≠ [] := by simp
  cases g with
  | true =>
    refine (XRuns.bind (ok₂ := x.val < 500) (XRuns.ledgerOp (p := p) (O := oracles H wit) (s := s) (st := st)
      (ops := [.idx false true count.path, .addi (disclose (Value.ofExprs [.var 0] : Uint16)).expr,
        .ins true count.path.length]) hops hgd (res := if n + x.val < 2 ^ 64 then some ([], σ₁) else none)
      (fun e he => by rw [hl]; exact op_req (hinc e he)))
      (Grows.bind (Grows.when_ _ (Grows.ledgerOp _ _)) fun _ => Grows.require _ _)
      fun st₁ ha₁ hQ₁ => ?_).conseq
      ⟨fun ⟨⟨l, hl⟩, h⟩ _ => ⟨by split at hl <;> simp_all, h⟩, fun h => ⟨⟨σ₁, by simp [(h rfl).1]⟩, (h rfl).2⟩⟩
      (fun _ _ _ _ h => h)
    have hg1 := Grows.ledgerOp [] [.idx false true count.path, .addi (disclose (Value.ofExprs [.var 0] : Uint16)).expr,
      .ins true count.path.length] s
    generalize (Damp.ledgerOp [] [.idx false true count.path,
      .addi (disclose (Value.ofExprs [.var 0] : Uint16)).expr, .ins true count.path.length]).run s = q₁ at hQ₁ hg1 ⊢
    obtain ⟨u, s₁⟩ := q₁
    obtain ⟨hn1, hgd1, -⟩ := hg1
    simp only at hQ₁ hn1 hgd1 ⊢
    obtain ⟨hw1, hres⟩ := hQ₁.holds
    have hov : n + x.val < 2 ^ 64 := by
      rcases Nat.lt_or_ge (n + x.val) (2 ^ 64) with hc | hc
      · exact hc
      · simp [Nat.not_lt.2 hc] at hres
    have hl1 : st₁.ledger = σ₁ := by simp [hov] at hres; exact hres.symm
    -- `when_ (!.(disclose stop)) (total.write ...)`
    have hw2 := XRuns.when_ (p := p) (O := oracles H wit) (s := s₁) (st := st₁) (gb := true) (cb := !t)
      (ok := True) (Q := fun _ _ w l => w = st₁.private_ ∧ l = bumpLedger σ n x.val true t)
      (GuardIs.step hgd ha₁ hn1 hgd1) ((hS.transfer ha₁).mono hn1) (Grows.ledgerOp _ _)
      (fun s' st' ctx => by
        cases t with
        | false =>
          refine (XRuns.ledgerOp (p := p) (O := oracles H wit) (s := s') (st := st') (List.cons_ne_nil _ _) ctx.2.2.2.2
            (res := some ([], σ₁.setField 1 (.cell ⟨[.field], [x.val]⟩))) (fun e he => by
              rw [ctx.2.2.2.1, hl1]
              exact op_req (hwr e σ₁ _ hst₁ (by simp) hwf₁ (((hX.transfer ha₁).mono hn1 |> ctx.transfer) e he)))).conseq
            ⟨fun _ => trivial, fun _ => ⟨_, rfl⟩⟩ fun _ _ w l h => ⟨h.1.trans ctx.2.2.1, by
              simp only [Option.some.injEq, Prod.mk.injEq, true_and] at h; rw [← h.2]; rfl⟩
        | true =>
          refine (XRuns.ledgerOp_off (p := p) (O := oracles H wit) (s := s') (st := st') (List.cons_ne_nil _ _) ctx.2.2.2.2
            (by obtain ⟨req, h, -⟩ := op_req (hwr st'.env σ₁ _ hst₁ (by simp) hwf₁
                  (((hX.transfer ha₁).mono hn1 |> ctx.transfer).holds)); exact ⟨req, h⟩)).conseq
            Iff.rfl fun _ _ w l h => ⟨h.1.trans ctx.2.2.1, by rw [h.2, ctx.2.2.2.1, hl1]; rfl⟩)
    refine XRuns.bind' hw2 (Grows.require _ _) fun st₂ ha₂ hQ₂ => ?_
    have hg2 := Grows.when_ (!.(disclose (Value.ofExprs [.var 2] : Boolean)))
      (show Grows (total.write (Uint.toField (disclose (Value.ofExprs [.var 0] : Uint16)))) from Grows.ledgerOp _ _) s₁
    generalize (when_ (!.(disclose (Value.ofExprs [.var 2] : Boolean)))
      (total.write (Uint.toField (disclose (Value.ofExprs [.var 0] : Uint16))))).run s₁ = q₂ at hQ₂ hg2 ⊢
    obtain ⟨u, s₂⟩ := q₂
    obtain ⟨hn2, hgd2, -⟩ := hg2
    simp only at hQ₂ hn2 hgd2 ⊢
    obtain ⟨hw2', hl2⟩ := hQ₂.holds
    -- `require (x <. 500)`
    have hc3 : Stable s₂.next st₂.env (fun e => Boolean.Is p e ((Value.ofExprs [.var 0] : Uint16) <. 500)
        (decide (x.val < 500))) :=
      (((hXm.transfer ha₁).mono hn1).transfer ha₂ |>.mono hn2).imp fun e h => cmpLt_means_nat h (by decide)
    refine (XRuns.lift (O := oracles H wit) (st := st₂)
      (Runs.require (p := p) (st := st₂.runState) "too big" (GuardIs.step (GuardIs.step hgd ha₁ hn1 hgd1) ha₂ hn2 hgd2)
        hc3) (Quiet.require _ _)).conseq (by simp) fun _ _ w l h => ⟨?_, ?_, fun _ => hov⟩
    · rw [h.2.1, hw2', hw1]
    · rw [h.2.2, hl2]
  | false =>
    refine XRuns.bind' ((XRuns.ledgerOp_off (p := p) (O := oracles H wit) (s := s) (st := st)
      (ops := [.idx false true count.path, .addi (disclose (Value.ofExprs [.var 0] : Uint16)).expr,
        .ins true count.path.length]) hops hgd
      (by obtain ⟨req, h, -⟩ := op_req (hinc st.env (Agree.refl _ _)); exact ⟨req, h⟩)))
      (Grows.bind (Grows.when_ _ (Grows.ledgerOp _ _)) fun _ => Grows.require _ _)
      fun st₁ ha₁ hQ₁ => ?_
    have hg1 := (show Grows (count.increment (disclose (Value.ofExprs [.var 0] : Uint16))) from Grows.ledgerOp _ _) s
    generalize (count.increment (disclose (Value.ofExprs [.var 0] : Uint16))).run s = q₁ at hQ₁ hg1 ⊢
    obtain ⟨u, s₁⟩ := q₁
    obtain ⟨hn1, hgd1, -⟩ := hg1
    simp only at hQ₁ hn1 hgd1 ⊢
    obtain ⟨hw1, hl1⟩ := hQ₁.holds
    have hw2 := XRuns.when_ (p := p) (O := oracles H wit) (s := s₁) (st := st₁) (gb := false) (cb := !t)
      (ok := True) (Q := fun _ _ w l => w = st₁.private_ ∧ l = σ)
      (GuardIs.step hgd ha₁ hn1 hgd1) ((hS.transfer ha₁).mono hn1) (Grows.ledgerOp _ _)
      (fun s' st' ctx => by
        refine (XRuns.ledgerOp_off (p := p) (O := oracles H wit) (s := s') (st := st') (List.cons_ne_nil _ _) ctx.2.2.2.2
          (by obtain ⟨req, h, -⟩ := op_req (hwr st'.env σ _ hst (by simp) hwf
                (((hX.transfer ha₁).mono hn1 |> ctx.transfer).holds)); exact ⟨req, h⟩)).conseq
          Iff.rfl fun _ _ w l h => ⟨h.1.trans ctx.2.2.1, by rw [h.2, ctx.2.2.2.1, hl1, hl]⟩)
    refine XRuns.bind' hw2 (Grows.require _ _) fun st₂ ha₂ hQ₂ => ?_
    have hg2 := Grows.when_ (!.(disclose (Value.ofExprs [.var 2] : Boolean)))
      (show Grows (total.write (Uint.toField (disclose (Value.ofExprs [.var 0] : Uint16)))) from Grows.ledgerOp _ _) s₁
    generalize (when_ (!.(disclose (Value.ofExprs [.var 2] : Boolean)))
      (total.write (Uint.toField (disclose (Value.ofExprs [.var 0] : Uint16))))).run s₁ = q₂ at hQ₂ hg2 ⊢
    obtain ⟨u, s₂⟩ := q₂
    obtain ⟨hn2, hgd2, -⟩ := hg2
    simp only at hQ₂ hn2 hgd2 ⊢
    obtain ⟨hw2', hl2⟩ := hQ₂.holds
    have hc3 : Stable s₂.next st₂.env (fun e => Boolean.Is p e ((Value.ofExprs [.var 0] : Uint16) <. 500)
        (decide (x.val < 500))) :=
      (((hXm.transfer ha₁).mono hn1).transfer ha₂ |>.mono hn2).imp fun e h => cmpLt_means_nat h (by decide)
    refine (XRuns.lift (O := oracles H wit) (st := st₂)
      (Runs.require (p := p) (st := st₂.runState) "too big" (GuardIs.step (GuardIs.step hgd ha₁ hn1 hgd1) ha₂ hn2 hgd2)
        hc3) (Quiet.require _ _)).conseq (by simp) fun _ _ w l h => ⟨?_, ?_, fun h => nomatch h⟩
    · rw [h.2.1, hw2', hw1]
    · rw [h.2.2, hl2]; rfl

theorem bumpLedger_count (σ : LedgerState) (a : List Zkir.AlignAtom) (n x : Nat) (tot capv : SV)
    (hst : σ.state = .array [.cell ⟨a, [n]⟩, tot, capv]) (hwf : σ.WF) (g t : Bool) :
    ∃ fs a', (bumpLedger σ n x g t).state = .array fs ∧ fs[0]? = some (.cell ⟨a', [if g then n + x else n]⟩) ∧
      (bumpLedger σ n x g t).WF := by
  cases g <;> cases t <;>
    simp [bumpLedger, LedgerState.setField, hst, AV.ofU64, LedgerState.WF] <;>
    simpa [LedgerState.WF] using hwf

theorem bump_ranges : CircuitFnSpec.ranges (Uint16 → Boolean → Boolean → CircuitM Uint64) =
    [some (uintRange 65535), some .bool, some .bool] := by
  simp [Value.ranges, Value.shape, Shape.ranges_prim, ranges_uint, ranges_bool]

/-- The body of `counter.bump`. -/
theorem bump_runs (x : Fr) (hx : x.val ≤ 65535) (g t : Bool) (ω₀ : ω) (σ : LedgerState) (a : List Zkir.AlignAtom)
    (n : Nat) (tot capv : SV) (hst : σ.state = .array [.cell ⟨a, [n]⟩, tot, capv]) (hwf : σ.WF) (hn : n < 2 ^ 64) :
    XRuns p (oracles H wit) (bump (Value.ofExprs [.var 0]) (Value.ofExprs [.var 1]) (Value.ofExprs [.var 2]))
      { next := 3 } (Exec.State.start (fun v => [x, Fr.ofBool g, Fr.ofBool t].getD v 0) ω₀ σ)
      (g = true → n + x.val < 2 ^ 64 ∧ x.val < 500)
      (fun r e w l => Value.Is p e r [Fr.ofNat (if g then n + x.val else n)] ∧ w = ω₀ ∧
        l = bumpLedger σ n x.val g t) := by
  let env : Env := fun v => [x, Fr.ofBool g, Fr.ofBool t].getD v 0
  have hA : Stable 3 env (fun e => e 0 = x) := fun e he => (he 0 (by decide)).symm
  have hXm := arg_uint_means (p := p) (m := 65535) (by decide) (k := 3) (env := env) (v := 0) (by decide)
    (by rw [uintRange_holds (show (65535 : Nat) < 2 ^ 254 by decide)]; simpa [env] using hx)
  have hG := arg_boolean_means (p := p) (k := 3) (env := env) (v := 1) (by decide) (b := g) rfl
  have hT := arg_boolean_means (p := p) (k := 3) (env := env) (v := 2) (by decide) (b := t) rfl
  refine (XRuns.seq (ok₂ := True)
    (XRuns.when_ (p := p) (O := oracles H wit) (s := { next := 3 }) (st := Exec.State.start env ω₀ σ)
      (gb := true) (cb := g) (ok := g = true → n + x.val < 2 ^ 64 ∧ x.val < 500)
      (Q := fun _ _ w l => w = ω₀ ∧ l = bumpLedger σ n x.val g t ∧ (g = true → n + x.val < 2 ^ 64))
      (guardIs_top rfl) (hG.imp fun e h => disclose_boolean_is h)
      (Grows.bind (Grows.ledgerOp _ _) fun _ => Grows.bind (Grows.when_ _ (Grows.ledgerOp _ _)) fun _ =>
        Grows.require _ _)
      (fun s' st' ctx => (bump_branch p H wit x hx g t σ a n tot capv hst hwf hn s' st' ctx.2.2.2.2 ctx.2.2.2.1
        (ctx.transfer hA) (ctx.transfer hT) (by simpa [env] using ctx.transfer hXm)).conseq Iff.rfl
        fun _ _ w l h => ⟨h.1.trans ctx.2.2.1, h.2⟩))
    (fun _ => Grows.ledgerRead _ _) fun u s₁ st₁ _ hgd1 ha₁ hQ₁ => ?_).conseq (by simp) fun _ _ _ _ h => h
  obtain ⟨hw1, hl1, hov⟩ := hQ₁.holds
  obtain ⟨fs, a', hfs, hf0, hwf'⟩ := bumpLedger_count σ a n x.val tot capv hst hwf g t
  have hn' : (if g then n + x.val else n) < 2 ^ 64 := by
    cases g
    · simpa using hn
    · simpa using hov rfl
  refine (XRuns.ledgerRead (p := p) (O := oracles H wit) (s := s₁) (st := st₁) (α := Uint64)
    (roundTrip_uint (by decide))
    (mk := fun es => [.dup 0, .idx false false count.path, .popeq true [.bytes 8] es])
    (ReadOps.popeq_last [.dup 0, .idx false false count.path] true _) (by decide) (guardIs_top hgd1)
    (res := some ([Fr.ofNat (if g then n + x.val else n)], bumpLedger σ n x.val g t)) (fun e _ => by
      have := Counter.read_spec H count p e _ fs a' _ rfl hfs hf0 hn' (by decide) hwf'
      rw [hl1]; exact read_req this)).conseq
    ⟨fun _ => trivial, fun _ => ⟨_, _, rfl, rfl⟩⟩ fun r e w l ⟨hw, ys, hy, hi⟩ => by
      simp only [Option.some.injEq, Prod.mk.injEq] at hy
      obtain ⟨rfl, rfl⟩ := hy
      exact ⟨hi, hw.trans hw1, rfl⟩


/-- `counter.bump` before optimization. -/
theorem bump_exec (x go stop : Fr) (ω₀ : ω) (σ : LedgerState) (a : List Zkir.AlignAtom) (n : Nat) (tot capv : SV)
    (hst : σ.state = .array [.cell ⟨a, [n]⟩, tot, capv]) (hwf : σ.WF) (hn : n < 2 ^ 64) :
    ((Exec.run p (oracles H wit) bump.circuit [x, go, stop] ω₀ σ).isSome = true ↔
      x.val ≤ 65535 ∧ (go = 0 ∨ go = 1) ∧ (stop = 0 ∨ stop = 1) ∧
        (go = 1 → n + x.val < 2 ^ 64 ∧ x.val < 500)) ∧
    ∀ r, Exec.run p (oracles H wit) bump.circuit [x, go, stop] ω₀ σ = some r →
      r.outputs = [Fr.ofNat (if go = 1 then n + x.val else n)] ∧ r.private_ = ω₀ ∧
      r.ledger = bumpLedger σ n x.val (decide (go = 1)) (decide (stop = 1)) := by
  have hrh : rangesHold (CircuitFnSpec.ranges (Uint16 → Boolean → Boolean → CircuitM Uint64)) [x, go, stop] =
      decide (x.val ≤ 65535 ∧ (go = 0 ∨ go = 1) ∧ (stop = 0 ∨ stop = 1)) := by
    rw [bump_ranges]
    simp only [rangesHold, List.zip_cons_cons, List.zip_nil_right, List.all_cons, List.all_nil, Option.all,
      uintRange_holds (show (65535 : Nat) < 2 ^ 254 by decide)]
    simp [Range.holds]
  show ((Exec.run p (oracles H wit) (mkCircuit "bump" ["x", "go", "stop"] bump) [x, go, stop] ω₀ σ).isSome = true
    ↔ _) ∧ ∀ r, Exec.run p (oracles H wit) (mkCircuit "bump" ["x", "go", "stop"] bump) [x, go, stop] ω₀ σ = some r → _
  by_cases hin : x.val ≤ 65535 ∧ (go = 0 ∨ go = 1) ∧ (stop = 0 ∨ stop = 1)
  · obtain ⟨g, rfl⟩ : ∃ g, go = Fr.ofBool g := by
      rcases hin.2.1 with h | h
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    obtain ⟨t, rfl⟩ : ∃ t, stop = Fr.ofBool t := by
      rcases hin.2.2 with h | h
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    obtain ⟨h1, h2⟩ := mkCircuit_exec_of_XRuns (p := p) (O := oracles H wit) "bump" ["x", "go", "stop"] bump
      (xs := [x, Fr.ofBool g, Fr.ofBool t]) (w := ω₀) (l := σ)
      (outs := [Fr.ofNat (if g then n + x.val else n)])
      (P := fun w l => w = ω₀ ∧ l = bumpLedger σ n x.val g t)
      (by rw [bump_ranges]; rfl) (by rw [hrh]; simpa using hin)
      (by rw [bump_ranges]; exact (bump_runs p H wit x hin.1 g t ω₀ σ a n tot capv hst hwf hn))
    refine ⟨h1.trans ?_, fun r hr => ?_⟩
    · cases g <;> simp [hin, Fr.ofBool, Fr.zero_ne_one, Ne.symm Fr.zero_ne_one]
    · obtain ⟨e1, e2, e3⟩ := h2 r hr
      refine ⟨?_, e2, ?_⟩
      · rw [e1]; cases g <;> simp [Fr.ofBool, Fr.zero_ne_one, Ne.symm Fr.zero_ne_one]
      · rw [e3]; cases g <;> cases t <;> simp [Fr.ofBool, Fr.zero_ne_one, Ne.symm Fr.zero_ne_one]
  · have hnone : Exec.run p (oracles H wit) (mkCircuit "bump" ["x", "go", "stop"] bump) [x, go, stop] ω₀ σ = none := by
      rw [mkCircuit_exec]; split
      · rename_i h; rw [hrh] at h; simp only [decide_eq_true_eq] at h; exact absurd h.2 hin
      · rfl
    rw [hnone]
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff, reduceCtorEq, false_implies, implies_true,
      and_true]
    exact fun h => hin ⟨h.1, h.2.1, h.2.2.1⟩

/-- **`counter.bump`, as shipped.** For every input and every ledger state whose
    counter holds a 64-bit `n`: the executor, running the optimized circuit
    against the modelled VM, completes exactly when `x` is a `Uint16`, `go` and
    `stop` are truth values, and, if `go`, the counter does not overflow and
    `x < 500`; it then returns the counter (`n + x` if `go`, else `n`), leaves
    the private state alone and the ledger as `bumpLedger` says (if `go`: the
    counter `n + x`, and `total` set to `x` unless `stop`; otherwise
    unchanged); and the ZKIR emitted for the shipped circuit accepts the proof
    data it recorded. -/
theorem bump_shipped (x go stop : Fr) (ω₀ : ω) (σ : LedgerState) (a : List Zkir.AlignAtom) (n : Nat) (tot capv : SV)
    (hst : σ.state = .array [.cell ⟨a, [n]⟩, tot, capv]) (hwf : σ.WF) (hn : n < 2 ^ 64) :
    ((∃ r, Exec.run p (oracles H wit) bump.circuit.optimize [x, go, stop] ω₀ σ = some r) ↔
      x.val ≤ 65535 ∧ (go = 0 ∨ go = 1) ∧ (stop = 0 ∨ stop = 1) ∧
        (go = 1 → n + x.val < 2 ^ 64 ∧ x.val < 500)) ∧
    ∀ r, Exec.run p (oracles H wit) bump.circuit.optimize [x, go, stop] ω₀ σ = some r →
      r.outputs = [Fr.ofNat (if go = 1 then n + x.val else n)] ∧ r.private_ = ω₀ ∧
      r.ledger = bumpLedger σ n x.val (decide (go = 1)) (decide (stop = 1)) ∧
      ∀ src, Emit.circuit bump.circuit.optimize = .ok src →
        src.run p [x, go, stop] r.priv r.pub = some { outputs := r.outputs, groups := r.groups } := by
  obtain ⟨h1, h2⟩ := bump_exec p H wit x go stop ω₀ σ a n tot capv hst hwf hn
  refine ⟨(run_optimize_isSome p _ _ _ _ _).trans h1, fun r hr => ?_⟩
  obtain ⟨r', hu, ho, hpr, hl⟩ := run_optimize_some p _ _ _ _ _ r hr
  obtain ⟨e1, e2, e3⟩ := h2 r' hu
  exact ⟨ho.trans e1, hpr.trans e2, hl.trans e3, fun src hsrc =>
    Exec.run_accepted_by_zkir p (oracles H wit) bump.circuit src hsrc [x, go, stop] ω₀ σ r hr⟩

end Counter

end Examples.LedgerProofs
