/-
What a witness statement does to the executor's ledger state, given the
footprint of its witness (`Damp/Executor/Witnesses.lean`), and what survives it.

* `step_witness_rel`: any reflexive relation the witness oracle keeps between
  the ledger states before and after holds between the executor's.
* `step_witness_keeps`: a witness that keeps the ledger leaves it as it was.
* `step_witness_ctx`: `createZswapOutput` (`CtxSlotWriter 1`) changes only
  call-context slot 1.
* `readSpec_ctx_frame`: a read of the call context whose first key is a
  constant other than 1 answers the same after such a change.
-/
import Damp.Proofs.Ledger.OptFrame
import Damp.Executor.Witnesses

set_option linter.unusedSimpArgs false

namespace Damp.Exec
open Damp.IR
open Damp.Zkir (Prims)

variable {ω σ : Type}

/-- **What a witness statement does to the ledger is what its oracle does**: a
    reflexive relation `R` that holds between every ledger state the witness
    `name` is asked in and the one it returns holds between the executor's
    ledger states before and after the statement. -/
theorem step_witness_rel (p : Prims) (O : Oracles ω σ) (R : σ → σ → Prop) (hrefl : ∀ l, R l l)
    {name : String} (hR : ∀ args x l r x' l', O.witness name args x l = some (r, x', l') → R l l')
    {s s' : State ω σ} {guard : Expr} {args : List Expr} {outs : List (Var × Option Range)} {shape : Shape}
    (h : Exec.step p O s (.witness guard name args outs shape) = some s') : R s.ledger s'.ledger := by
  simp only [Exec.step] at h
  cases hg : guard.eval p s.env with
  | none => simp [hg] at h
  | some g =>
    simp only [hg, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · split at h
      · cases ha : Expr.evalList p s.env args with
        | none => simp [ha] at h
        | some a =>
          cases hw : O.witness name a s.private_ s.ledger with
          | none => simp [ha, hw] at h
          | some r =>
            obtain ⟨vals, w', l'⟩ := r
            simp only [ha, hw, Option.bind_some] at h
            split at h
            · cases h; exact hR _ _ _ _ _ _ hw
            · simp at h
      · cases h; exact hrefl _
    · cases hb : asBool g with
      | none => simp [hb] at h
      | some b =>
        simp only [hb, Option.bind_some] at h
        split at h
        · cases ha : Expr.evalList p s.env args with
          | none => simp [ha] at h
          | some a =>
            cases hw : O.witness name a s.private_ s.ledger with
            | none => simp [ha, hw] at h
            | some r =>
              obtain ⟨vals, w', l'⟩ := r
              simp only [ha, hw, Option.bind_some] at h
              cases he : assign s.env outs vals with
              | none => simp [he] at h
              | some env => simp [he] at h; cases h; exact hR _ _ _ _ _ _ hw
        · cases he : assign s.env outs (outs.map fun _ => 0) with
          | none => simp [he] at h
          | some env => simp [he] at h; cases h; exact hrefl _

theorem step_witness_keeps (p : Prims) (O : Oracles ω σ) {name : String} (hk : KeepsLedger O.witness name)
    {s s' : State ω σ} {guard : Expr} {args : List Expr} {outs : List (Var × Option Range)} {shape : Shape}
    (h : Exec.step p O s (.witness guard name args outs shape) = some s') : s'.ledger = s.ledger :=
  (step_witness_rel p O (fun l l' => l' = l) (fun _ => rfl) (fun args x l r x' l' hw => hk args x l r x' l' hw) h)

/-- **A witness statement run on another ledger state**: if the witness's
    answers from `l` are its answers from `s.ledger` with `φ` applied to the
    ledger state they return, and `φ s.ledger = l`, then the statement run from
    `l` is the statement run from `s.ledger` with `φ` applied to the ledger
    state it leaves. -/
theorem step_witness_map (p : Prims) (O : Oracles ω σ) (φ : σ → σ) (s : State ω σ) (l : σ)
    (hφ : φ s.ledger = l) {name : String}
    (hW : ∀ a x, O.witness name a x l = (O.witness name a x s.ledger).map fun (r, x', l') => (r, x', φ l'))
    (guard : Expr) (args : List Expr) (outs : List (Var × Option Range)) (shape : Shape) :
    Exec.step p O { s with ledger := l } (.witness guard name args outs shape) =
      (Exec.step p O s (.witness guard name args outs shape)).map fun r => { r with ledger := φ r.ledger } := by
  obtain ⟨env, priv, pub, groups, private_, ledger⟩ := s
  simp only at hφ hW
  subst hφ
  simp only [Exec.step]
  cases hg : guard.eval p env with
  | none => simp
  | some gv =>
    simp only [Option.bind_some, Option.bind_eq_bind]
    by_cases ho : outs.isEmpty
    · simp only [ho, ite_true]
      by_cases h1 : gv = 1
      · simp only [h1, ite_true]
        cases ha : Expr.evalList p env args with
        | none => simp
        | some xs =>
          simp only [Option.bind_some, hW]
          cases hw : O.witness name xs private_ ledger with
          | none => simp
          | some res =>
            obtain ⟨vals, x', l'⟩ := res
            by_cases he : vals.isEmpty <;> simp [he]
      · simp [h1]
    · simp only [ho, Bool.false_eq_true, ite_false]
      cases hb : asBool gv with
      | none => simp
      | some b =>
        cases b
        · simp
          cases Exec.assign env outs (outs.map fun _ => 0) <;> simp
        · simp only [Option.bind_some, ite_true]
          cases ha : Expr.evalList p env args with
          | none => simp
          | some xs =>
            simp only [Option.bind_some, hW]
            cases hw : O.witness name xs private_ ledger with
            | none => simp
            | some res =>
              obtain ⟨vals, x', l'⟩ := res
              simp only [Option.map_some, Option.bind_some]
              cases Exec.assign env outs vals <;> simp

end Damp.Exec

namespace Damp.Ledger
open Damp.IR Damp.Exec Damp.Impact
open Damp.Zkir (Prims)

variable {ω : Type}

/-- The ledger states before and after `createZswapOutput`: the same contract
    state and effects, and call contexts agreeing everywhere but at slot `k`. -/
def CtxStep (k : Nat) (l l' : LedgerState) : Prop :=
  l'.state = l.state ∧ l'.effects = l.effects ∧ CtxAgreeExcept k l.context l'.context

theorem CtxStep.refl (k : Nat) (l : LedgerState) : CtxStep k l l := ⟨rfl, rfl, Or.inl rfl⟩

theorem CtxSlotWriter.step {k : Nat} {W : WitnessOracle ω LedgerState} {n : String} (h : CtxSlotWriter k W n) :
    ∀ args x l r x' l', W n args x l = some (r, x', l') → CtxStep k l l' := by
  intro args x l r x' l' hw
  obtain ⟨g, hg, hk⟩ := h
  rw [hg] at hw
  cases hgx : g args x l.context with
  | none => simp [hgx] at hw
  | some y =>
    obtain ⟨r0, x0, c⟩ := y
    simp only [hgx, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨-, -, rfl⟩ := hw
    exact ⟨rfl, rfl, hk _ _ _ _ _ _ hgx⟩

/-- **`createZswapOutput` changes at most call-context slot `k`** of the executor's ledger state. -/
theorem step_witness_ctx (p : Prims) {k : Nat} {W : WitnessOracle ω LedgerState} {H : Hooks} {name : String}
    (hW : CtxSlotWriter k W name)
    {s s' : State ω LedgerState} {guard : Expr} {args : List Expr} {outs : List (Var × Option Range)} {shape : Shape}
    (h : Exec.step p (oracles H W) s (.witness guard name args outs shape) = some s') : CtxStep k s.ledger s'.ledger :=
  step_witness_rel p (oracles H W) (CtxStep k) (CtxStep.refl k) hW.step h

/-- **Sees and changes only the call context**: the witness `n`'s answer, the
    private state afterwards and the new call context depend on its arguments,
    the private state and the call context only, and nothing else in the
    ledger state changes. Isolated witnesses and `createZswapOutput` are such. -/
def CtxOnly (W : WitnessOracle ω LedgerState) (n : String) : Prop :=
  ∃ g : List Fr → ω → SV → Option (List Fr × ω × SV),
    ∀ args x l, W n args x l = (g args x l.context).map fun (r, x', c) => (r, x', { l with context := c })

theorem _root_.Damp.Exec.Isolated.ctxOnly {W : WitnessOracle ω LedgerState} {n : String} (h : Isolated W n) : CtxOnly W n := by
  obtain ⟨g, hg⟩ := h
  refine ⟨fun a x c => (g a x).map fun (r, x') => (r, x', c), fun a x l => ?_⟩
  rw [hg]; cases h : g a x <;> simp [h]

theorem CtxSlotWriter.ctxOnly {k : Nat} {W : WitnessOracle ω LedgerState} {n : String} (h : CtxSlotWriter k W n) :
    CtxOnly W n := ⟨h.choose, h.choose_spec.1⟩

/-- A witness that sees and changes only the call context, asked from a ledger
    state with the same call context: its answers, with the rest of that ledger
    state kept. -/
theorem CtxOnly.map {W : WitnessOracle ω LedgerState} {n : String} (h : CtxOnly W n) (l₁ l₂ : LedgerState)
    (hc : l₂.context = l₁.context) (a : List Fr) (x : ω) :
    W n a x l₂ = (W n a x l₁).map fun (r, x', l') => (r, x', { l₂ with context := l'.context }) := by
  obtain ⟨g, hg⟩ := h
  rw [hg, hg, hc]
  cases g a x l₁.context <;> rfl

/-- What the witnesses of a `WitnessesOK` oracle other than a user's are. -/
theorem WitnessesOK.ctxOnly {W : WitnessOracle ω LedgerState} (h : WitnessesOK W) {n : String}
    (hn : witnessClass n ≠ .user) : CtxOnly W n := by
  cases hc : witnessClass n with
  | isolated => exact (h.isolated hc).ctxOnly
  | zswapOutput => exact (h.zswapOutput hc).ctxOnly
  | user => exact absurd hc hn

theorem CtxOnly.step {W : WitnessOracle ω LedgerState} {n : String} (h : CtxOnly W n) :
    ∀ args x l r x' l', W n args x l = some (r, x', l') → l'.state = l.state ∧ l'.effects = l.effects := by
  intro args x l r x' l' hw
  obtain ⟨g, hg⟩ := h
  rw [hg] at hw
  cases hgx : g args x l.context with
  | none => simp [hgx] at hw
  | some y =>
    obtain ⟨r0, x0, c⟩ := y
    simp only [hgx, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hw
    obtain ⟨-, -, rfl⟩ := hw
    exact ⟨rfl, rfl⟩

theorem CtxStep.wf {k : Nat} {l l' : LedgerState} (h : CtxStep k l l') (hw : l.WF) : l'.WF := by
  unfold LedgerState.WF at *; rw [h.2.1]; exact hw

/-- A step through an array along a key that is not `k` sees the same thing in contexts agreeing but at `k`. -/
theorem svStep_ctx {k : Nat} {c c' : SV} (hc : CtxAgreeExcept k c c') (kv : AV) (hk : kv.atoms ≠ [k]) :
    svStep c' kv = svStep c kv := by
  rcases hc with rfl | ⟨cs, cs', rfl, rfl, -, hi⟩
  · rfl
  · simp only [svStep]
    unfold AV.toU8
    split
    · rename_i x hx
      by_cases hlt : x < 2 ^ 8
      · have hxk : x ≠ k := fun e => hk (by rw [hx, e])
        simp [hlt, hi x hxk]
      · simp [hlt]
    · rfl

/-- **A context read whose first key is a constant other than `k` answers the
    same** in a ledger state whose call context differs from the original only
    at slot `k`. -/
theorem readSpec_ctx_frame {p : Prims} {env : Env} {path : List (Aligned Expr)} {path' : List (Aligned Fr)}
    (hp : path.mapM (fun k : Aligned Expr => k.mapM (Expr.eval p env)) = some path') (a : List Zkir.AlignAtom)
    {k : Nat} {kv : AV} (hkv : constPrefix 1 path = [kv]) (hk : kv.atoms ≠ [k])
    {q q' : LedgerState} (hc : CtxAgreeExcept k q.context q'.context) :
    readSpec 2 path' a q' = readSpec 2 path' a q := by
  unfold readSpec
  cases hks : path'.mapM AV.ofAligned with
  | none => rfl
  | some keys =>
    obtain ⟨rest, rfl⟩ := constPrefix_keys 1 hp hks
    rw [hkv]
    simp only [Option.bind_some, LedgerState.comp, List.cons_append, List.nil_append, svWalk, svStep_ctx hc kv hk,
      Option.bind_eq_bind]

/-- No witness of a `WitnessesOK` oracle changes the effects, so none breaks well-formedness. -/
theorem WitnessesOK.wf {W : WitnessOracle ω LedgerState} (h : WitnessesOK W) (n : String) :
    ∀ args x l r x' l', W n args x l = some (r, x', l') → l.WF → l'.WF := by
  intro args x l r x' l' hw hwf
  by_cases hz : witnessClass n = .zswapOutput
  · exact ((h.zswapOutput hz).step args x l r x' l' hw).wf hwf
  · rw [h.keepsLedger hz args x l r x' l' hw]; exact hwf

end Damp.Ledger
