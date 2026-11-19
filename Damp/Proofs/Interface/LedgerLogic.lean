/-
A program logic for circuit bodies run by the executor: ledger operations and
witness calls included.

`Runs` (`Logic.lean`) describes what a builder computation's statements do under
the IR semantics (`execAll`), where a witness call reads the private transcript
and a ledger operation the public one. What a user wants to know about a ledger
circuit is what *running* it does: what the executor (`Exec.steps`, with
oracles `O`) answers and what it leaves in the ledger. `XRuns p O m s st ok Q`
is that description:

* building `m` from `s` appends statements `T`, keeps the guard and does not move
  the counter back;
* the executor runs `T` from `st` to completion exactly when `ok` holds;
* when it does, it changes the environment only at variables numbered `s.next`
  or above, and `Q r env w l` holds of the result `r`, stably in the
  environment (as in `Runs`), with `w` the private state and `l` the ledger
  state afterwards.

The pure fragment is not re-proved: `XRuns.lift` turns any `Runs` description
of a computation whose statements are all quiet (bindings, asserts, range
checks: `Quiet`) into an `XRuns` one that keeps both oracle states, so
`Runs.require`, `Runs.val`, `Runs.sub`, `Runs.cond` on quiet branches, ... apply
unchanged. The executor's steps on quiet statements are exactly the semantics'
(`steps_quiet`). The new rules are:

* `XRuns.bind`, `XRuns.bind'`, `XRuns.seq`, `XRuns.pure`, `XRuns.conseq`:
  sequencing and weakening;
* `XRuns.ledgerOp`, `XRuns.ledgerRead`: a ledger operation under a guard that
  holds, described by what the ledger oracle answers to the request (any
  environment agreeing below the counter must give the same request; the
  specifications of `Damp/Proofs/Ledger/*.lean` have exactly this form);
* `XRuns.ledgerOp_off`, `XRuns.ledgerRead_off`: under a guard that is off, the
  oracle is not asked, the ledger is unchanged, and the reads are zero;
* `XRuns.askWitness`, `XRuns.askWitness_off`: a witness call, parameterized by
  the oracle's answer: it completes when the answer has the type's width and
  passes its range checks, and the result means the answer;
* `XRuns.underGuard`, `XRuns.when_`, `XRuns.cond`: `if%` whose branches may
  touch the ledger or call witnesses; each branch is described in every state it
  may be built in, under its guard (`XBranchCtx`; the `else` branch from the
  state the `then` branch left);
* `mkCircuit_exec_of_XRuns`: a description of a circuit function's body gives
  `Exec.run` of the circuit `mkCircuit` builds.
-/
import Damp.Proofs.Interface.Circuit
import Damp.Proofs.Ledger.Basic
import Damp.Proofs.LedgerAgreement

namespace Damp
open IR

set_option linter.unusedSimpArgs false

variable {ω σ : Type} {p : Zkir.Prims} {O : Exec.Oracles ω σ}

/-! ## Quiet statements -/

/-- A binding, an assert or a range check: what the executor and the semantics
    do alike, touching neither transcript nor oracle. -/
def IR.Stmt.quiet : Stmt → Bool
  | .bind .. => true
  | .assert .. => true
  | .constrain .. => true
  | _ => false

/-- Every statement `m` builds, from any state, is quiet. -/
def Quiet {α : Type} (m : CircuitM α) : Prop :=
  ∀ s : Build, ∃ T, (m.run s).2.stmts.toList = s.stmts.toList ++ T ∧ ∀ x ∈ T, x.quiet = true

/-- The run state the IR semantics sees for an executor state. -/
def Exec.State.runState (st : Exec.State ω σ) : RunState :=
  { env := st.env, priv := st.priv, pub := st.pub, groups := st.groups }

/-- The state a call starts in: no transcripts yet. -/
def Exec.State.start (env : Env) (w : ω) (l : σ) : Exec.State ω σ := { env, private_ := w, ledger := l }

theorem Exec.State.runState_env (st : Exec.State ω σ) : st.runState.env = st.env := rfl

/-- On a quiet statement the executor does what the semantics does, and the
    semantics changes only the environment. -/
theorem step_quiet {x : Stmt} (hx : x.quiet = true) (st : Exec.State ω σ) :
    Exec.step p O st x = (x.exec p st.runState).map (fun r => { st with env := r.env }) ∧
      ∀ r, x.exec p st.runState = some r → r = { st.runState with env := r.env } := by
  cases x with
  | bind v h e =>
    simp only [Exec.step, Stmt.exec, Exec.State.runState]
    cases e.eval p st.env <;> simp [Option.bind]
  | assert c m =>
    simp only [Exec.step, Stmt.exec, Exec.State.runState]
    cases hc : c.eval p st.env with
    | none => simp [hc, Option.bind]
    | some v =>
      cases hb : asBool v with
      | none => simp [hc, hb, Option.bind]
      | some b => cases b <;> simp [hc, hb, Option.bind]
  | constrain e r =>
    simp only [Exec.step, Stmt.exec, Exec.State.runState]
    cases he : e.eval p st.env with
    | none => simp [he, Option.bind]
    | some v => by_cases hr : r.holds v <;> simp [hr, Option.bind, he]
  | witness => simp [Stmt.quiet] at hx
  | ledger => simp [Stmt.quiet] at hx

/-- The executor on quiet statements is the semantics. -/
theorem steps_quiet : ∀ (T : List Stmt), (∀ x ∈ T, x.quiet = true) → ∀ st : Exec.State ω σ,
    Exec.steps p O T st = (execAll p T st.runState).map (fun r => { st with env := r.env })
  | [], _, st => rfl
  | x :: T, hq, st => by
    obtain ⟨h1, h2⟩ := step_quiet (p := p) (O := O) (hq x (by simp)) st
    simp only [Exec.steps, execAll, h1]
    cases hx : x.exec p st.runState with
    | none => rfl
    | some r =>
      have hr := h2 r hx
      have hT := steps_quiet T (fun y hy => hq y (by simp [hy])) { st with env := r.env }
      have hrun : ({ st with env := r.env } : Exec.State ω σ).runState = r := by
        rw [hr]; rfl
      rw [hrun] at hT
      show Exec.steps p O T { st with env := r.env } = Option.map _ (execAll p T r)
      rw [hT]

theorem steps_append (l₁ l₂ : List Stmt) (st : Exec.State ω σ) :
    Exec.steps p O (l₁ ++ l₂) st = (Exec.steps p O l₁ st).bind (Exec.steps p O l₂) := by
  induction l₁ generalizing st with
  | nil => rfl
  | cons x l ih =>
    simp only [List.cons_append, Exec.steps]
    cases Exec.step p O st x with
    | none => rfl
    | some s' => exact ih s'

theorem steps_single (x : Stmt) (st : Exec.State ω σ) : Exec.steps p O [x] st = Exec.step p O st x := by
  simp only [Exec.steps]; cases Exec.step p O st x <;> rfl

namespace Quiet

theorem pure' {α : Type} (a : α) : Quiet (Pure.pure a : CircuitM α) := fun s =>
  ⟨[], by simp [CircuitM.pure_run], by simp⟩

theorem bind {α β : Type} {m : CircuitM α} {f : α → CircuitM β} (hm : Quiet m) (hf : ∀ a, Quiet (f a)) :
    Quiet (m >>= f) := fun s => by
  rw [CircuitM.bind_run]
  obtain ⟨T₁, hT₁, q₁⟩ := hm s
  obtain ⟨T₂, hT₂, q₂⟩ := hf (m.run s).1 (m.run s).2
  refine ⟨T₁ ++ T₂, by rw [hT₂, hT₁, List.append_assoc], fun x hx => ?_⟩
  rcases List.mem_append.1 hx with h | h
  · exact q₁ x h
  · exact q₂ x h

theorem emit {x : Stmt} (hx : x.quiet = true) : Quiet (Damp.emit x) := fun s =>
  ⟨[x], Array.toList_push (xs := s.stmts) (x := x), by simp [hx]⟩

theorem freshVar : Quiet Damp.freshVar := fun s => ⟨[], by simp; rfl, by simp⟩
theorem currentGuard : Quiet Damp.currentGuard := fun s => ⟨[], by simp; rfl, by simp⟩

theorem of_errors {α : Type} {m : CircuitM α} (h : ∀ s, (m.run s).2 = { s with errors := (m.run s).2.errors }) :
    Quiet m := fun s => by rw [h s]; exact ⟨[], by simp, by simp⟩

theorem require (c : Boolean) (msg : String) : Quiet (Damp.require c msg) := fun s => by
  rw [require_run]; exact ⟨_, Array.toList_push, by simp [Stmt.quiet]⟩

theorem sub {m k : Nat} (a : Uint m) (b : Uint k) : Quiet (a.sub b) := fun s => by
  rw [Uint.sub_run]; exact ⟨_, Array.toList_push, by simp [Stmt.quiet]⟩

theorem guarded (e : Expr) : Quiet (Damp.guarded e) := fun s => by
  rw [guarded_run]; exact ⟨[], by simp, by simp⟩

theorem mapM {α β : Type} {f : α → CircuitM β} (hf : ∀ a, Quiet (f a)) : ∀ l : List α, Quiet (l.mapM f)
  | [] => pure' _
  | a :: l => by
    rw [List.mapM_cons]; exact bind (hf a) fun _ => bind (mapM hf l) fun _ => pure' _

theorem val {α : Type} [Value α] (x : α) (hint : String) : Quiet (Damp.val x hint) :=
  bind (mapM (fun _ => bind freshVar fun _ => bind (emit rfl) fun _ => pure' _) _) fun _ => pure' _

theorem nameGuard (e : Expr) : Quiet (Damp.nameGuard e) := by
  unfold Damp.nameGuard
  split
  · exact pure' _
  · exact pure' _
  · exact bind freshVar fun v => bind (emit rfl) fun _ => pure' _

theorem underGuard {α : Type} (g : Expr) {body : CircuitM α} (h : Quiet body) : Quiet (Damp.underGuard g body) :=
  fun s => by
    obtain ⟨T, hT, hq⟩ := h { s with guard := g }
    exact ⟨T, hT, hq⟩

theorem when_ (c : Boolean) {body : CircuitM Unit} (h : Quiet body) : Quiet (Damp.when_ c body) :=
  bind currentGuard fun _ => bind (nameGuard _) fun g => underGuard g h

theorem cond {α : Type} [Value α] (c : Boolean) {t e : CircuitM α} (ht : Quiet t) (he : Quiet e) :
    Quiet (Damp.cond c t e) := by
  rw [cond_eq]
  exact bind currentGuard fun _ => bind (nameGuard _) fun _ => bind (nameGuard _) fun _ =>
    bind (underGuard _ ht) fun _ => bind (underGuard _ he) fun _ =>
      bind (of_errors (condProblems_run _ _)) fun _ => pure' _

end Quiet

/-! ## The executor triple -/

/-- What a builder computation does when the executor runs its statements. -/
structure XRuns (p : Zkir.Prims) (O : Exec.Oracles ω σ) {α : Type} (m : CircuitM α) (s : Build)
    (st : Exec.State ω σ) (ok : Prop) (Q : α → Env → ω → σ → Prop) : Prop where
  next_le : s.next ≤ (m.run s).2.next
  guard : (m.run s).2.guard = s.guard
  exec : ∃ T, (m.run s).2.stmts.toList = s.stmts.toList ++ T ∧
    ((Exec.steps p O T st).isSome = true ↔ ok) ∧
    ∀ st', Exec.steps p O T st = some st' →
      Agree s.next st.env st'.env ∧
      Stable (m.run s).2.next st'.env (fun e => Q (m.run s).1 e st'.private_ st'.ledger)

namespace XRuns

theorem grows {α : Type} {m : CircuitM α} {s : Build} {st : Exec.State ω σ} {ok : Prop}
    {Q : α → Env → ω → σ → Prop} (h : XRuns p O m s st ok Q) :
    s.next ≤ (m.run s).2.next ∧ (m.run s).2.guard = s.guard ∧
      ∃ T, (m.run s).2.stmts.toList = s.stmts.toList ++ T := by
  obtain ⟨hn, hg, T, hT, -⟩ := h; exact ⟨hn, hg, T, hT⟩

/-- Weakening. -/
theorem conseq {α : Type} {m : CircuitM α} {s : Build} {st : Exec.State ω σ} {ok ok' : Prop}
    {Q Q' : α → Env → ω → σ → Prop}
    (h : XRuns p O m s st ok Q) (hok : ok ↔ ok') (hq : ∀ a e w l, Q a e w l → Q' a e w l) :
    XRuns p O m s st ok' Q' := by
  obtain ⟨hn, hg, T, hT, hs, hst⟩ := h
  refine ⟨hn, hg, T, hT, hs.trans hok, fun st' h' => ?_⟩
  obtain ⟨a, b⟩ := hst st' h'
  exact ⟨a, b.imp fun e => hq _ _ _ _⟩

/-- `pure a`. -/
theorem pure {α : Type} {a : α} {s : Build} {st : Exec.State ω σ} {Q : α → Env → ω → σ → Prop}
    (h : Stable s.next st.env (fun e => Q a e st.private_ st.ledger)) :
    XRuns p O (Pure.pure a : CircuitM α) s st True Q :=
  ⟨Nat.le_refl _, rfl, [], by simp [CircuitM.pure_run], by simp [Exec.steps],
    fun st' h' => by
      simp only [Exec.steps, Option.some.injEq] at h'; subst h'
      exact ⟨Agree.refl _ _, h⟩⟩

/-- **The pure fragment.** A computation that builds only quiet statements,
    described under the semantics by `Runs`, is described the same way for the
    executor, which then changes neither the private state nor the ledger. -/
theorem lift {α : Type} {m : CircuitM α} {s : Build} {st : Exec.State ω σ} {ok : Prop} {Q : α → Env → Prop}
    (h : Runs p m s st.runState ok Q) (hq : Quiet m) :
    XRuns p O m s st ok (fun a e w l => Q a e ∧ w = st.private_ ∧ l = st.ledger) := by
  obtain ⟨hn, hg, T, hT, hs, hst⟩ := h
  obtain ⟨T', hT', hqT⟩ := hq s
  have e : T' = T := List.append_cancel_left (hT'.symm.trans hT)
  subst e
  have hsteps := steps_quiet (p := p) (O := O) T' hqT st
  refine ⟨hn, hg, T', hT, by rw [hsteps]; simpa using hs, fun st' h' => ?_⟩
  rw [hsteps] at h'
  cases he : execAll p T' st.runState with
  | none => simp [he] at h'
  | some r =>
    simp only [he, Option.map_some, Option.some.injEq] at h'
    subst h'
    obtain ⟨ha, -, -, -, hQ⟩ := hst r he
    exact ⟨ha, hQ.imp fun e h => ⟨h, rfl, rfl⟩⟩

/-- Sequencing. -/
theorem bind {α β : Type} {m : CircuitM α} {f : α → CircuitM β} {s : Build} {st : Exec.State ω σ}
    {ok₁ ok₂ : Prop} {Q₁ : α → Env → ω → σ → Prop} {Q₂ : β → Env → ω → σ → Prop}
    (h₁ : XRuns p O m s st ok₁ Q₁) (hg : Grows (f (m.run s).1))
    (h₂ : ∀ st' : Exec.State ω σ, Agree s.next st.env st'.env →
      Stable (m.run s).2.next st'.env (fun e => Q₁ (m.run s).1 e st'.private_ st'.ledger) →
      XRuns p O (f (m.run s).1) (m.run s).2 st' ok₂ Q₂) :
    XRuns p O (m >>= f) s st (ok₁ ∧ ok₂) Q₂ := by
  obtain ⟨hn₁, hg₁, T₁, hT₁, hs₁, hst₁⟩ := h₁
  have hr := CircuitM.bind_run m f s
  cases he : Exec.steps p O T₁ st with
  | none =>
    have hno : ¬ ok₁ := by rw [← hs₁, he]; simp
    obtain ⟨hn₂, hg₂, T₂, hT₂⟩ := hg (m.run s).2
    refine ⟨?_, ?_, ?_⟩ <;> rw [hr]
    · exact Nat.le_trans hn₁ hn₂
    · exact hg₂.trans hg₁
    refine ⟨T₁ ++ T₂, by rw [hT₂, hT₁, List.append_assoc], ?_, ?_⟩
    · rw [steps_append, he]; simp [hno]
    · intro st' h'; rw [steps_append, he] at h'; cases h'
  | some st₁ =>
    have hok₁ : ok₁ := hs₁.1 (by rw [he]; rfl)
    obtain ⟨ha, hQ⟩ := hst₁ st₁ he
    obtain ⟨hn₂, hg₂, T₂, hT₂, hs₂, hst₂⟩ := h₂ st₁ ha hQ
    refine ⟨?_, ?_, ?_⟩ <;> rw [hr]
    · exact Nat.le_trans hn₁ hn₂
    · exact hg₂.trans hg₁
    refine ⟨T₁ ++ T₂, by rw [hT₂, hT₁, List.append_assoc], ?_, ?_⟩
    · rw [steps_append, he, Option.bind_some, hs₂]; simp [hok₁]
    · intro st' h'
      rw [steps_append, he, Option.bind_some] at h'
      obtain ⟨ha', hQ'⟩ := hst₂ st' h'
      exact ⟨ha.trans (ha'.mono hn₁), hQ'⟩

/-- Sequencing after a computation that always completes. -/
theorem bind' {α β : Type} {m : CircuitM α} {f : α → CircuitM β} {s : Build} {st : Exec.State ω σ}
    {ok₂ : Prop} {Q₁ : α → Env → ω → σ → Prop} {Q₂ : β → Env → ω → σ → Prop}
    (h₁ : XRuns p O m s st True Q₁) (hg : Grows (f (m.run s).1))
    (h₂ : ∀ st' : Exec.State ω σ, Agree s.next st.env st'.env →
      Stable (m.run s).2.next st'.env (fun e => Q₁ (m.run s).1 e st'.private_ st'.ledger) →
      XRuns p O (f (m.run s).1) (m.run s).2 st' ok₂ Q₂) :
    XRuns p O (m >>= f) s st ok₂ Q₂ :=
  (bind h₁ hg h₂).conseq (by simp) (fun _ _ _ _ h => h)

/-- Sequencing, with the first computation's result and builder state named:
    the second may assume the counter has not moved back and the guard is the
    same. -/
theorem seq {α β : Type} {m : CircuitM α} {f : α → CircuitM β} {s : Build} {st : Exec.State ω σ}
    {ok₁ ok₂ : Prop} {Q₁ : α → Env → ω → σ → Prop} {Q₂ : β → Env → ω → σ → Prop}
    (h₁ : XRuns p O m s st ok₁ Q₁) (hg : ∀ a, Grows (f a))
    (h₂ : ∀ (a : α) (s₁ : Build) (st₁ : Exec.State ω σ), s.next ≤ s₁.next → s₁.guard = s.guard →
      Agree s.next st.env st₁.env → Stable s₁.next st₁.env (fun e => Q₁ a e st₁.private_ st₁.ledger) →
      XRuns p O (f a) s₁ st₁ ok₂ Q₂) :
    XRuns p O (m >>= f) s st (ok₁ ∧ ok₂) Q₂ :=
  bind h₁ (hg _) fun st' ha hQ => h₂ _ _ st' h₁.grows.1 h₁.grows.2.1 ha hQ

end XRuns

/-! ## Ledger statements -/

/-- The groups a ledger statement declares exist whenever its request does. -/
theorem ledgerGroups_of_request {e : Env} {ops : List (Impact.Op Expr)} {req : List (Impact.Op Fr)}
    (h : Exec.request p e ops = some req) : ∃ gs, ledgerGroups p e true ops = some gs := by
  rw [Exec.ledgerGroups_eq_transcript]
  rw [Exec.request_eq_map] at h
  cases ht : Exec.transcript p e ops with
  | none => simp [ht] at h
  | some t => exact ⟨_, rfl⟩

theorem ledgerOp_run (reads : List Var) (ops : List (Impact.Op Expr)) (s : Build) :
    (ledgerOp reads ops).run s = ((), { s with stmts := s.stmts.push (.ledger s.guard reads ops) }) := rfl

/-- The guard of a statement built at `s`, under a guard meaning `gb`, evaluates
    in the executor's environment to the truth value. -/
theorem guard_eval {s : Build} {st : Exec.State ω σ} {gb : Bool} (hg : GuardIs p s st.runState gb) :
    s.guard.eval p st.env = some (Fr.ofBool gb) := hg.holds

/-- **A ledger operation that reads nothing**, under a guard that holds. The
    request it sends, in every environment agreeing with the current one below
    the counter, is answered with `res`; it completes exactly when the answer
    reads nothing, and leaves the ledger the answer gives. -/
theorem XRuns.ledgerOp {ops : List (Impact.Op Expr)} {s : Build} {st : Exec.State ω σ}
    {res : Option (List Fr × σ)} (hops : ops ≠ []) (hg : GuardIs p s st.runState true)
    (hreq : ∀ e, Agree s.next st.env e → ∃ req, Exec.request p e ops = some req ∧ O.ledger req st.ledger = res) :
    XRuns p O (Damp.ledgerOp [] ops) s st (∃ l, res = some ([], l))
      (fun _ _ w l => w = st.private_ ∧ res = some ([], l)) := by
  obtain ⟨req, hr, ho⟩ := hreq st.env (Agree.refl _ _)
  obtain ⟨gs, hgs⟩ := ledgerGroups_of_request hr
  have hne : (([] : List Var).isEmpty && ops.isEmpty) = false := by cases ops <;> simp_all
  have hstep : Exec.steps p O [.ledger s.guard [] ops] st =
      (res.bind fun r => if r.1 = [] then some { st with ledger := r.2, groups := st.groups ++ gs } else none) := by
    rw [steps_single]
    simp only [Exec.step, guard_eval hg, hne, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind,
      Option.bind_some, show asBool (Fr.ofBool true) = some true from rfl, hr, ho]
    cases res with
    | none => rfl
    | some r =>
      obtain ⟨vals, l⟩ := r
      cases vals with
      | nil => simp [Exec.assign, hgs]
      | cons v vs => simp [Exec.assign]
  refine ⟨Nat.le_refl _, rfl, [.ledger s.guard [] ops], by rw [ledgerOp_run]; exact Array.toList_push, ?_, ?_⟩
  · rw [hstep]
    cases res with
    | none => simp
    | some r => obtain ⟨vals, l⟩ := r; cases vals <;> simp
  · intro st' h'
    rw [hstep] at h'
    cases res with
    | none => simp at h'
    | some r =>
      obtain ⟨vals, l⟩ := r
      cases vals with
      | cons => simp at h'
      | nil =>
        simp only [Option.bind_some, ↓reduceIte, Option.some.injEq] at h'
        subst h'
        exact ⟨Agree.refl _ _, Stable.const ⟨rfl, rfl⟩⟩

/-- A ledger operation that reads nothing, under a guard that is off: the
    oracle is not asked, and nothing changes (the operands must evaluate). -/
theorem XRuns.ledgerOp_off {ops : List (Impact.Op Expr)} {s : Build} {st : Exec.State ω σ}
    (hops : ops ≠ []) (hg : GuardIs p s st.runState false)
    (hreq : ∃ req, Exec.request p st.env ops = some req) :
    XRuns p O (Damp.ledgerOp [] ops) s st True (fun _ _ w l => w = st.private_ ∧ l = st.ledger) := by
  obtain ⟨req, hr⟩ := hreq
  obtain ⟨gs, hgs⟩ := ledgerGroups_of_request hr
  have hne : (([] : List Var).isEmpty && ops.isEmpty) = false := by cases ops <;> simp_all
  have hstep : Exec.steps p O [.ledger s.guard [] ops] st =
      some { st with groups := st.groups ++ gs.map fun g => { active := false, vals := g.vals.map fun _ => 0 } } := by
    rw [steps_single]
    simp only [Exec.step, guard_eval hg, hne, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind,
      Option.bind_some, show asBool (Fr.ofBool false) = some false from rfl, List.map_nil, Exec.assign,
      ledgerGroups_off _ ops gs hgs]
    rfl
  refine ⟨Nat.le_refl _, rfl, [.ledger s.guard [] ops], by rw [ledgerOp_run]; exact Array.toList_push,
    by rw [hstep]; simp, fun st' h' => ?_⟩
  rw [hstep, Option.some.injEq] at h'
  subst h'
  exact ⟨Agree.refl _ _, Stable.const ⟨rfl, rfl⟩⟩

/-! ### Reading operations -/

/-- The variables `ledgerRead` reads into, built from `s`. -/
def readVarsAt (k w : Nat) : List Var := (List.range w).map (k + ·)

theorem ledgerRead_run (α : Type) [Value α] (mk : List Expr → List (Impact.Op Expr)) (s : Build) :
    (ledgerRead α mk).run s =
      (Value.ofExprs ((readVarsAt s.next (Value.width α)).map Expr.var),
       { s with next := s.next + Value.width α,
                stmts := s.stmts.push (.ledger s.guard (readVarsAt s.next (Value.width α))
                  (mk ((readVarsAt s.next (Value.width α)).map Expr.var))) }) := by
  have h := Ledger.mapM_freshVar (List.range (Value.width α)) s
  simp only [List.length_range] at h
  show (let r := ((List.range (Value.width α)).mapM (fun _ => freshVar)).run s;
        (Value.ofExprs (r.1.map Expr.var),
         { r.2 with stmts := r.2.stmts.push (.ledger r.2.guard r.1 (mk (r.1.map Expr.var))) })) = _
  rw [h]
  rfl

theorem readVarsAt_eq_range' (k w : Nat) : readVarsAt k w = List.range' k w := by
  unfold readVarsAt
  rw [List.range'_eq_map_range]

theorem readVarsAt_nodup (k w : Nat) : (readVarsAt k w).Nodup := by
  rw [readVarsAt_eq_range']; exact List.nodup_range'

theorem readVarsAt_ge {k w v : Nat} (h : v ∈ readVarsAt k w) : k ≤ v ∧ v < k + w := by
  unfold readVarsAt at h
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h
  simp at hi; omega

/-- Assigning distinct fresh variables: the environment agrees with the old one
    below them and maps them to the values. -/
theorem assign_readVarsAt {k w : Nat} {env env' : Env} {vals : List Fr}
    (h : Exec.assign env ((readVarsAt k w).map fun v => (v, none)) vals = some env') :
    Agree k env env' ∧ (readVarsAt k w).map env' = vals := by
  obtain ⟨h1, h2⟩ := Exec.assign_reads (readVarsAt k w) env env' vals (readVarsAt_nodup k w) h
  exact ⟨fun v hv => (h2 v fun hm => by have := (readVarsAt_ge hm).1; omega).symm, h1⟩

theorem assign_none_some : ∀ (reads : List Var) (env : Env) (vals : List Fr), vals.length = reads.length →
    ∃ env', Exec.assign env (reads.map fun v => (v, none)) vals = some env'
  | [], env, [], _ => ⟨env, rfl⟩
  | v :: rs, env, x :: xs, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [List.map_cons, Exec.assign]
    exact assign_none_some rs _ xs h
  | [], _, _ :: _, h => by simp at h
  | _ :: _, _, [], h => by simp at h

theorem assign_none_length : ∀ (reads : List Var) (env env' : Env) (vals : List Fr),
    Exec.assign env (reads.map fun v => (v, none)) vals = some env' → vals.length = reads.length
  | [], env, env', [], _ => rfl
  | v :: rs, env, env', x :: xs, h => by
    simp only [List.map_cons, Exec.assign] at h
    simp [assign_none_length rs _ env' xs h]
  | [], _, _, _ :: _, h => by simp [Exec.assign] at h
  | _ :: _, _, _, [], h => by simp [Exec.assign] at h

/-- The value a reading operation returns, from the variables it read into. -/
theorem read_value_is {α : Type} [Value α] (hrt : Value.RoundTrip α) {k : Nat} {env : Env} {ys : List Fr}
    (hys : (readVarsAt k (Value.width α)).map env = ys) :
    Stable (k + Value.width α) env
      (fun e => Value.Is p e (Value.ofExprs ((readVarsAt k (Value.width α)).map Expr.var) : α) ys) := by
  intro e he
  unfold Value.Is
  rw [hrt _ (by simp [readVarsAt]) p e]
  rw [readVarsAt_eq_range'] at hys ⊢
  have := evalList_argVars (p := p) e k (Value.width α)
  unfold argVars at this
  rw [this, ← hys]
  congr 1
  exact List.map_congr_left fun v hv => by
    have := List.mem_range'_1.1 hv; exact (he v (by omega)).symm

/-- A reading operation's instructions depend on the variables read into only
    through the `popeq`s, which the request blanks: the request is the same
    whichever variables they are. True of every reading operation of
    `Damp/Lang/Ledger.lean`, whose instructions end with the `popeq`
    (`ReadOps.request`). -/
def ReadOps (mk : List Expr → List (Impact.Op Expr)) : Prop :=
  ∀ (p : Zkir.Prims) (e : Env) (vs vs' : List Var),
    Exec.request p e (mk (vs.map Expr.var)) = Exec.request p e (mk (vs'.map Expr.var))

theorem request_append (e : Env) : ∀ (l₁ l₂ : List (Impact.Op Expr)),
    Exec.request p e (l₁ ++ l₂) = (do let a ← Exec.request p e l₁; let b ← Exec.request p e l₂; pure (a ++ b))
  | [], l₂ => by simp [Exec.request]
  | op :: l₁, l₂ => by
    simp only [List.cons_append, Exec.request, request_append e l₁ l₂]
    cases op.mapM (Expr.eval p e) <;> cases Exec.request p e l₁ <;> cases Exec.request p e l₂ <;> rfl

/-- Instructions ending with a `popeq` into the read variables are `ReadOps`. -/
theorem ReadOps.popeq_last (pre : List (Impact.Op Expr)) (c : Bool) (a : List Zkir.AlignAtom) :
    ReadOps fun es => pre ++ [.popeq c a es] := by
  intro p e vs vs'
  have h : ∀ vs : List Var, Exec.request p e [.popeq c a (vs.map Expr.var)] = some [.popeq c a []] := by
    intro vs
    have hv : ∀ vs : List Var, vs.mapM (Expr.eval p e ∘ Expr.var) = some (vs.map e) := by
      intro vs; induction vs with
      | nil => rfl
      | cons v vs ih => simp [List.mapM_cons, Expr.eval, ih]
    simp [Exec.request, Impact.Op.mapM, hv, Exec.blank]
  simp only [request_append, h]

/-- **A reading operation**, under a guard that holds: as `XRuns.ledgerOp`,
    the answer `res` given in every environment agreeing below the counter (to
    the request of the instructions read into `readVars α`, the form the
    specifications of `Damp/Proofs/Ledger/` take); it completes exactly when the
    answer has the type's width, and the result means the values read. -/
theorem XRuns.ledgerRead {α : Type} [Value α] (hrt : Value.RoundTrip α) {mk : List Expr → List (Impact.Op Expr)}
    (hmk : ReadOps mk) {s : Build} {st : Exec.State ω σ} {res : Option (List Fr × σ)}
    (hw : 0 < Value.width α) (hg : GuardIs p s st.runState true)
    (hreq : ∀ e, Agree s.next st.env e →
      ∃ req, Exec.request p e (mk (Ledger.readVars α)) = some req ∧ O.ledger req st.ledger = res) :
    XRuns p O (Damp.ledgerRead α mk) s st (∃ ys l, res = some (ys, l) ∧ ys.length = Value.width α)
      (fun r e w l => w = st.private_ ∧ ∃ ys, res = some (ys, l) ∧ Value.Is p e r ys) := by
  have hrv : Ledger.readVars α = (List.range (Value.width α)).map Expr.var := rfl
  let vs := readVarsAt s.next (Value.width α)
  have hreq' : ∀ e, Agree s.next st.env e →
      ∃ req, Exec.request p e (mk (vs.map Expr.var)) = some req ∧ O.ledger req st.ledger = res := by
    intro e he
    obtain ⟨req, h1, h2⟩ := hreq e he
    exact ⟨req, by rw [hmk p e vs (List.range (Value.width α)), ← hrv]; exact h1, h2⟩
  obtain ⟨req, hr, ho⟩ := hreq' st.env (Agree.refl _ _)
  have hne : (vs.isEmpty && (mk (vs.map Expr.var)).isEmpty) = false := by
    have : vs ≠ [] := by
      show readVarsAt s.next (Value.width α) ≠ []
      unfold readVarsAt; cases h : Value.width α with
      | zero => omega
      | succ n => simp [List.range_succ_eq_map]
    cases hv : vs with
    | nil => exact absurd hv this
    | cons => rfl
  have hrun := ledgerRead_run α mk s
  refine ⟨by rw [hrun]; exact Nat.le_add_right _ _, by rw [hrun], [.ledger s.guard vs (mk (vs.map Expr.var))],
    by rw [hrun]; exact Array.toList_push, ?_, ?_⟩
  · rw [steps_single]
    simp only [Exec.step, guard_eval hg, hne, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind,
      Option.bind_some, show asBool (Fr.ofBool true) = some true from rfl, hr, ho]
    constructor
    · intro h
      cases res with
      | none => simp at h
      | some r =>
        obtain ⟨vals, l⟩ := r
        simp only [Option.bind_some] at h
        cases ha : Exec.assign st.env (vs.map fun v => (v, none)) vals with
        | none => simp [ha] at h
        | some env' =>
          exact ⟨vals, l, rfl, by have := assign_none_length _ _ _ _ ha; simpa [vs, readVarsAt] using this⟩
    · rintro ⟨ys, l, rfl, hl⟩
      obtain ⟨env', ha⟩ := assign_none_some vs st.env ys (by simpa [vs, readVarsAt] using hl)
      obtain ⟨hag, -⟩ := assign_readVarsAt ha
      obtain ⟨req', hr', -⟩ := hreq' env' hag
      obtain ⟨gs, hgs⟩ := ledgerGroups_of_request hr'
      simp [ha, hgs]
  · intro st' h'
    rw [steps_single] at h'
    simp only [Exec.step, guard_eval hg, hne, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind,
      Option.bind_some, show asBool (Fr.ofBool true) = some true from rfl, hr, ho] at h'
    cases res with
    | none => simp at h'
    | some r =>
      obtain ⟨vals, l⟩ := r
      simp only [Option.bind_some] at h'
      cases ha : Exec.assign st.env (vs.map fun v => (v, none)) vals with
      | none => simp [ha] at h'
      | some env' =>
        simp only [ha, Option.bind_some] at h'
        cases hgs : ledgerGroups p env' true (mk (vs.map Expr.var)) with
        | none => simp [hgs] at h'
        | some gs =>
          simp only [hgs, Option.bind_some, Option.pure_def, Option.some.injEq] at h'
          subst h'
          obtain ⟨hag, hvals⟩ := assign_readVarsAt ha
          rw [hrun]
          exact ⟨hag, (read_value_is hrt hvals).imp fun e h => ⟨rfl, vals, rfl, h⟩⟩

/-- A reading operation under a guard that is off: the oracle is not asked,
    nothing changes, and the result is zero. -/
theorem XRuns.ledgerRead_off {α : Type} [Value α] (hrt : Value.RoundTrip α)
    {mk : List Expr → List (Impact.Op Expr)} (hmk : ReadOps mk) {s : Build} {st : Exec.State ω σ}
    (hw : 0 < Value.width α) (hg : GuardIs p s st.runState false)
    (hreq : ∀ e, Agree s.next st.env e → ∃ req, Exec.request p e (mk (Ledger.readVars α)) = some req) :
    XRuns p O (Damp.ledgerRead α mk) s st True
      (fun r e w l => w = st.private_ ∧ l = st.ledger ∧ Value.Is p e r (List.replicate (Value.width α) 0)) := by
  have hrv : Ledger.readVars α = (List.range (Value.width α)).map Expr.var := rfl
  let vs := readVarsAt s.next (Value.width α)
  have hne : (vs.isEmpty && (mk (vs.map Expr.var)).isEmpty) = false := by
    have : vs ≠ [] := by
      show readVarsAt s.next (Value.width α) ≠ []
      unfold readVarsAt; cases h : Value.width α with
      | zero => omega
      | succ n => simp [List.range_succ_eq_map]
    cases hv : vs with
    | nil => exact absurd hv this
    | cons => rfl
  obtain ⟨env', ha⟩ := assign_none_some vs st.env (vs.map fun _ => 0) (by simp)
  obtain ⟨hag, hvals⟩ := assign_readVarsAt ha
  obtain ⟨req', hr', -⟩ := (fun e he => (hreq e he).imp fun req h => ⟨h, trivial⟩ : ∀ e, Agree s.next st.env e →
    ∃ req, Exec.request p e (mk (Ledger.readVars α)) = some req ∧ True) env' hag
  rw [hrv, hmk p env' (List.range (Value.width α)) vs] at hr'
  obtain ⟨gs, hgs⟩ := ledgerGroups_of_request hr'
  have hgs' := ledgerGroups_off (p := p) env' _ gs hgs
  have hrun := ledgerRead_run α mk s
  have hstep : Exec.steps p O [.ledger s.guard vs (mk (vs.map Expr.var))] st =
      some { st with env := env',
                     groups := st.groups ++ gs.map fun g => { active := false, vals := g.vals.map fun _ => 0 } } := by
    rw [steps_single]
    simp only [Exec.step, guard_eval hg, hne, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind,
      Option.bind_some, show asBool (Fr.ofBool false) = some false from rfl, ha, hgs']
    rfl
  refine ⟨by rw [hrun]; exact Nat.le_add_right _ _, by rw [hrun], [.ledger s.guard vs (mk (vs.map Expr.var))],
    by rw [hrun]; exact Array.toList_push, by rw [hstep]; simp, fun st' h' => ?_⟩
  rw [hstep, Option.some.injEq] at h'
  subst h'
  rw [hrun]
  refine ⟨hag, (read_value_is hrt ?_).imp fun e h => ⟨rfl, rfl, h⟩⟩
  rw [hvals]; simp [vs, readVarsAt, Function.comp_def, List.map_const']

/-! ## Witness calls -/

theorem mapM_freshVar_ranges : ∀ (rs : List (Option Range)) (s : Build),
    (rs.mapM fun r => do pure ((← freshVar), r)).run s =
      ((List.range' s.next rs.length).zip rs, { s with next := s.next + rs.length })
  | [], s => by simp; rfl
  | r :: rs, s => by
    rw [List.mapM_cons]
    have h : ((((do pure ((← freshVar), r)) : CircuitM (Var × Option Range)) >>= fun a =>
        rs.mapM (fun r => do pure ((← freshVar), r)) >>= fun l => pure (a :: l)) : CircuitM _).run s =
        ((s.next, r) :: ((rs.mapM fun r => do pure ((← freshVar), r)).run { s with next := s.next + 1 }).1,
         ((rs.mapM fun r => do pure ((← freshVar), r)).run { s with next := s.next + 1 }).2) := rfl
    rw [h, mapM_freshVar_ranges rs]
    simp only [List.length_cons, List.range'_succ, List.zip_cons_cons]
    refine Prod.ext rfl ?_
    show Build.mk _ _ _ _ = Build.mk _ _ _ _
    congr 1; rw [Nat.add_assoc, Nat.add_comm 1]

theorem askWitness_run (name : String) (α : Type) [Value α] (args : List Expr) (s : Build) :
    ((askWitness name α args).run s).1 =
        Value.ofExprs ((List.range' s.next (Value.width α)).map Expr.var) ∧
      ((askWitness name α args).run s).2.next = s.next + Value.width α ∧
      ((askWitness name α args).run s).2.guard = s.guard ∧
      ((askWitness name α args).run s).2.stmts.toList = s.stmts.toList ++
        [.witness s.guard name args ((List.range' s.next (Value.width α)).zip (Value.ranges α)) (Value.shape α)] := by
  have h := mapM_freshVar_ranges (Value.ranges α) s
  have hc := checkUintBounds_run (Value.tys α)
    { s with next := s.next + (Value.ranges α).length,
             stmts := s.stmts.push (.witness s.guard name args
               ((List.range' s.next (Value.ranges α).length).zip (Value.ranges α)) (Value.shape α)) }
  have e : (askWitness name α args).run s =
      (Value.ofExprs (((List.range' s.next (Value.ranges α).length).zip (Value.ranges α)).map fun (v, _) => Expr.var v),
       ((checkUintBounds (Value.tys α)).run
         { s with next := s.next + (Value.ranges α).length,
                  stmts := s.stmts.push (.witness s.guard name args
                    ((List.range' s.next (Value.ranges α).length).zip (Value.ranges α)) (Value.shape α)) }).2) := by
    show (let r := ((Value.ranges α).mapM fun r => do pure ((← freshVar), r)).run s;
          let s1 := { r.2 with stmts := r.2.stmts.push (.witness s.guard name args r.1 (Value.shape α)) };
          (Value.ofExprs (r.1.map fun (v, _) => Expr.var v), ((checkUintBounds (Value.tys α)).run s1).2)) = _
    rw [h]
  have hm : (((List.range' s.next (Value.ranges α).length).zip (Value.ranges α)).map fun (v, _) => Expr.var v) =
      (List.range' s.next (Value.ranges α).length).map Expr.var :=
    map_zip_fst Expr.var _ _ (by simp)
  rw [e, hc]
  refine ⟨by rw [hm]; rfl, rfl, rfl, ?_⟩
  simp [Value.width]

/-- Binding fresh variables to values checked against ranges. -/
theorem assign_range' : ∀ (rs : List (Option Range)) (k : Nat) (env : Env) (ys : List Fr) (env' : Env),
    Exec.assign env ((List.range' k rs.length).zip rs) ys = some env' →
      (List.range' k rs.length).map env' = ys ∧ Agree k env env' ∧ rangesHold rs ys = true
  | [], k, env, [], env', h => by simp [Exec.assign] at h; subst h; exact ⟨rfl, Agree.refl _ _, rfl⟩
  | [], _, _, _ :: _, _, h => by simp [Exec.assign] at h
  | _ :: _, _, _, [], _, h => by simp [Exec.assign] at h
  | r :: rs, k, env, y :: ys, env', h => by
    simp only [List.length_cons, List.range'_succ, List.zip_cons_cons, Exec.assign] at h
    have hgo : Exec.assign (env.set k y) ((List.range' (k + 1) rs.length).zip rs) ys = some env' ∧
        r.all (·.holds y) = true := by
      cases r with
      | none => exact ⟨h, rfl⟩
      | some r =>
        simp only at h
        by_cases hh : r.holds y
        · simp only [hh, ↓reduceIte] at h; exact ⟨h, by simp [hh]⟩
        · simp [hh] at h
    obtain ⟨h1, h2, h3⟩ := assign_range' rs (k + 1) _ ys env' hgo.1
    have hag : Agree k env env' := (Agree.set (Nat.le_refl k) y).trans (h2.mono (Nat.le_succ k))
    refine ⟨?_, hag, ?_⟩
    · simp only [List.length_cons, List.range'_succ, List.map_cons, h1, List.cons.injEq, and_true]
      rw [← h2 k (Nat.lt_succ_self k)]; simp [Env.set]
    · simp only [rangesHold, List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h3 ⊢
      exact ⟨hgo.2, h3⟩

theorem assign_range'_some : ∀ (rs : List (Option Range)) (k : Nat) (env : Env) (ys : List Fr),
    ys.length = rs.length → rangesHold rs ys = true →
      ∃ env', Exec.assign env ((List.range' k rs.length).zip rs) ys = some env'
  | [], k, env, [], _, _ => ⟨env, rfl⟩
  | [], _, _, _ :: _, h, _ => by simp at h
  | _ :: _, _, _, [], h, _ => by simp at h
  | r :: rs, k, env, y :: ys, hl, hr => by
    simp only [rangesHold, List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hr
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    obtain ⟨env', h⟩ := assign_range'_some rs (k + 1) (env.set k y) ys hl hr.2
    refine ⟨env', ?_⟩
    simp only [List.length_cons, List.range'_succ, List.zip_cons_cons, Exec.assign]
    cases r with
    | none => exact h
    | some r =>
      have h1 : r.holds y = true := by simpa using hr.1
      simp [h1, h]

/-- **A witness call**, under a guard that holds, parameterized by the oracle's
    answer to the arguments' values: it completes exactly when the answer has the
    type's width and passes its range checks; then the result means the answer,
    the private state is the one the oracle returned, and the ledger is
    unchanged. -/
theorem XRuns.askWitness {α : Type} [Value α] (hrt : Value.RoundTrip α) (name : String) {args : List Expr}
    {argVals : List Fr} {s : Build} {st : Exec.State ω σ} (hw : 0 < Value.width α)
    (hg : GuardIs p s st.runState true) (hargs : Expr.evalList p st.env args = some argVals) :
    XRuns p O (Damp.askWitness name α args) s st
      (∃ ys w', O.witness name argVals st.private_ = some (ys, w') ∧ ys.length = Value.width α ∧
        rangesHold (Value.ranges α) ys = true)
      (fun r e w l => l = st.ledger ∧ ∃ ys, O.witness name argVals st.private_ = some (ys, w) ∧
        rangesHold (Value.ranges α) ys = true ∧ Value.Is p e r ys) := by
  obtain ⟨h1, h2, h3, h4⟩ := askWitness_run name α args s
  have hne : ((List.range' s.next (Value.width α)).zip (Value.ranges α)).isEmpty = false := by
    have : Value.width α = (Value.ranges α).length := rfl
    cases hr : Value.ranges α with
    | nil => rw [hr] at this; simp at this; omega
    | cons r rs =>
      rw [hr] at this; rw [this]; simp [List.range'_succ]
  have hstep : Exec.steps p O [.witness s.guard name args ((List.range' s.next (Value.width α)).zip (Value.ranges α))
      (Value.shape α)] st =
      (O.witness name argVals st.private_).bind fun r =>
        (Exec.assign st.env ((List.range' s.next (Value.width α)).zip (Value.ranges α)) r.1).map fun env =>
          { st with env, private_ := r.2, priv := st.priv ++ r.1 } := by
    rw [steps_single]
    simp only [Exec.step, guard_eval hg, hne, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind,
      Option.bind_some, show asBool (Fr.ofBool true) = some true from rfl, hargs]
    cases O.witness name argVals st.private_ with
    | none => rfl
    | some r =>
      obtain ⟨vals, w'⟩ := r
      simp only [Option.bind_some]
      cases Exec.assign st.env ((List.range' s.next (Value.width α)).zip (Value.ranges α)) vals <;> rfl
  refine ⟨by rw [h2]; exact Nat.le_add_right _ _, h3, _, h4, ?_, ?_⟩
  · rw [hstep]
    constructor
    · intro h
      cases hw' : O.witness name argVals st.private_ with
      | none => simp [hw'] at h
      | some r =>
        obtain ⟨vals, w'⟩ := r
        rw [hw'] at h
        cases ha : Exec.assign st.env ((List.range' s.next (Value.width α)).zip (Value.ranges α)) vals with
        | none => simp [ha] at h
        | some env' =>
          obtain ⟨hv, -, hr⟩ := assign_range' (Value.ranges α) s.next st.env vals env' ha
          exact ⟨vals, w', rfl, by rw [← hv]; simp [Value.width], hr⟩
    · rintro ⟨ys, w', hw', hl, hr⟩
      obtain ⟨env', ha⟩ := assign_range'_some (Value.ranges α) s.next st.env ys hl hr
      rw [hw']
      simp [show Value.width α = (Value.ranges α).length from rfl, ha]
  · intro st' h'
    rw [hstep] at h'
    cases hw' : O.witness name argVals st.private_ with
    | none => simp [hw'] at h'
    | some r =>
      obtain ⟨vals, w'⟩ := r
      rw [hw'] at h'
      cases ha : Exec.assign st.env ((List.range' s.next (Value.width α)).zip (Value.ranges α)) vals with
      | none => simp [ha] at h'
      | some env' =>
        simp only [ha, Option.bind_some, Option.map_some, Option.some.injEq] at h'
        subst h'
        obtain ⟨hv, hag, hr⟩ := assign_range' (Value.ranges α) s.next st.env vals env' ha
        refine ⟨hag, ?_⟩
        rw [h1, h2]
        have hv' : (readVarsAt s.next (Value.width α)).map env' = vals := by
          rw [readVarsAt_eq_range']; exact hv
        have := read_value_is (p := p) hrt hv'
        rw [readVarsAt_eq_range'] at this
        exact this.imp fun e h => ⟨rfl, vals, rfl, hr, h⟩

/-- A witness call under a guard that is off: the oracle is not asked, and the
    result is zero (every range of the type must accept 0). -/
theorem XRuns.askWitness_off {α : Type} [Value α] (hrt : Value.RoundTrip α) (name : String) {args : List Expr}
    {s : Build} {st : Exec.State ω σ} (hw : 0 < Value.width α) (hg : GuardIs p s st.runState false)
    (h0 : rangesHold (Value.ranges α) (List.replicate (Value.width α) 0) = true) :
    XRuns p O (Damp.askWitness name α args) s st True
      (fun r e w l => w = st.private_ ∧ l = st.ledger ∧ Value.Is p e r (List.replicate (Value.width α) 0)) := by
  obtain ⟨h1, h2, h3, h4⟩ := askWitness_run name α args s
  have hW : Value.width α = (Value.ranges α).length := rfl
  have hne : ((List.range' s.next (Value.width α)).zip (Value.ranges α)).isEmpty = false := by
    cases hr : Value.ranges α with
    | nil => rw [hr] at hW; simp at hW; omega
    | cons r rs => rw [hr] at hW; rw [hW]; simp [List.range'_succ]
  obtain ⟨env', ha⟩ := assign_range'_some (Value.ranges α) s.next st.env (List.replicate (Value.width α) 0)
    (by simp [hW]) h0
  have hz : (((List.range' s.next (Value.width α)).zip (Value.ranges α)).map fun _ => (0 : Fr)) =
      List.replicate (Value.width α) 0 := by simp [List.map_const', hW]
  have hstep : Exec.steps p O [.witness s.guard name args ((List.range' s.next (Value.width α)).zip (Value.ranges α))
      (Value.shape α)] st = some { st with env := env' } := by
    rw [steps_single]
    simp only [Exec.step, guard_eval hg, hne, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind,
      Option.bind_some, show asBool (Fr.ofBool false) = some false from rfl, hz]
    rw [hW] at ha ⊢
    simp [ha]
  refine ⟨by rw [h2]; exact Nat.le_add_right _ _, h3, _, h4, by rw [hstep]; simp, fun st' h' => ?_⟩
  rw [hstep, Option.some.injEq] at h'
  subst h'
  rw [hW] at ha
  obtain ⟨hv, hag, -⟩ := assign_range' (Value.ranges α) s.next st.env _ env' ha
  refine ⟨hag, ?_⟩
  rw [h1, h2]
  have hv' : (readVarsAt s.next (Value.width α)).map env' = List.replicate (Value.width α) 0 := by
    rw [readVarsAt_eq_range']; rw [hW]; exact hv
  have := read_value_is (p := p) hrt hv'
  rw [readVarsAt_eq_range'] at this
  exact this.imp fun e h => ⟨rfl, rfl, h⟩

/-! ## Building only appends -/

theorem Grows.ledgerOp (reads : List Var) (ops : List (Impact.Op Expr)) : Grows (Damp.ledgerOp reads ops) :=
  fun s => by rw [ledgerOp_run]; exact ⟨Nat.le_refl _, rfl, _, Array.toList_push⟩

theorem Grows.ledgerRead (α : Type) [Value α] (mk : List Expr → List (Impact.Op Expr)) :
    Grows (Damp.ledgerRead α mk) :=
  fun s => by rw [ledgerRead_run]; exact ⟨Nat.le_add_right _ _, rfl, _, Array.toList_push⟩

theorem Grows.askWitness (name : String) (α : Type) [Value α] (args : List Expr) :
    Grows (Damp.askWitness name α args) := fun s => by
  obtain ⟨-, h2, h3, h4⟩ := askWitness_run name α args s
  exact ⟨by rw [h2]; exact Nat.le_add_right _ _, h3, _, h4⟩

/-! ## Guards: `when_` -/

/-- `underGuard g body` runs `body` with `g` as the guard, then restores the guard. -/
theorem XRuns.underGuard {α : Type} {g : Expr} {body : CircuitM α} {s : Build} {st : Exec.State ω σ} {ok : Prop}
    {Q : α → Env → ω → σ → Prop} (h : XRuns p O body { s with guard := g } st ok Q) :
    XRuns p O (Damp.underGuard g body) s st ok Q := by
  have hrun : (Damp.underGuard g body).run s =
      ((body.run { s with guard := g }).1, { (body.run { s with guard := g }).2 with guard := s.guard }) := rfl
  obtain ⟨hn, -, T, hT, hs, hst⟩ := h
  exact ⟨by rw [hrun]; exact hn, by rw [hrun], T, by rw [hrun]; exact hT, hs, by rw [hrun]; exact hst⟩

/-- What a branch may assume about the state it is built in: no earlier than the
    branch point, an environment agreeing below the branch point's counter, the
    same private and ledger states, and a guard meaning `g`. -/
def XBranchCtx (p : Zkir.Prims) (s : Build) (st : Exec.State ω σ) (g : Bool) (s' : Build)
    (st' : Exec.State ω σ) : Prop :=
  s.next ≤ s'.next ∧ Agree s.next st.env st'.env ∧ st'.private_ = st.private_ ∧ st'.ledger = st.ledger ∧
    GuardIs p s' st'.runState g

theorem XBranchCtx.transfer {s : Build} {st : Exec.State ω σ} {g : Bool} {s' : Build} {st' : Exec.State ω σ}
    (h : XBranchCtx p s st g s' st') {P : Env → Prop} (hP : Stable s.next st.env P) : Stable s'.next st'.env P :=
  (hP.transfer h.2.1).mono h.1

/-- **`when_` (`if%` without `else`) with effects.** Under a guard meaning `gb`,
    with the condition meaning `cb`: the body is built under the guard `gb ∧ cb`,
    and the whole is described by the body's description in every state it may
    be built in. With the guard off, the body's ledger operations and witness
    calls are described by the `*_off` rules: nothing is asked, nothing changes. -/
theorem XRuns.when_ {c : Boolean} {body : CircuitM Unit} {s : Build} {st : Exec.State ω σ} {gb cb : Bool}
    {ok : Prop} {Q : Unit → Env → ω → σ → Prop}
    (hg : GuardIs p s st.runState gb) (hc : Stable s.next st.env (fun e => Boolean.Is p e c cb))
    (gbody : Grows body)
    (hb : ∀ s' st', XBranchCtx p s st (gb && cb) s' st' → XRuns p O body s' st' ok Q) :
    XRuns p O (Damp.when_ c body) s st ok Q := by
  unfold Damp.when_
  refine XRuns.bind' (XRuns.lift (Runs.currentGuard (p := p) (s := s) (st := st.runState)) Quiet.currentGuard)
    (Grows.bind (Grows.nameGuard _) fun _ => Grows.underGuard _ gbody) fun st₀ ha₀ hQ₀ => ?_
  have hout : (Damp.currentGuard.run s).1 = s.guard := rfl
  have hs₀ : (Damp.currentGuard.run s).2 = s := rfl
  rw [hout, hs₀]
  rw [hs₀] at hQ₀
  obtain ⟨-, hw₀, hl₀⟩ := hQ₀.holds
  have hgt : Stable s.next st₀.env (fun env => (guardAnd s.guard c.expr).eval p env = some (Fr.ofBool (gb && cb))) :=
    ((hg.transfer ha₀).and (hc.transfer ha₀)).imp fun env h => guardAnd_eval h.1 h.2
  refine XRuns.bind' (XRuns.lift (Runs.nameGuard (p := p) (st := st₀.runState) hgt) (Quiet.nameGuard _))
    (Grows.underGuard _ gbody) fun st₁ ha₁ hQ₁ => ?_
  have hn₁ := (Grows.nameGuard (guardAnd s.guard c.expr) s).1
  generalize (Damp.nameGuard (guardAnd s.guard c.expr)).run s = q₁ at hQ₁ hn₁ ⊢
  obtain ⟨g, s₁⟩ := q₁
  simp only at hQ₁ hn₁ ⊢
  obtain ⟨-, hw₁, hl₁⟩ := hQ₁.holds
  exact XRuns.underGuard (hb _ _ ⟨hn₁, ha₀.trans (ha₁.mono (Nat.le_refl _)), hw₁.trans hw₀, hl₁.trans hl₀,
    hQ₁.imp fun e h => h.1⟩)

/-- **`if%` with effects in both branches.** Under a guard meaning `gb`, with
    the condition meaning `cb`: the `then` branch is built under `gb ∧ cb` from a
    state with the ledger and private state unchanged (`XBranchCtx`); the `else`
    branch under `gb ∧ ¬cb`, from the state the `then` branch left, described for
    each result `a` of the `then` branch and every such state satisfying `Qt a`.
    The conditional completes exactly when both do, and its result is
    `select c a b` (the taken branch's value, `select_*`). -/
theorem XRuns.cond {α : Type} [Value α] {c : Boolean} {t e : CircuitM α} {s : Build} {st : Exec.State ω σ}
    {gb cb : Bool} {okt oke : Prop} {Qt : α → Env → ω → σ → Prop} {Qe : α → α → Env → ω → σ → Prop}
    (hg : GuardIs p s st.runState gb) (hc : Stable s.next st.env (fun env => Boolean.Is p env c cb))
    (gt : Grows t) (ge : Grows e)
    (ht : ∀ s' st', XBranchCtx p s st (gb && cb) s' st' → XRuns p O t s' st' okt Qt)
    (he : ∀ a s' (st' : Exec.State ω σ), s.next ≤ s'.next → Agree s.next st.env st'.env →
      GuardIs p s' st'.runState (gb && !cb) → Stable s'.next st'.env (fun env => Qt a env st'.private_ st'.ledger) →
      XRuns p O e s' st' oke (Qe a)) :
    XRuns p O (Damp.cond c t e) s st (okt ∧ oke)
      (fun r env w l => ∃ a b, r = select c a b ∧ Qe a b env w l ∧ Boolean.Is p env c cb) := by
  rw [cond_eq]
  refine (XRuns.seq (ok₂ := okt ∧ oke) (XRuns.lift (Runs.currentGuard (p := p) (s := s) (st := st.runState)) Quiet.currentGuard)
    (fun _ => Grows.bind (Grows.nameGuard _) fun _ => Grows.bind (Grows.nameGuard _) fun _ =>
      Grows.bind (Grows.underGuard _ gt) fun _ => Grows.bind (Grows.underGuard _ ge) fun _ =>
      Grows.bind (Grows.of_errors (condProblems_run _ _)) fun _ => Grows.pure' _)
    fun g₀ s₀ st₀ hn₀ hgd₀ ha₀ hQ₀ => ?_).conseq (ok' := okt ∧ oke) (by simp) (fun _ _ _ _ h => h)
  obtain ⟨hg₀, hw₀, hl₀⟩ := hQ₀.holds
  subst hg₀
  have hgt : Stable s₀.next st₀.env
      (fun env => (guardAnd s.guard c.expr).eval p env = some (Fr.ofBool (gb && cb))) :=
    (((hg.transfer ha₀).and (hc.transfer ha₀)).imp fun env h => guardAnd_eval h.1 h.2).mono hn₀
  refine (XRuns.seq (ok₂ := okt ∧ oke) (XRuns.lift (Runs.nameGuard (p := p) (st := st₀.runState) hgt) (Quiet.nameGuard _))
    (fun _ => Grows.bind (Grows.nameGuard _) fun _ =>
      Grows.bind (Grows.underGuard _ gt) fun _ => Grows.bind (Grows.underGuard _ ge) fun _ =>
      Grows.bind (Grows.of_errors (condProblems_run _ _)) fun _ => Grows.pure' _)
    fun gtE s₁ st₁ hn₁ hgd₁ ha₁ hQ₁ => ?_).conseq (ok' := okt ∧ oke) (by simp) (fun _ _ _ _ h => h)
  obtain ⟨-, hw₁, hl₁⟩ := hQ₁.holds
  have hnc : Stable s.next st₁.env (fun env => Boolean.Is p env c.not (!cb)) :=
    (hc.transfer (ha₀.trans (ha₁.mono hn₀))).imp fun env h => Boolean.not_is h
  have hge : Stable s₁.next st₁.env
      (fun env => (guardAnd s.guard c.not.expr).eval p env = some (Fr.ofBool (gb && !cb))) :=
    (((hg.transfer (ha₀.trans (ha₁.mono hn₀))).and hnc).imp fun env h => guardAnd_eval h.1 h.2).mono
      (Nat.le_trans hn₀ hn₁)
  refine (XRuns.seq (ok₂ := okt ∧ oke) (XRuns.lift (Runs.nameGuard (p := p) (st := st₁.runState) hge) (Quiet.nameGuard _))
    (fun _ => Grows.bind (Grows.underGuard _ gt) fun _ => Grows.bind (Grows.underGuard _ ge) fun _ =>
      Grows.bind (Grows.of_errors (condProblems_run _ _)) fun _ => Grows.pure' _)
    fun geE s₂ st₂ hn₂ hgd₂ ha₂ hQ₂ => ?_).conseq (ok' := okt ∧ oke) (by simp) (fun _ _ _ _ h => h)
  obtain ⟨-, hw₂, hl₂⟩ := hQ₂.holds
  have hA₂ : Agree s.next st.env st₂.env := ha₀.trans ((ha₁.mono hn₀).trans (ha₂.mono (Nat.le_trans hn₀ hn₁)))
  have ctxT : XBranchCtx p s st (gb && cb) { s₂ with guard := gtE } st₂ :=
    ⟨Nat.le_trans hn₀ (Nat.le_trans hn₁ hn₂), hA₂, hw₂.trans (hw₁.trans hw₀), hl₂.trans (hl₁.trans hl₀),
      ((hQ₁.imp fun env h => h.1).transfer ha₂).mono hn₂⟩
  refine (XRuns.seq (ok₂ := oke) (XRuns.underGuard (ht _ _ ctxT))
    (fun _ => Grows.bind (Grows.underGuard _ ge) fun _ =>
      Grows.bind (Grows.of_errors (condProblems_run _ _)) fun _ => Grows.pure' _)
    fun a s₃ st₃ hn₃ hgd₃ ha₃ hQ₃ => ?_).conseq Iff.rfl (fun _ _ _ _ h => h)
  have hA₃ : Agree s.next st.env st₃.env := hA₂.trans (ha₃.mono ctxT.1)
  refine (XRuns.seq (ok₂ := True) (XRuns.underGuard (he a { s₃ with guard := geE } st₃
      (Nat.le_trans ctxT.1 hn₃) hA₃ (((hQ₂.imp fun env h => h.1).transfer ha₃).mono hn₃) hQ₃))
    (fun _ => Grows.bind (Grows.of_errors (condProblems_run _ _)) fun _ => Grows.pure' _)
    fun b s₄ st₄ hn₄ hgd₄ ha₄ hQ₄ => ?_).conseq (by simp) (fun _ _ _ _ h => h)
  have hA₄ : Agree s.next st.env st₄.env := hA₃.trans (ha₄.mono (Nat.le_trans ctxT.1 hn₃))
  have hs₅ := condProblems_run a b s₄
  refine (XRuns.seq (ok₂ := True) (XRuns.lift (Runs.ofErrors (p := p) (st := st₄.runState) (condProblems_run a b)
      (Q := fun _ _ => True) (Stable.const trivial)) (Quiet.of_errors (condProblems_run a b)))
    (fun _ => Grows.pure' _) fun u s₅ st₅ hn₅ hgd₅ ha₅ hQ₅ => ?_).conseq (by simp) (fun _ _ _ _ h => h)
  obtain ⟨-, hw₅, hl₅⟩ := hQ₅.holds
  have hn45 : ((condProblems a b).run s₄).2.next = s₄.next := by rw [hs₅]
  refine XRuns.pure fun env hag => ⟨a, b, rfl, ?_, ?_⟩
  · have h4 := hQ₄.transfer ha₅
    rw [hw₅, hl₅]
    exact h4 env (hag.mono (by first | exact hn₅ | (rw [hn45]; exact hn₅)))
  · exact (hc.transfer (hA₄.trans (ha₅.mono (Nat.le_trans ctxT.1 (Nat.le_trans hn₃ hn₄))))) env
      (hag.mono (Nat.le_trans (Nat.le_trans ctxT.1 (Nat.le_trans hn₃ hn₄)) (by first | exact hn₅ | (rw [hn45]; exact hn₅))))

/-! ## Circuits -/

/-- `Exec.run` of a circuit `mkCircuit` builds: on inputs of the right number
    passing their range checks, the executor runs the body's statements from
    the inputs, the private state and the ledger state, and reads the outputs. -/
theorem mkCircuit_exec {φ : Type} [CircuitFn φ] [CircuitFnSpec φ] (name : String) (names : List String) (f : φ)
    (xs : List Fr) (w : ω) (l : σ) :
    Exec.run p O (mkCircuit name names f) xs w l =
      if xs.length = (CircuitFnSpec.ranges φ).length ∧ rangesHold (CircuitFnSpec.ranges φ) xs = true then
        let r := (CircuitFnSpec.apply f (argVars 0 (CircuitFnSpec.ranges φ).length)).run
          { next := (CircuitFnSpec.ranges φ).length }
        (Exec.steps p O r.2.stmts.toList (Exec.State.start (fun v => xs.getD v 0) w l)).bind
          fun s => (Expr.evalList p s.env (Value.toExprs r.1)).map fun outputs =>
            { outputs, priv := s.priv, pub := s.pub, groups := s.groups, private_ := s.private_, ledger := s.ledger }
      else none := by
  have hb := CircuitFnSpec.build_run f names {}
  unfold mkCircuit
  generalize (CircuitFn.build f names).run {} = q at hb
  obtain ⟨sig, st⟩ := q
  obtain ⟨hi, ho, -, hst⟩ := hb
  have h0 : ({ ({} : Build) with next := ({} : Build).next + (CircuitFnSpec.ranges φ).length } : Build)
      = { next := (CircuitFnSpec.ranges φ).length } := by simp
  rw [h0] at ho hst
  simp only at hi ho hst ⊢
  generalize (CircuitFnSpec.apply f (argVars 0 (CircuitFnSpec.ranges φ).length)).run
    { next := (CircuitFnSpec.ranges φ).length } = r at ho hst
  generalize hrs : CircuitFnSpec.ranges φ = rs at hi ho hst
  have hlen : sig.inputs.length = rs.length := by
    have := congrArg List.length hi; simpa using this
  have hvars : sig.inputs.map (·.var) = List.range' 0 sig.inputs.length := by
    have := congrArg (List.map Prod.fst) hi
    rw [List.map_map, List.map_fst_zip (by simp)] at this
    rw [hlen]; exact this
  simp only [Exec.run]
  rw [bindInputs_consecutive _ 0 _ xs hvars, hlen]
  by_cases hx : xs.length = rs.length
  · have henv : (fun v => if 0 ≤ v ∧ v < 0 + rs.length then xs.getD (v - 0) 0 else (fun _ => (0 : Fr)) v)
        = fun v => xs.getD v 0 := by
      funext v; split
      · simp
      · rename_i h; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show xs.length ≤ v by omega)]
    simp only [hx, ↓reduceIte, henv, Array.toList_append, Option.bind_some]
    have hq : ∀ x ∈ inputChecks sig.inputs, x.quiet = true := by
      intro x hx
      simp only [inputChecks, List.mem_filterMap] at hx
      obtain ⟨i, -, hi⟩ := hx
      cases hr : i.range with
      | none => simp [hr] at hi
      | some r => simp [hr] at hi; subst hi; rfl
    change ((Exec.steps p O (inputChecks sig.inputs ++ st.stmts.toList)
      (Exec.State.start (fun v => xs.getD v 0) w l)).bind _) = _
    rw [steps_append, steps_quiet _ hq, execAll_inputChecks_eq]
    have hall : (sig.inputs.all fun i => i.range.all (·.holds (xs.getD i.var 0))) = rangesHold rs xs := by
      have := congrArg (List.all · fun (vr : Nat × Option Range) => vr.2.all (·.holds (xs.getD vr.1 0))) hi
      simp only [List.all_map] at this
      rw [← all_zip_range' (fun v => xs.getD v 0) 0 rs xs hx (fun j hj => by simp [hj])]
      exact this
    simp only [Exec.State.runState, Exec.State.start, hall]
    by_cases hh : rangesHold rs xs = true
    · have hstm : st.stmts = r.2.stmts := (congrArg Build.stmts hst :)
      simp only [hh, ↓reduceIte, true_and, hstm, ho, Option.map_some, Option.bind_some]
      congr 1; funext s'; cases Expr.evalList p s'.env (Value.toExprs r.fst) <;> rfl
    · simp [hh]
  · simp [hx]

/-- **Contract-level runs through the executor.** If the body, applied to the
    arguments read off the input variables, is described by `XRuns` from the
    inputs, the private state `w` and the ledger state `l`, with outputs `outs`
    and a final private and ledger state satisfying `P`, then on inputs of the
    right number that pass their range checks the executor completes exactly
    when `ok` holds, and then outputs `outs` and leaves states satisfying `P`. -/
theorem mkCircuit_exec_of_XRuns {φ : Type} [CircuitFn φ] [CircuitFnSpec φ] (name : String) (names : List String)
    (f : φ) {xs : List Fr} {w : ω} {l : σ} {ok : Prop} {outs : List Fr} {P : ω → σ → Prop}
    (hlen : xs.length = (CircuitFnSpec.ranges φ).length)
    (hr : rangesHold (CircuitFnSpec.ranges φ) xs = true)
    (h : XRuns p O (CircuitFnSpec.apply f (argVars 0 (CircuitFnSpec.ranges φ).length))
      { next := (CircuitFnSpec.ranges φ).length } (Exec.State.start (fun v => xs.getD v 0) w l) ok
      (fun r e w' l' => Value.Is p e r outs ∧ P w' l')) :
    ((Exec.run p O (mkCircuit name names f) xs w l).isSome = true ↔ ok) ∧
      ∀ r, Exec.run p O (mkCircuit name names f) xs w l = some r → r.outputs = outs ∧ P r.private_ r.ledger := by
  rw [mkCircuit_exec]
  simp only [hlen, hr, and_self, ↓reduceIte]
  obtain ⟨-, -, T, hT, hs, hst⟩ := h
  have hT' : ((CircuitFnSpec.apply f (argVars 0 (CircuitFnSpec.ranges φ).length)).run
      { next := (CircuitFnSpec.ranges φ).length }).2.stmts.toList = T := by rw [hT]; rfl
  rw [hT']
  cases he : Exec.steps p O T (Exec.State.start (fun v => xs.getD v 0) w l) with
  | none =>
    have : ¬ ok := by rw [← hs, he]; simp
    simp [this]
  | some st' =>
    have hok : ok := hs.1 (by rw [he]; rfl)
    obtain ⟨-, hQ⟩ := hst st' he
    have hQ' := hQ.holds
    have hout := hQ'.1
    unfold Value.Is at hout
    simp only [Option.bind_some, hout, Option.map_some, Option.isSome_some, true_iff]
    refine ⟨hok, fun r hr => ?_⟩
    simp only [Option.some.injEq] at hr
    subst hr
    exact ⟨rfl, hQ'.2⟩

end Damp
