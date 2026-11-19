/-
A small program logic for the builder monad.

`Runs p m s st ok Q` describes a builder computation `m` started from builder
state `s`, whose statements are then executed from run state `st`:

* building appends statements `T` to `s.stmts`, keeps the guard, and does not
  move the variable counter back;
* executing `T` from `st` succeeds exactly when `ok` holds;
* when it does, it changes the environment only at variables numbered
  `s.next` or above (the ones `m` allocated), leaves both transcripts and the
  public-input groups alone, and the result `r` satisfies `Q r` in the final
  environment and in every environment that agrees with it below the final
  counter.

The last clause ("stable" facts) is what makes the logic compositional without
any syntactic freshness argument: statements built later only assign variables
at or above the counter at that time, so a stable fact survives them
(`Runs.bind`). Facts about the circuit arguments are stable from the start,
since the arguments are the variables below the first counter.

The fragment covers what does not touch the transcripts: `require`, `val`,
the checked `Uint` operations, `when_`, `cond`; witness calls and ledger
operations are described at the statement level in `Control.lean`.
-/
import Damp.Proofs.Interface.Compare

namespace Damp
open IR

/-- Two environments agree on the variables below `k`. -/
def Agree (k : Nat) (e e' : Env) : Prop := ∀ v, v < k → e v = e' v

/-- `P` holds in `env` and in every environment that agrees with it below `k`. -/
def Stable (k : Nat) (env : Env) (P : Env → Prop) : Prop := ∀ env', Agree k env env' → P env'

theorem Agree.refl (k : Nat) (e : Env) : Agree k e e := fun _ _ => rfl
theorem Agree.trans {k : Nat} {a b c : Env} (h1 : Agree k a b) (h2 : Agree k b c) : Agree k a c :=
  fun v hv => (h1 v hv).trans (h2 v hv)
theorem Agree.symm {k : Nat} {a b : Env} (h : Agree k a b) : Agree k b a := fun v hv => (h v hv).symm
theorem Agree.mono {k k' : Nat} {a b : Env} (hk : k ≤ k') (h : Agree k' a b) : Agree k a b :=
  fun v hv => h v (Nat.lt_of_lt_of_le hv hk)
theorem Agree.set {k : Nat} {e : Env} {v : Var} (hv : k ≤ v) (x : Fr) : Agree k e (e.set v x) := by
  intro w hw
  show e w = (if w = v then x else e w)
  simp only [Nat.ne_of_lt (Nat.lt_of_lt_of_le hw hv), ↓reduceIte]

theorem Stable.holds {k : Nat} {env : Env} {P : Env → Prop} (h : Stable k env P) : P env := h env (Agree.refl _ _)
theorem Stable.mono {k k' : Nat} {env : Env} {P : Env → Prop} (hk : k ≤ k') (h : Stable k env P) :
    Stable k' env P := fun e he => h e (Agree.mono hk he)
theorem Stable.transfer {k : Nat} {env env' : Env} {P : Env → Prop} (he : Agree k env env') (h : Stable k env P) :
    Stable k env' P := fun e he' => h e (he.trans he')
theorem Stable.and {k : Nat} {env : Env} {P Q : Env → Prop} (h1 : Stable k env P) (h2 : Stable k env Q) :
    Stable k env (fun e => P e ∧ Q e) := fun e he => ⟨h1 e he, h2 e he⟩
theorem Stable.imp {k : Nat} {env : Env} {P Q : Env → Prop} (h : Stable k env P) (hpq : ∀ e, P e → Q e) :
    Stable k env Q := fun e he => hpq e (h e he)
theorem Stable.const {k : Nat} {env : Env} {P : Prop} (h : P) : Stable k env (fun _ => P) := fun _ _ => h

/-- The value of variable `v < k` is stable below `k`. -/
theorem Stable.var {k : Nat} {env : Env} {v : Var} (hv : v < k) :
    Stable k env (fun e => (Expr.var v).eval p e = some (env v)) := fun e he => by
  show some (e v) = some (env v); rw [he v hv]

/-- Building `m` from any state only appends statements, keeps the guard and does not move
    the counter back. -/
def Grows {α : Type} (m : CircuitM α) : Prop :=
  ∀ s : Build, s.next ≤ (m.run s).2.next ∧ (m.run s).2.guard = s.guard ∧
    ∃ T, (m.run s).2.stmts.toList = s.stmts.toList ++ T

/-- What a builder computation does when its statements run. -/
structure Runs (p : Zkir.Prims) {α : Type} (m : CircuitM α) (s : Build) (st : RunState) (ok : Prop)
    (Q : α → Env → Prop) : Prop where
  next_le : s.next ≤ (m.run s).2.next
  guard : (m.run s).2.guard = s.guard
  exec : ∃ T, (m.run s).2.stmts.toList = s.stmts.toList ++ T ∧
    ((execAll p T st).isSome = true ↔ ok) ∧
    ∀ st', execAll p T st = some st' →
      Agree s.next st.env st'.env ∧ st'.priv = st.priv ∧ st'.pub = st.pub ∧ st'.groups = st.groups ∧
      Stable (m.run s).2.next st'.env (Q (m.run s).1)

namespace Runs
variable {p : Zkir.Prims}

/-- Weakening. -/
theorem conseq {α : Type} {m : CircuitM α} {s : Build} {st : RunState} {ok ok' : Prop} {Q Q' : α → Env → Prop}
    (h : Runs p m s st ok Q) (hok : ok ↔ ok') (hq : ∀ a e, Q a e → Q' a e) : Runs p m s st ok' Q' := by
  obtain ⟨hn, hg, T, hT, hs, hst⟩ := h
  refine ⟨hn, hg, T, hT, hs.trans hok, fun st' h' => ?_⟩
  obtain ⟨a, b, c, d, e⟩ := hst st' h'
  exact ⟨a, b, c, d, e.imp (hq _)⟩

/-- `pure a`: nothing is built; the result satisfies whatever stable fact holds of `a`. -/
theorem pure {α : Type} {a : α} {s : Build} {st : RunState} {Q : α → Env → Prop}
    (h : Stable s.next st.env (Q a)) : Runs p (Pure.pure a : CircuitM α) s st True Q :=
  ⟨Nat.le_refl _, rfl, [], by simp [CircuitM.pure_run], by simp [execAll],
    fun st' h' => by
      simp only [execAll, Option.some.injEq] at h'; subst h'
      exact ⟨Agree.refl _ _, rfl, rfl, rfl, h⟩⟩

/-- Sequencing: the second computation may assume what the first established, in the run
    state the first left. That the second only appends statements is needed separately (`hg`),
    for the runs where the first fails. -/
theorem bind {α β : Type} {m : CircuitM α} {f : α → CircuitM β} {s : Build} {st : RunState}
    {ok₁ ok₂ : Prop} {Q₁ : α → Env → Prop} {Q₂ : β → Env → Prop}
    (h₁ : Runs p m s st ok₁ Q₁) (hg : Grows (f (m.run s).1))
    (h₂ : ∀ st' : RunState, Agree s.next st.env st'.env → st'.priv = st.priv → st'.pub = st.pub →
      st'.groups = st.groups → Stable (m.run s).2.next st'.env (Q₁ (m.run s).1) →
      Runs p (f (m.run s).1) (m.run s).2 st' ok₂ Q₂) :
    Runs p (m >>= f) s st (ok₁ ∧ ok₂) Q₂ := by
  obtain ⟨hn₁, hg₁, T₁, hT₁, hs₁, hst₁⟩ := h₁
  have hr := CircuitM.bind_run m f s
  cases he : execAll p T₁ st with
  | none =>
    have hno : ¬ ok₁ := by rw [← hs₁, he]; simp
    obtain ⟨hn₂, hg₂, T₂, hT₂⟩ := hg (m.run s).2
    refine ⟨?_, ?_, ?_⟩ <;> rw [hr]
    · exact Nat.le_trans hn₁ hn₂
    · exact hg₂.trans hg₁
    refine ⟨T₁ ++ T₂, by rw [hT₂, hT₁, List.append_assoc], ?_, ?_⟩
    · rw [execAll_append, he]; simp [hno]
    · intro st' h'; rw [execAll_append, he] at h'; cases h'
  | some st₁ =>
    have hok₁ : ok₁ := hs₁.1 (by rw [he]; rfl)
    obtain ⟨ha, hpriv, hpub, hgr, hQ⟩ := hst₁ st₁ he
    obtain ⟨hn₂, hg₂, T₂, hT₂, hs₂, hst₂⟩ := h₂ st₁ ha hpriv hpub hgr hQ
    refine ⟨?_, ?_, ?_⟩ <;> rw [hr]
    · exact Nat.le_trans hn₁ hn₂
    · exact hg₂.trans hg₁
    refine ⟨T₁ ++ T₂, by rw [hT₂, hT₁, List.append_assoc], ?_, ?_⟩
    · rw [execAll_append, he, Option.bind_some, hs₂]; simp [hok₁]
    · intro st' h'
      rw [execAll_append, he, Option.bind_some] at h'
      obtain ⟨ha', hpriv', hpub', hgr', hQ'⟩ := hst₂ st' h'
      exact ⟨ha.trans (ha'.mono hn₁), hpriv'.trans hpriv, hpub'.trans hpub, hgr'.trans hgr, hQ'⟩

/-- `Runs` for `m >>= f` where the first part always succeeds. -/
theorem bind' {α β : Type} {m : CircuitM α} {f : α → CircuitM β} {s : Build} {st : RunState}
    {ok₂ : Prop} {Q₁ : α → Env → Prop} {Q₂ : β → Env → Prop}
    (h₁ : Runs p m s st True Q₁) (hg : Grows (f (m.run s).1))
    (h₂ : ∀ st' : RunState, Agree s.next st.env st'.env → st'.priv = st.priv → st'.pub = st.pub →
      st'.groups = st.groups → Stable (m.run s).2.next st'.env (Q₁ (m.run s).1) →
      Runs p (f (m.run s).1) (m.run s).2 st' ok₂ Q₂) :
    Runs p (m >>= f) s st ok₂ Q₂ :=
  (bind h₁ hg h₂).conseq (by simp) (fun _ _ h => h)

end Runs

/-! ## Building only appends -/

namespace Grows

theorem pure' {α : Type} (a : α) : Grows (Pure.pure a : CircuitM α) := fun s =>
  ⟨Nat.le_refl _, rfl, [], by simp [CircuitM.pure_run]⟩

theorem bind {α β : Type} {m : CircuitM α} {f : α → CircuitM β} (hm : Grows m) (hf : ∀ a, Grows (f a)) :
    Grows (m >>= f) := fun s => by
  rw [CircuitM.bind_run]
  obtain ⟨hn₁, hg₁, T₁, hT₁⟩ := hm s
  obtain ⟨hn₂, hg₂, T₂, hT₂⟩ := hf (m.run s).1 (m.run s).2
  exact ⟨Nat.le_trans hn₁ hn₂, hg₂.trans hg₁, T₁ ++ T₂, by rw [hT₂, hT₁, List.append_assoc]⟩

theorem emit (st : Stmt) : Grows (Damp.emit st) := fun s =>
  ⟨Nat.le_refl _, rfl, [st], Array.toList_push (xs := s.stmts) (x := st)⟩

theorem freshVar : Grows Damp.freshVar := fun s =>
  ⟨Nat.le_succ _, rfl, [], by simp; rfl⟩

theorem currentGuard : Grows Damp.currentGuard := fun s =>
  ⟨Nat.le_refl _, rfl, [], by simp; rfl⟩

theorem buildError (msg : String) : Grows (Damp.buildError msg) := fun s =>
  ⟨Nat.le_refl _, rfl, [], by simp; rfl⟩

/-- Anything that only records errors. -/
theorem of_errors {α : Type} {m : CircuitM α} (h : ∀ s, (m.run s).2 = { s with errors := (m.run s).2.errors }) :
    Grows m := fun s => by
  rw [h s]; exact ⟨Nat.le_refl _, rfl, [], by simp⟩

theorem checkUintBounds (tys : List Ty) : Grows (Damp.checkUintBounds tys) :=
  of_errors (checkUintBounds_run tys)

theorem require (c : Boolean) (msg : String) : Grows (Damp.require c msg) := fun s => by
  rw [require_run]; exact ⟨Nat.le_refl _, rfl, _, Array.toList_push⟩

theorem guarded (e : Expr) : Grows (Damp.guarded e) := fun s => by
  rw [guarded_run]; exact ⟨Nat.le_refl _, rfl, [], by simp⟩

theorem sub {m k : Nat} (a : Uint m) (b : Uint k) : Grows (a.sub b) := fun s => by
  rw [Uint.sub_run]; exact ⟨Nat.le_refl _, rfl, _, Array.toList_push⟩

theorem nameGuard (e : Expr) : Grows (Damp.nameGuard e) := by
  unfold Damp.nameGuard
  split
  · exact pure' _
  · exact pure' _
  · exact bind freshVar fun v => bind (emit _) fun _ => pure' _

theorem underGuard {α : Type} (g : Expr) {body : CircuitM α} (h : Grows body) : Grows (Damp.underGuard g body) :=
  fun s => by
    obtain ⟨hn, hg, T, hT⟩ := h { s with guard := g }
    exact ⟨hn, rfl, T, hT⟩

theorem when_ (c : Boolean) {body : CircuitM Unit} (h : Grows body) : Grows (Damp.when_ c body) :=
  bind currentGuard fun _ => bind (nameGuard _) fun g => underGuard g h

theorem mapM {α β : Type} {f : α → CircuitM β} (hf : ∀ a, Grows (f a)) : ∀ l : List α, Grows (l.mapM f)
  | [] => pure' _
  | a :: l => by
    rw [List.mapM_cons]; exact bind (hf a) fun _ => bind (mapM hf l) fun _ => pure' _

theorem val {α : Type} [Value α] (x : α) (hint : String) : Grows (Damp.val x hint) :=
  bind (mapM (fun _ => bind freshVar fun _ => bind (emit _) fun _ => pure' _) _) fun _ => pure' _

theorem valM {α : Type} [Value α] {m : CircuitM α} (h : Grows m) (hint : String) : Grows (Damp.valM m hint) :=
  bind h fun x => val x hint

theorem castTo {m : Nat} (a : Uint m) (k : Nat) : Grows (a.castTo k) := by
  unfold Uint.castTo
  refine bind (checkUintBounds _) fun _ => ?_
  split
  · exact pure' _
  · exact bind (guarded _) fun _ => bind (by unfold constrainTy; split <;> first | exact emit _ | exact pure' _)
      fun _ => pure' _

theorem toUint (a : Field) (k : Nat) : Grows (a.toUint k) := by
  unfold Field.toUint
  exact bind (checkUintBounds _) fun _ => bind (guarded _) fun _ =>
    bind (by unfold constrainTy; split <;> first | exact emit _ | exact pure' _) fun _ => pure' _

end Grows

/-! ## `cond`, unfolded -/

/-- The problems `cond` reports about the branch results; they only record errors. -/
def condProblems {α : Type} [Value α] (a b : α) : CircuitM Unit :=
  for p in [Value.problem a, Value.problem b] do
    if let some msg := p then buildError msg

/-- `cond` (`if%`): name the two branch guards, build each branch under its guard, select. -/
theorem cond_eq {α : Type} [Value α] (c : Boolean) (t e : CircuitM α) :
    cond c t e = (do
      let outer ← currentGuard
      let gt ← nameGuard (guardAnd outer c.expr)
      let ge ← nameGuard (guardAnd outer c.not.expr)
      let a ← underGuard gt t
      let b ← underGuard ge e
      condProblems a b
      return select c a b) := rfl

theorem condProblems_run {α : Type} [Value α] (a b : α) (s : Build) :
    ((condProblems a b).run s).2 = { s with errors := ((condProblems a b).run s).2.errors } := by
  unfold condProblems
  simp only [List.forIn_cons, List.forIn_nil]
  cases Value.problem a <;> cases Value.problem b <;> rfl

theorem Grows.cond {α : Type} [Value α] (c : Boolean) {t e : CircuitM α} (ht : Grows t) (he : Grows e) :
    Grows (Damp.cond c t e) := by
  rw [cond_eq]
  exact bind currentGuard fun _ => bind (nameGuard _) fun _ => bind (nameGuard _) fun _ =>
    bind (underGuard _ ht) fun _ => bind (underGuard _ he) fun _ =>
      bind (of_errors (condProblems_run _ _)) fun _ => pure' _

end Damp
