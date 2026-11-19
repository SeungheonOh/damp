/-
What the disclosure check (`Circuit.checkDisclosure`, `Damp/IR/Disclosure.lean`)
guarantees: a noninterference property for the public inputs.

Private data, for the check, is a circuit's arguments and its witness results.
`disclose` is declassification: whatever is wrapped in it may become public.
The theorem `groups_noninterference` says: for a circuit that passes the
check, two accepted runs that read the same values from the ledger (the same
`pub` transcript) and in which every `disclose`d expression that the public
inputs could depend on has the same value, produce the same public inputs
(`groups`), however their arguments and private transcripts differ.

"Every `disclose`d expression has the same value" is `Agree`: at each
statement, each `disclose e` inside an expression whose value could reach the
public inputs evaluates to the same value in the two runs, at the point where
the statement evaluates it.

The property is termination-insensitive: it compares two runs that both
succeed. A private value can still decide *whether* a run succeeds (an
`assert` on it), which the check does not look at.
-/
import Damp.IR.Disclosure
import Damp.IR.Semantics

namespace Damp.IR
open Damp.Zkir (Prims Outcome)

namespace Disclosure

/-! ## Taints -/

theorem foldl_union_eq_nil : ∀ (b a : Taint),
    b.foldl (fun acc s => if acc.contains s then acc else acc ++ [s]) a = [] ↔ a = [] ∧ b = []
  | [], a => by simp
  | s :: b, a => by
      rw [List.foldl_cons, foldl_union_eq_nil b]
      constructor
      · rintro ⟨h, -⟩
        split at h
        · rename_i hc; subst h; simp at hc
        · simp at h
      · rintro ⟨-, h⟩; cases h

theorem Taint.union_eq_nil (a b : Taint) : a.union b = [] ↔ a = [] ∧ b = [] :=
  foldl_union_eq_nil b a

/-- The circuit's variables a run's public data does not depend on through
    undisclosed private data, as the check sees them: those with no taint. -/
def _root_.Damp.IR.Low (σ : List (Var × Taint)) (e₁ e₂ : Env) : Prop :=
  ∀ v, (σ.lookup v).getD [] = [] → e₁ v = e₂ v

/-! ## Disclosed values agree -/

mutual
/-- Every `disclose e` in the expression has the same value in the two
    environments. -/
def _root_.Damp.IR.Expr.DA (p : Prims) (e₁ e₂ : Env) : Expr → Prop
  | .disclose e => e.eval p e₁ = e.eval p e₂
  | .var _ | .const _ | .invalid _ => True
  | .add a b | .mul a b | .lt _ a b | .eq a b => a.DA p e₁ e₂ ∧ b.DA p e₁ e₂
  | .neg a | .divmod _ _ a => a.DA p e₁ e₂
  | .select c a b => c.DA p e₁ e₂ ∧ a.DA p e₁ e₂ ∧ b.DA p e₁ e₂
  | .hash xs | .phash _ _ xs => Expr.DAList p e₁ e₂ xs
def _root_.Damp.IR.Expr.DAList (p : Prims) (e₁ e₂ : Env) : List Expr → Prop
  | [] => True
  | x :: xs => x.DA p e₁ e₂ ∧ Expr.DAList p e₁ e₂ xs
end

mutual
/-- An expression with no undisclosed private dependency has the same value in
    two environments that agree on the variables with no taint, when its
    disclosed values agree. -/
theorem Expr.eval_low (p : Prims) {σ : List (Var × Taint)} {e₁ e₂ : Env} (hl : Low σ e₁ e₂) :
    ∀ e : Expr, e.taint σ = [] → e.DA p e₁ e₂ → e.eval p e₁ = e.eval p e₂
  | .var v, ht, _ => by simp only [Expr.taint] at ht; simp [Expr.eval, hl v ht]
  | .const _, _, _ | .invalid _, _, _ => rfl
  | .disclose e, _, hd => by simpa [Expr.eval, Expr.DA] using hd
  | .add a b, ht, hd | .mul a b, ht, hd | .eq a b, ht, hd | .lt _ a b, ht, hd => by
      simp only [Expr.taint, Taint.union_eq_nil] at ht
      simp only [Expr.DA] at hd
      simp only [Expr.eval, Expr.eval_low p hl a ht.1 hd.1, Expr.eval_low p hl b ht.2 hd.2]
  | .neg a, ht, hd | .divmod _ _ a, ht, hd => by
      simp only [Expr.taint] at ht
      simp only [Expr.DA] at hd
      simp only [Expr.eval, Expr.eval_low p hl a ht hd]
  | .select c a b, ht, hd => by
      simp only [Expr.taint, Taint.union_eq_nil] at ht
      simp only [Expr.DA] at hd
      simp only [Expr.eval, Expr.eval_low p hl c ht.1.1 hd.1, Expr.eval_low p hl a ht.1.2 hd.2.1,
        Expr.eval_low p hl b ht.2 hd.2.2]
  | .hash xs, ht, hd | .phash _ _ xs, ht, hd => by
      simp only [Expr.taint] at ht
      simp only [Expr.DA] at hd
      simp only [Expr.eval, Expr.evalList_low p hl xs ht hd]
theorem Expr.evalList_low (p : Prims) {σ : List (Var × Taint)} {e₁ e₂ : Env} (hl : Low σ e₁ e₂) :
    ∀ xs : List Expr, Expr.taintList σ xs = [] → Expr.DAList p e₁ e₂ xs →
      Expr.evalList p e₁ xs = Expr.evalList p e₂ xs
  | [], _, _ => rfl
  | x :: xs, ht, hd => by
      simp only [Expr.taintList, Taint.union_eq_nil] at ht
      simp only [Expr.DAList] at hd
      simp only [Expr.evalList, Expr.eval_low p hl x ht.1 hd.1, Expr.evalList_low p hl xs ht.2 hd.2]
end

theorem taintList_append (σ : List (Var × Taint)) (xs ys : List Expr) :
    Expr.taintList σ (xs ++ ys) = [] ↔ Expr.taintList σ xs = [] ∧ Expr.taintList σ ys = [] := by
  induction xs with
  | nil => simp [Expr.taintList]
  | cons x xs ih =>
      simp only [List.cons_append, Expr.taintList, Taint.union_eq_nil, ih, and_assoc]

theorem DAList_append (p : Prims) (e₁ e₂ : Env) (xs ys : List Expr) :
    Expr.DAList p e₁ e₂ (xs ++ ys) ↔ Expr.DAList p e₁ e₂ xs ∧ Expr.DAList p e₁ e₂ ys := by
  induction xs with
  | nil => simp [Expr.DAList]
  | cons x xs ih => simp only [List.cons_append, Expr.DAList, ih, and_assoc]

/-- The public inputs of ledger instructions whose operands have no undisclosed
    private dependency. -/
theorem ledgerGroups_low (p : Prims) {σ : List (Var × Taint)} {e₁ e₂ : Env} (hl : Low σ e₁ e₂)
    (active : Bool) : ∀ ops : List (Impact.Op Expr),
    Expr.taintList σ (ops.flatMap fun op => op.encode Expr.const) = [] →
    Expr.DAList p e₁ e₂ (ops.flatMap fun op => op.encode Expr.const) →
    ledgerGroups p e₁ active ops = ledgerGroups p e₂ active ops
  | [], _, _ => rfl
  | op :: ops, ht, hd => by
      rw [List.flatMap_cons, taintList_append] at ht
      rw [List.flatMap_cons, DAList_append] at hd
      simp only [ledgerGroups, Expr.evalList_low p hl _ ht.1 hd.1, ledgerGroups_low p hl active ops ht.2 hd.2]

/-! ## Statements -/

/-- What the check records after a statement. -/
def discStep (σ : List (Var × Taint)) : Stmt → List (Var × Taint)
  | .bind v _ e => (v, e.taint σ) :: σ
  | .witness _ name _ outs _ => outs.map (fun x => (x.fst, [Source.witness name])) ++ σ
  | .ledger _ reads _ => reads.map (fun v => (v, [])) ++ σ
  | _ => σ

/-- What the check requires of a statement. -/
def stepOK (σ : List (Var × Taint)) : Stmt → Prop
  | .ledger g _ ops =>
      g.taint σ = [] ∧ Expr.taintList σ (ops.flatMap fun op => op.encode Expr.const) = []
  | _ => True

/-- The check's loop succeeds on these statements. -/
def DiscOK : List (Var × Taint) → List Stmt → Prop
  | _, [] => True
  | σ, st :: rest => stepOK σ st ∧ DiscOK (discStep σ st) rest

theorem forIn_discOK {F : Stmt → List (Var × Taint) → Except String (ForInStep (List (Var × Taint)))}
    (hF : ∀ s σ r, F s σ = .ok r → r = .yield (discStep σ s) ∧ stepOK σ s) :
    ∀ (l : List Stmt) (σ σf : List (Var × Taint)), forIn l σ F = .ok σf → DiscOK σ l
  | [], _, _, _ => trivial
  | s :: l, σ, σf, h => by
      rw [List.forIn_cons] at h
      cases hs : F s σ with
      | error e => simp [hs, bind, Except.bind] at h
      | ok r =>
          obtain ⟨rfl, hok⟩ := hF s σ r hs
          simp only [hs, bind, Except.bind] at h
          exact ⟨hok, forIn_discOK hF l _ σf h⟩

/-- The initial taints: every argument is private. -/
def initTaint (c : Circuit) : List (Var × Taint) :=
  c.inputs.map fun i => (i.var, [Source.argument i.name])

theorem checkDisclosure_ok {c : Circuit} (h : c.checkDisclosure = .ok ()) :
    DiscOK (initTaint c) c.body.toList := by
  unfold Circuit.checkDisclosure at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i σf hf
    rw [← Array.forIn_toList] at hf
    refine forIn_discOK ?_ _ _ σf hf
    intro s σ r hr
    cases s with
    | bind v _ e =>
        simp only [pure, Except.pure, Except.ok.injEq] at hr
        exact ⟨hr.symm, trivial⟩
    | assert => simp only [pure, Except.pure, Except.ok.injEq] at hr; exact ⟨hr.symm, trivial⟩
    | constrain => simp only [pure, Except.pure, Except.ok.injEq] at hr; exact ⟨hr.symm, trivial⟩
    | witness =>
        simp only [pure, Except.pure, Except.ok.injEq] at hr
        exact ⟨hr.symm, trivial⟩
    | ledger g reads ops =>
        simp only at hr
        split at hr
        · rename_i hg
          split at hr
          · rename_i ho
            simp only [pure, Except.pure, Except.ok.injEq] at hr
            exact ⟨hr.symm, List.isEmpty_iff.mp hg, List.isEmpty_iff.mp ho⟩
          · simp [throw, throwThe, MonadExceptOf.throw] at hr
        · simp [throw, throwThe, MonadExceptOf.throw] at hr

/-! ## Runs -/

/-- Every `disclose`d value a statement could make public agrees in the two
    states: for a binding, in its expression; for a ledger statement, in its
    guard, and in its operands as evaluated after the reads. -/
def _root_.Damp.IR.Stmt.DA (p : Prims) (s₁ s₂ : RunState) : Stmt → Prop
  | .bind _ _ e => e.DA p s₁.env s₂.env
  | .ledger g reads ops =>
      g.DA p s₁.env s₂.env ∧
      ∀ (active : Bool) (e₁ e₂ : Env) (q₁ q₂ : List Fr),
        readAll active s₁.env (reads.map fun v => (v, none)) s₁.pub = some (e₁, q₁) →
        readAll active s₂.env (reads.map fun v => (v, none)) s₂.pub = some (e₂, q₂) →
        Expr.DAList p e₁ e₂ (ops.flatMap fun op => op.encode Expr.const)
  | _ => True

/-- The disclosed values agree at every statement of two runs. -/
def _root_.Damp.IR.Agree (p : Prims) : List Stmt → RunState → RunState → Prop
  | [], _, _ => True
  | st :: rest, s₁, s₂ =>
      st.DA p s₁ s₂ ∧ ∀ s₁' s₂', st.exec p s₁ = some s₁' → st.exec p s₂ = some s₂' → Agree p rest s₁' s₂'

theorem lookup_map_append (l : List Var) (t : Taint) (σ : List (Var × Taint)) (w : Var) :
    ((l.map fun v => (v, t)) ++ σ).lookup w = if w ∈ l then some t else σ.lookup w := by
  induction l with
  | nil => simp
  | cons v l ih =>
      simp only [List.map_cons, List.cons_append, List.lookup, List.mem_cons]
      by_cases h : w = v
      · subst h; simp
      · have : (w == v) = false := by simp [h]
        simp [this, ih, h]

theorem lookup_map_append' (outs : List (Var × Option Range)) (t : Taint) (σ : List (Var × Taint)) (w : Var) :
    ((outs.map fun x => (x.fst, t)) ++ σ).lookup w =
      if w ∈ outs.map Prod.fst then some t else σ.lookup w := by
  have := lookup_map_append (outs.map Prod.fst) t σ w
  simpa [List.map_map, Function.comp_def] using this

/-- One step of a read. -/
theorem readAll_cons {active : Bool} {e e' : Env} {v : Var} {r : Option Range}
    {rest : List (Var × Option Range)} {st st' : List Fr}
    (h : readAll active e ((v, r) :: rest) st = some (e', st')) :
    ∃ x st₁, Zkir.readOne active st = some (x, st₁) ∧ readAll active (e.set v x) rest st₁ = some (e', st') := by
  simp only [readAll, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨x, st₁⟩, hr, h⟩ := h
  refine ⟨x, st₁, hr, ?_⟩
  split at h
  · split at h
    · exact h
    · simp at h
  · exact h

/-- Reading leaves every other variable alone. -/
theorem readAll_other : ∀ (outs : List (Var × Option Range)) (active : Bool) (e e' : Env) (st st' : List Fr),
    readAll active e outs st = some (e', st') → ∀ w, w ∉ outs.map Prod.fst → e' w = e w
  | [], _, e, e', st, st', h, w, _ => by simp [readAll] at h; rw [h.1]
  | (v, r) :: rest, active, e, e', st, st', h, w, hw => by
      simp only [List.map_cons, List.mem_cons, not_or] at hw
      obtain ⟨x, st₁, _, h⟩ := readAll_cons h
      rw [readAll_other rest active _ _ _ _ h w hw.2]; simp [Env.set, hw.1]

/-- Two reads of the same stream, with the same guard, read the same values. -/
theorem readAll_same : ∀ (outs : List (Var × Option Range)) (active : Bool) (e₁ e₂ e₁' e₂' : Env)
    (st q₁ q₂ : List Fr),
    readAll active e₁ outs st = some (e₁', q₁) → readAll active e₂ outs st = some (e₂', q₂) →
    q₁ = q₂ ∧ ∀ w, w ∈ outs.map Prod.fst → e₁' w = e₂' w
  | [], _, _, _, _, _, st, q₁, q₂, h₁, h₂ => by
      simp [readAll] at h₁ h₂; exact ⟨h₁.2.symm.trans h₂.2, by simp⟩
  | (v, r) :: rest, active, e₁, e₂, e₁', e₂', st, q₁, q₂, h₁, h₂ => by
      obtain ⟨x, st₁, hr₁, k₁⟩ := readAll_cons h₁
      obtain ⟨x', st₁', hr₂, k₂⟩ := readAll_cons h₂
      rw [hr₁] at hr₂
      cases hr₂
      obtain ⟨hq, hw⟩ := readAll_same rest active _ _ _ _ st₁ q₁ q₂ k₁ k₂
      refine ⟨hq, fun w hm => ?_⟩
      by_cases hr' : w ∈ rest.map Prod.fst
      · exact hw w hr'
      · simp only [List.map_cons, List.mem_cons] at hm
        rcases hm with rfl | hm
        · rw [readAll_other rest active _ _ _ _ k₁ _ hr', readAll_other rest active _ _ _ _ k₂ _ hr']
          simp [Env.set]
        · exact absurd hm hr'

/-- One statement keeps the two runs in step. -/
theorem Stmt.exec_low (p : Prims) {σ : List (Var × Taint)} {s₁ s₂ s₁' s₂' : RunState} (st : Stmt)
    (hok : stepOK σ st) (hl : Low σ s₁.env s₂.env) (hp : s₁.pub = s₂.pub) (hg : s₁.groups = s₂.groups)
    (hd : st.DA p s₁ s₂) (h₁ : st.exec p s₁ = some s₁') (h₂ : st.exec p s₂ = some s₂') :
    Low (discStep σ st) s₁'.env s₂'.env ∧ s₁'.pub = s₂'.pub ∧ s₁'.groups = s₂'.groups := by
  cases st with
  | bind v _ e =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h₁ h₂
      obtain ⟨x₁, hx₁, rfl⟩ := h₁
      obtain ⟨x₂, hx₂, rfl⟩ := h₂
      refine ⟨fun w hw => ?_, hp, hg⟩
      simp only [discStep, List.lookup] at hw
      simp only [Env.set]
      by_cases hwv : w = v
      · subst hwv
        simp only [beq_self_eq_true, Option.getD_some] at hw
        have := Expr.eval_low p hl e hw hd
        rw [hx₁, hx₂] at this
        simpa using this
      · have : (w == v) = false := by simp [hwv]
        simp only [this] at hw
        simp [hwv, hl w hw]
  | assert c msg =>
      have key : ∀ {s s' : RunState}, (Stmt.assert c msg).exec p s = some s' → s' = s := by
        intro s s' h
        simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨_, _, b, _, h⟩ := h
        split at h
        · simpa [pure] using h.symm
        · cases h
      rw [key h₁, key h₂]; exact ⟨hl, hp, hg⟩
  | constrain e r =>
      have key : ∀ {s s' : RunState}, (Stmt.constrain e r).exec p s = some s' → s' = s := by
        intro s s' h
        simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨_, _, h⟩ := h
        split at h
        · simpa [pure] using h.symm
        · cases h
      rw [key h₁, key h₂]; exact ⟨hl, hp, hg⟩
  | witness g name args outs shape =>
      -- The results are private: they get a taint; nothing else changes.
      have key : ∀ {s s' : RunState}, (Stmt.witness g name args outs shape).exec p s = some s' →
          s'.pub = s.pub ∧ s'.groups = s.groups ∧ ∀ w, w ∉ outs.map Prod.fst → s'.env w = s.env w := by
        intro s s' h
        simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨_, _, h⟩ := h
        split at h
        · simp only [pure, Option.some.injEq] at h; subst h; exact ⟨rfl, rfl, fun _ _ => rfl⟩
        · simp only [Option.bind_eq_some_iff, pure, Option.some.injEq] at h
          obtain ⟨_, _, ⟨env, priv⟩, hr, rfl⟩ := h
          exact ⟨rfl, rfl, fun w hw => readAll_other outs _ _ _ _ _ hr w hw⟩
      obtain ⟨p₁, g₁, o₁⟩ := key h₁
      obtain ⟨p₂, g₂, o₂⟩ := key h₂
      refine ⟨fun w hw => ?_, by rw [p₁, p₂, hp], by rw [g₁, g₂, hg]⟩
      simp only [discStep, lookup_map_append'] at hw
      split at hw
      · simp at hw
      · rename_i hm
        rw [o₁ w hm, o₂ w hm]; exact hl w hw
  | ledger g reads ops =>
      obtain ⟨hgt, hot⟩ := hok
      obtain ⟨hgd, hod⟩ := hd
      have hge := Expr.eval_low p hl g hgt hgd
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h₁ h₂
      obtain ⟨x, hx₁, h₁⟩ := h₁
      obtain ⟨x', hx₂, h₂⟩ := h₂
      rw [← hge, hx₁] at hx₂
      cases hx₂
      by_cases hemp : (reads.isEmpty && ops.isEmpty) = true
      · simp only [hemp, ite_true, Option.pure_def, Option.some.injEq] at h₁ h₂
        subst h₁ h₂
        have hr : reads = [] := by simp_all
        subst hr
        exact ⟨by simpa [discStep] using hl, hp, hg⟩
      · simp only [hemp, Bool.false_eq_true, ite_false, Option.bind_eq_some_iff, Option.pure_def,
          Option.some.injEq] at h₁ h₂
        obtain ⟨active, ha, ⟨e₁, q₁⟩, hr₁, gs, hgs, rfl⟩ := h₁
        obtain ⟨active', ha', ⟨e₂, q₂⟩, hr₂, gs', hgs₂, rfl⟩ := h₂
        rw [ha] at ha'
        cases ha'
        have hr₁' := hr₁
        rw [hp] at hr₁'
        obtain ⟨hq, hsame⟩ := readAll_same _ active _ _ _ _ _ _ _ hr₁' hr₂
        have hmap : (reads.map fun v => ((v, none) : Var × Option Range)).map Prod.fst = reads := by
          simp [List.map_map, Function.comp_def]
        rw [hmap] at hsame
        have o₁ := readAll_other _ _ _ _ _ _ hr₁
        have o₂ := readAll_other _ _ _ _ _ _ hr₂
        rw [hmap] at o₁ o₂
        -- After the reads, the two environments still agree on what has no taint.
        have hl' : Low σ e₁ e₂ := by
          intro w hw
          by_cases hm : w ∈ reads
          · exact hsame w hm
          · rw [o₁ w hm, o₂ w hm]; exact hl w hw
        have hge' := ledgerGroups_low p hl' active ops hot (hod active e₁ e₂ q₁ q₂ hr₁ hr₂)
        rw [hge', hgs₂] at hgs
        cases hgs
        refine ⟨fun w hw => ?_, hq, by simp [hg]⟩
        simp only [discStep, lookup_map_append] at hw
        by_cases hm : w ∈ reads
        · exact hsame w hm
        · simp only [hm, ite_false] at hw
          show e₁ w = e₂ w
          rw [o₁ w hm, o₂ w hm]; exact hl w hw

theorem execAll_low (p : Prims) : ∀ (stmts : List Stmt) (σ : List (Var × Taint)) (s₁ s₂ s₁' s₂' : RunState),
    DiscOK σ stmts → Low σ s₁.env s₂.env → s₁.pub = s₂.pub → s₁.groups = s₂.groups →
    Agree p stmts s₁ s₂ → execAll p stmts s₁ = some s₁' → execAll p stmts s₂ = some s₂' →
    s₁'.groups = s₂'.groups
  | [], _, s₁, s₂, s₁', s₂', _, _, _, hg, _, h₁, h₂ => by
      simp [execAll] at h₁ h₂; subst h₁ h₂; exact hg
  | st :: rest, σ, s₁, s₂, s₁', s₂', hok, hl, hp, hg, ha, h₁, h₂ => by
      simp only [execAll, bind, Option.bind] at h₁ h₂
      cases e₁ : st.exec p s₁ with
      | none => simp [e₁] at h₁
      | some t₁ =>
        cases e₂ : st.exec p s₂ with
        | none => simp [e₂] at h₂
        | some t₂ =>
          simp only [e₁, e₂] at h₁ h₂
          obtain ⟨hl', hp', hg'⟩ := Stmt.exec_low p st hok.1 hl hp hg ha.1 e₁ e₂
          exact execAll_low p rest _ t₁ t₂ s₁' s₂' hok.2 hl' hp' hg' (ha.2 t₁ t₂ e₁ e₂) h₁ h₂

theorem bindInputs_other : ∀ (ins : List Input) (xs : List Fr) (e e' : Env),
    bindInputs e ins xs = some e' → ∀ w, w ∉ ins.map Input.var → e' w = e w
  | [], [], e, e', h, w, _ => by simp [bindInputs] at h; rw [h]
  | [], _ :: _, _, _, h, _, _ => by simp [bindInputs] at h
  | _ :: _, [], _, _, h, _, _ => by simp [bindInputs] at h
  | i :: ins, x :: xs, e, e', h, w, hw => by
      simp only [List.map_cons, List.mem_cons, not_or] at hw
      simp only [bindInputs] at h
      rw [bindInputs_other ins xs _ e' h w hw.2]
      simp [Env.set, hw.1]

theorem lookup_initTaint : ∀ (ins : List Input) (w : Var), w ∈ ins.map Input.var →
    ∃ t, (ins.map fun i => (i.var, [Source.argument i.name])).lookup w = some t ∧ t ≠ []
  | [], _, hm => by simp at hm
  | i :: ins, w, hm => by
      simp only [List.map_cons, List.lookup]
      by_cases hwi : w = i.var
      · subst hwi; simp
      · have : (w == i.var) = false := by simp [hwi]
        simp only [this]
        simp only [List.map_cons, List.mem_cons] at hm
        exact lookup_initTaint ins w (hm.resolve_left hwi)

end Disclosure
open Disclosure

/-- **Noninterference for the public inputs.** For a circuit that passes the
    disclosure check, two accepted runs that read the same values from the
    ledger, and in which every disclosed value the public inputs could depend
    on agrees (`Agree`), produce the same public inputs, whatever their
    arguments and private transcripts. -/
theorem groups_noninterference (p : Prims) (c : Circuit) (hc : c.checkDisclosure = .ok ())
    (in₁ in₂ priv₁ priv₂ pub : List Fr) (o₁ o₂ : Outcome)
    (h₁ : c.run p in₁ priv₁ pub = some o₁) (h₂ : c.run p in₂ priv₂ pub = some o₂)
    (hagree : ∀ env₁ env₂, bindInputs (fun _ => 0) c.inputs in₁ = some env₁ →
      bindInputs (fun _ => 0) c.inputs in₂ = some env₂ →
      Agree p c.body.toList { env := env₁, priv := priv₁, pub } { env := env₂, priv := priv₂, pub }) :
    o₁.groups = o₂.groups := by
  simp only [Circuit.run, bind, Option.bind] at h₁ h₂
  cases hb₁ : bindInputs (fun _ => 0) c.inputs in₁ with
  | none => simp [hb₁] at h₁
  | some env₁ =>
  cases hb₂ : bindInputs (fun _ => 0) c.inputs in₂ with
  | none => simp [hb₂] at h₂
  | some env₂ =>
  simp only [hb₁, hb₂] at h₁ h₂
  cases hx₁ : execAll p c.body.toList { env := env₁, priv := priv₁, pub } with
  | none => simp [hx₁] at h₁
  | some s₁ =>
  cases hx₂ : execAll p c.body.toList { env := env₂, priv := priv₂, pub } with
  | none => simp [hx₂] at h₂
  | some s₂ =>
  simp only [hx₁, hx₂] at h₁ h₂
  have hg₁ : o₁.groups = s₁.groups := by
    split at h₁
    · cases h₁
    · split at h₁
      · simp [pure] at h₁; rw [← h₁]
      · cases h₁
  have hg₂ : o₂.groups = s₂.groups := by
    split at h₂
    · cases h₂
    · split at h₂
      · simp [pure] at h₂; rw [← h₂]
      · cases h₂
  rw [hg₁, hg₂]
  have hl : Low (initTaint c) env₁ env₂ := by
    intro w hw
    have hm : w ∉ c.inputs.map Input.var := by
      intro hm
      obtain ⟨t, ht, hne⟩ := lookup_initTaint c.inputs w hm
      simp only [initTaint, ht, Option.getD_some] at hw
      exact hne hw
    rw [bindInputs_other _ _ _ _ hb₁ w hm, bindInputs_other _ _ _ _ hb₂ w hm]
  exact execAll_low p _ _ { env := env₁, priv := priv₁, pub } { env := env₂, priv := priv₂, pub } s₁ s₂
    (checkDisclosure_ok hc) hl rfl rfl (hagree env₁ env₂ hb₁ hb₂) hx₁ hx₂

/-! ## Without `disclose` -/

namespace Disclosure

mutual
/-- Whether an expression contains a `disclose`. -/
def _root_.Damp.IR.Expr.hasDisclose : Expr → Bool
  | .disclose _ => true
  | .var _ | .const _ | .invalid _ => false
  | .add a b | .mul a b | .lt _ a b | .eq a b => a.hasDisclose || b.hasDisclose
  | .neg a | .divmod _ _ a => a.hasDisclose
  | .select c a b => c.hasDisclose || a.hasDisclose || b.hasDisclose
  | .hash xs | .phash _ _ xs => Expr.hasDiscloseList xs
def _root_.Damp.IR.Expr.hasDiscloseList : List Expr → Bool
  | [] => false
  | x :: xs => x.hasDisclose || Expr.hasDiscloseList xs
end

mutual
theorem Expr.DA_of_not_hasDisclose (p : Prims) (e₁ e₂ : Env) :
    ∀ e : Expr, e.hasDisclose = false → e.DA p e₁ e₂
  | .disclose _, h => by simp [Expr.hasDisclose] at h
  | .var _, _ | .const _, _ | .invalid _, _ => trivial
  | .add a b, h | .mul a b, h | .lt _ a b, h | .eq a b, h => by
      simp only [Expr.hasDisclose, Bool.or_eq_false_iff] at h
      exact ⟨Expr.DA_of_not_hasDisclose p e₁ e₂ a h.1, Expr.DA_of_not_hasDisclose p e₁ e₂ b h.2⟩
  | .neg a, h | .divmod _ _ a, h => by
      simp only [Expr.hasDisclose] at h
      exact Expr.DA_of_not_hasDisclose p e₁ e₂ a h
  | .select c a b, h => by
      simp only [Expr.hasDisclose, Bool.or_eq_false_iff] at h
      exact ⟨Expr.DA_of_not_hasDisclose p e₁ e₂ c h.1.1, Expr.DA_of_not_hasDisclose p e₁ e₂ a h.1.2,
        Expr.DA_of_not_hasDisclose p e₁ e₂ b h.2⟩
  | .hash xs, h | .phash _ _ xs, h => by
      simp only [Expr.hasDisclose] at h
      exact Expr.DAList_of_not_hasDisclose p e₁ e₂ xs h
theorem Expr.DAList_of_not_hasDisclose (p : Prims) (e₁ e₂ : Env) :
    ∀ xs : List Expr, Expr.hasDiscloseList xs = false → Expr.DAList p e₁ e₂ xs
  | [], _ => trivial
  | x :: xs, h => by
      simp only [Expr.hasDiscloseList, Bool.or_eq_false_iff] at h
      exact ⟨Expr.DA_of_not_hasDisclose p e₁ e₂ x h.1, Expr.DAList_of_not_hasDisclose p e₁ e₂ xs h.2⟩
end

/-- A statement whose bound expression, guard and operands contain no `disclose`. -/
def _root_.Damp.IR.Stmt.noDisclose : Stmt → Prop
  | .bind _ _ e => e.hasDisclose = false
  | .ledger g _ ops =>
      g.hasDisclose = false ∧ Expr.hasDiscloseList (ops.flatMap fun op => op.encode Expr.const) = false
  | _ => True

theorem agree_of_noDisclose (p : Prims) : ∀ (stmts : List Stmt), (∀ st ∈ stmts, st.noDisclose) →
    ∀ s₁ s₂, Agree p stmts s₁ s₂
  | [], _, _, _ => trivial
  | st :: rest, h, s₁, s₂ => by
      refine ⟨?_, fun s₁' s₂' _ _ => agree_of_noDisclose p rest (fun x hx => h x (by simp [hx])) s₁' s₂'⟩
      have hst := h st (by simp)
      cases st with
      | bind _ _ e => exact Expr.DA_of_not_hasDisclose p _ _ e hst
      | ledger g reads ops =>
          exact ⟨Expr.DA_of_not_hasDisclose p _ _ g hst.1,
            fun _ _ _ _ _ _ _ => Expr.DAList_of_not_hasDisclose p _ _ _ hst.2⟩
      | _ => trivial

end Disclosure

/-- **Without `disclose`, the public inputs depend on no private data.** For a
    circuit that passes the disclosure check and discloses nothing where it
    could reach the public inputs, two accepted runs that read the same values
    from the ledger produce the same public inputs, whatever their arguments
    and private transcripts. -/
theorem groups_noninterference_noDisclose (p : Prims) (c : Circuit) (hc : c.checkDisclosure = .ok ())
    (hnd : ∀ st ∈ c.body.toList, st.noDisclose)
    (in₁ in₂ priv₁ priv₂ pub : List Fr) (o₁ o₂ : Outcome)
    (h₁ : c.run p in₁ priv₁ pub = some o₁) (h₂ : c.run p in₂ priv₂ pub = some o₂) :
    o₁.groups = o₂.groups :=
  groups_noninterference p c hc in₁ in₂ priv₁ priv₂ pub o₁ o₂ h₁ h₂
    (fun _ _ _ _ => agree_of_noDisclose p _ hnd _ _)

end Damp.IR
