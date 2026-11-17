/-
Dropping unused bindings preserves every accepted run.

The emitter does not compile a `bind` whose variable nothing later reads
(`Emit.pruneDeadBinds`). This file proves that a run the original circuit
accepts is accepted by the pruned circuit with the same outcome.

The converse is false, and deliberately so: an unused binding whose expression
fails (say, a comparison of a value too wide for its stated width) fails the
original circuit under `Circuit.run`, which evaluates every statement, but
places no constraint in the emitted circuit. What a contract means is therefore
the run of the pruned circuit; this theorem says pruning never loses a run.
-/
import Damp.Emit
import Damp.Semantics

set_option linter.unusedSimpArgs false

namespace Damp.Emit
open Damp.IR
open Damp.Zkir (Prims Group Outcome)

/-- Two environments give the same value to every variable in `L`. -/
def Agree (L : List Var) (e₁ e₂ : Env) : Prop := ∀ v, v ∈ L → e₁ v = e₂ v

theorem Agree.mono {L L' : List Var} {e₁ e₂ : Env} (h : Agree L e₁ e₂) (sub : ∀ v, v ∈ L' → v ∈ L) :
    Agree L' e₁ e₂ := fun v hv => h v (sub v hv)

theorem Agree.left {A B : List Var} {e₁ e₂ : Env} (h : Agree (A ++ B) e₁ e₂) : Agree A e₁ e₂ :=
  h.mono fun _ hv => List.mem_append_left _ hv

theorem Agree.right {A B : List Var} {e₁ e₂ : Env} (h : Agree (A ++ B) e₁ e₂) : Agree B e₁ e₂ :=
  h.mono fun _ hv => List.mem_append_right _ hv

/-- Setting the same variable to the same value keeps environments in agreement. -/
theorem Agree.set {L : List Var} {e₁ e₂ : Env} (h : Agree L e₁ e₂) (v : Var) (x : Fr) :
    Agree L (e₁.set v x) (e₂.set v x) := by
  intro w hw
  simp only [Env.set]
  split
  · rfl
  · exact h w hw

/-- Setting a variable outside `L` on one side keeps agreement on `L`. -/
theorem Agree.set_left {L : List Var} {e₁ e₂ : Env} (h : Agree L e₁ e₂) (v : Var) (x : Fr)
    (hv : v ∉ L) : Agree L (e₁.set v x) e₂ := by
  intro w hw
  simp only [Env.set]
  split
  · next heq => exact absurd (heq ▸ hw) hv
  · exact h w hw

/-! ## An expression's value depends only on the variables in it -/

mutual
theorem eval_congr (p : Prims) {e₁ e₂ : Env} :
    ∀ e : Expr, Agree e.vars e₁ e₂ → e.eval p e₁ = e.eval p e₂
  | .var v, h => by simp only [Expr.eval]; rw [h v (by simp [Expr.vars])]
  | .const _, _ => rfl
  | .invalid _, _ => rfl
  | .disclose a, h => by
      simp only [Expr.eval]; exact eval_congr p a (by simpa [Expr.vars] using h)
  | .neg a, h => by
      simp only [Expr.eval]; rw [eval_congr p a (by simpa [Expr.vars] using h)]
  | .divmod _ _ a, h => by
      simp only [Expr.eval]; rw [eval_congr p a (by simpa [Expr.vars] using h)]
  | .add a b, h => by
      have h' : Agree (a.vars ++ b.vars) e₁ e₂ := by simpa [Expr.vars] using h
      simp only [Expr.eval]; rw [eval_congr p a h'.left, eval_congr p b h'.right]
  | .mul a b, h => by
      have h' : Agree (a.vars ++ b.vars) e₁ e₂ := by simpa [Expr.vars] using h
      simp only [Expr.eval]; rw [eval_congr p a h'.left, eval_congr p b h'.right]
  | .eq a b, h => by
      have h' : Agree (a.vars ++ b.vars) e₁ e₂ := by simpa [Expr.vars] using h
      simp only [Expr.eval]; rw [eval_congr p a h'.left, eval_congr p b h'.right]
  | .lt _ a b, h => by
      have h' : Agree (a.vars ++ b.vars) e₁ e₂ := by simpa [Expr.vars] using h
      simp only [Expr.eval]; rw [eval_congr p a h'.left, eval_congr p b h'.right]
  | .select c a b, h => by
      have h' : Agree ((c.vars ++ a.vars) ++ b.vars) e₁ e₂ := by simpa [Expr.vars] using h
      simp only [Expr.eval]
      rw [eval_congr p c h'.left.left, eval_congr p a h'.left.right, eval_congr p b h'.right]
  | .hash xs, h => by
      simp only [Expr.eval]; rw [evalList_congr p xs (by simpa [Expr.vars] using h)]
  | .phash _ _ xs, h => by
      simp only [Expr.eval]; rw [evalList_congr p xs (by simpa [Expr.vars] using h)]
theorem evalList_congr (p : Prims) {e₁ e₂ : Env} :
    ∀ xs : List Expr, Agree (Expr.varsList xs) e₁ e₂ → Expr.evalList p e₁ xs = Expr.evalList p e₂ xs
  | [], _ => rfl
  | x :: xs, h => by
      have h' : Agree (x.vars ++ Expr.varsList xs) e₁ e₂ := by simpa [Expr.varsList] using h
      simp only [Expr.evalList]; rw [eval_congr p x h'.left, evalList_congr p xs h'.right]
end

theorem varsList_eq_flatMap : ∀ xs : List Expr, Expr.varsList xs = xs.flatMap Expr.vars
  | [] => rfl
  | x :: xs => by simp [Expr.varsList, varsList_eq_flatMap xs]

/-! ## Statements -/

/-- Reading into agreeing environments gives agreeing environments and the same stream. -/
theorem readAll_congr {L : List Var} (active : Bool) :
    ∀ (outs : List (Var × Option Range)) (e₁ e₂ : Env) (stream : List Fr) (e₁' : Env) (rest : List Fr),
      Agree L e₁ e₂ → readAll active e₁ outs stream = some (e₁', rest) →
      ∃ e₂', readAll active e₂ outs stream = some (e₂', rest) ∧ Agree L e₁' e₂'
  | [], e₁, e₂, stream, e₁', rest, h, hr => by
      simp only [readAll, Option.some.injEq, Prod.mk.injEq] at hr
      exact ⟨e₂, by simp [readAll, hr.2], hr.1 ▸ h⟩
  | (v, range) :: outs, e₁, e₂, stream, e₁', rest, h, hr => by
      simp only [readAll] at hr ⊢
      cases hread : Zkir.readOne active stream with
      | none => simp [hread] at hr
      | some xs =>
          obtain ⟨x, stream'⟩ := xs
          simp only [hread, Option.bind_eq_bind, Option.bind_some] at hr ⊢
          cases range with
          | none =>
              simp only [Option.pure_def, Option.bind_some] at hr ⊢
              exact readAll_congr active outs _ _ stream' e₁' rest (h.set v x) hr
          | some r =>
              by_cases hh : r.holds x
              · simp only [hh, ite_true, Option.pure_def, Option.bind_some] at hr ⊢
                exact readAll_congr active outs _ _ stream' e₁' rest (h.set v x) hr
              · simp [hh] at hr

/-- The public inputs of a ledger statement depend only on the variables in its operands. -/
theorem ledgerGroups_congr (p : Prims) {e₁ e₂ : Env} (active : Bool) :
    ∀ ops : List (Impact.Op Expr),
      Agree (ops.flatMap fun op => (op.encode Expr.const).flatMap Expr.vars) e₁ e₂ →
      ledgerGroups p e₁ active ops = ledgerGroups p e₂ active ops
  | [], _ => rfl
  | op :: ops, h => by
      have h' : Agree ((op.encode Expr.const).flatMap Expr.vars ++
          ops.flatMap fun op => (op.encode Expr.const).flatMap Expr.vars) e₁ e₂ := by
        simpa using h
      simp only [ledgerGroups]
      rw [evalList_congr p _ (by rw [varsList_eq_flatMap]; exact h'.left),
        ledgerGroups_congr p active ops h'.right]

/-- A statement run in two environments that agree on what it reads and on `L`
    behaves the same and leaves environments that agree on `L`. -/
theorem stmt_congr (p : Prims) {L : List Var} (st : Stmt) (e₁ e₂ : Env) (priv pub : List Fr)
    (groups : List Group) (s₁ : RunState)
    (h : Agree (uses st ++ L) e₁ e₂)
    (hrun : st.exec p { env := e₁, priv, pub, groups } = some s₁) :
    ∃ e₂', st.exec p { env := e₂, priv, pub, groups }
        = some { env := e₂', priv := s₁.priv, pub := s₁.pub, groups := s₁.groups } ∧
      Agree (uses st ++ L) s₁.env e₂' := by
  cases st with
  | bind v hint e =>
      simp only [Stmt.exec] at hrun ⊢
      have he : e.eval p e₁ = e.eval p e₂ := eval_congr p e (by simpa [uses] using h.left)
      rw [← he]
      cases hx : e.eval p e₁ with
      | none => simp [hx] at hrun
      | some x =>
          simp only [hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
            Option.some.injEq] at hrun ⊢
          subst hrun
          exact ⟨e₂.set v x, rfl, h.set v x⟩
  | assert cond msg =>
      simp only [Stmt.exec] at hrun ⊢
      have he : cond.eval p e₁ = cond.eval p e₂ := eval_congr p cond (by simpa [uses] using h.left)
      rw [← he]
      cases hx : cond.eval p e₁ with
      | none => simp [hx] at hrun
      | some x =>
          simp only [hx, Option.bind_eq_bind, Option.bind_some] at hrun ⊢
          cases hb : asBool x with
          | none => simp [hb] at hrun
          | some b =>
              simp only [hb, Option.bind_some] at hrun ⊢
              cases b with
              | false => simp at hrun
              | true =>
                  simp only [ite_true, Option.pure_def, Option.some.injEq] at hrun ⊢
                  subst hrun
                  exact ⟨e₂, rfl, h⟩
  | constrain e r =>
      simp only [Stmt.exec] at hrun ⊢
      have he : e.eval p e₁ = e.eval p e₂ := eval_congr p e (by simpa [uses] using h.left)
      rw [← he]
      cases hx : e.eval p e₁ with
      | none => simp [hx] at hrun
      | some x =>
          simp only [hx, Option.bind_eq_bind, Option.bind_some] at hrun ⊢
          by_cases hh : r.holds x
          · simp only [hh, ite_true, Option.pure_def, Option.some.injEq] at hrun ⊢
            subst hrun
            exact ⟨e₂, rfl, h⟩
          · simp [hh] at hrun
  | witness guard name args outs shape =>
      simp only [Stmt.exec] at hrun ⊢
      have hg : guard.eval p e₁ = guard.eval p e₂ :=
        eval_congr p guard (by
          have := h.left
          simp only [uses] at this
          exact this.left)
      rw [← hg]
      cases hx : guard.eval p e₁ with
      | none => simp [hx] at hrun
      | some g =>
          simp only [hx, Option.bind_eq_bind, Option.bind_some] at hrun ⊢
          by_cases hempty : outs.isEmpty
          · simp only [hempty, ite_true, Option.pure_def, Option.some.injEq] at hrun ⊢
            subst hrun
            exact ⟨e₂, rfl, h⟩
          · simp only [hempty, Bool.false_eq_true, ite_false] at hrun ⊢
            cases hb : asBool g with
            | none => simp [hb] at hrun
            | some active =>
                simp only [hb, Option.bind_some] at hrun ⊢
                cases hr : readAll active e₁ outs priv with
                | none => simp [hr] at hrun
                | some res =>
                    obtain ⟨e₁', priv'⟩ := res
                    simp only [hr, Option.bind_some, Option.pure_def, Option.some.injEq] at hrun
                    subst hrun
                    obtain ⟨e₂', hr₂, hag⟩ := readAll_congr active outs e₁ e₂ priv e₁' priv' h hr
                    exact ⟨e₂', by simp [hr₂], hag⟩
  | ledger guard reads ops =>
      simp only [Stmt.exec] at hrun ⊢
      have huses := h.left
      simp only [uses] at huses
      have hg : guard.eval p e₁ = guard.eval p e₂ := eval_congr p guard huses.left
      rw [← hg]
      cases hx : guard.eval p e₁ with
      | none => simp [hx] at hrun
      | some g =>
          simp only [hx, Option.bind_eq_bind, Option.bind_some] at hrun ⊢
          by_cases hempty : (reads.isEmpty && ops.isEmpty) = true
          · simp only [hempty, ite_true, Option.pure_def, Option.some.injEq] at hrun ⊢
            subst hrun
            exact ⟨e₂, rfl, h⟩
          · simp only [hempty, Bool.false_eq_true, ite_false] at hrun ⊢
            cases hb : asBool g with
            | none => simp [hb] at hrun
            | some active =>
                simp only [hb, Option.bind_some] at hrun ⊢
                cases hr : readAll active e₁ (reads.map fun v => (v, none)) pub with
                | none => simp [hr] at hrun
                | some res =>
                    obtain ⟨e₁', pub'⟩ := res
                    simp only [hr, Option.bind_some] at hrun
                    obtain ⟨e₂', hr₂, hag⟩ :=
                      readAll_congr active (reads.map fun v => (v, none)) e₁ e₂ pub e₁' pub' h hr
                    have hgroups : ledgerGroups p e₁' active ops = ledgerGroups p e₂' active ops := by
                      apply ledgerGroups_congr
                      have := hag.left
                      simp only [uses] at this
                      exact this.right
                    cases hgr : ledgerGroups p e₁' active ops with
                    | none => simp [hgr] at hrun
                    | some gs =>
                        simp only [hgr, Option.bind_some, Option.pure_def, Option.some.injEq] at hrun
                        subst hrun
                        exact ⟨e₂', by simp [hr₂, ← hgroups, hgr], hag⟩

/-! ## Pruning -/

/-- One step of the backward pass: keep a statement unless it is a `bind` of a
    variable that nothing later reads. The second component is what is read from
    here on. -/
def pruneStep (s : Stmt) (acc : List Stmt × List Var) : List Stmt × List Var :=
  match s with
  | .bind v _ _ => if acc.2.contains v then (s :: acc.1, uses s ++ acc.2) else acc
  | _ => (s :: acc.1, uses s ++ acc.2)

/-- The backward pass over a list of statements, given what is read afterwards. -/
def pruneList (ss : List Stmt) (out : List Var) : List Stmt × List Var :=
  ss.foldr pruneStep ([], out)

theorem pruneDeadBinds_eq (c : Circuit) :
    (pruneDeadBinds c).toList = (pruneList c.body.toList (c.outputs.flatMap Expr.vars)).1 := by
  simp only [pruneDeadBinds, pruneList, Array.foldr_toList]
  first
    | rfl
    | (congr 2; funext s acc; cases s <;> rfl)

/-- Running the kept statements from an environment that agrees on everything
    read from here on reaches a state that agrees on everything read afterwards. -/
theorem pruneList_run (p : Prims) (out : List Var) :
    ∀ (ss : List Stmt) (e₁ e₂ : Env) (priv pub : List Fr) (groups : List Group) (s₁ : RunState),
      Agree (pruneList ss out).2 e₁ e₂ →
      execAll p ss { env := e₁, priv, pub, groups } = some s₁ →
      ∃ e₂', execAll p (pruneList ss out).1 { env := e₂, priv, pub, groups }
          = some { env := e₂', priv := s₁.priv, pub := s₁.pub, groups := s₁.groups } ∧
        Agree out s₁.env e₂'
  | [], e₁, e₂, priv, pub, groups, s₁, h, hrun => by
      simp only [execAll, Option.some.injEq] at hrun
      subst hrun
      exact ⟨e₂, rfl, h⟩
  | st :: rest, e₁, e₂, priv, pub, groups, s₁, h, hrun => by
      simp only [execAll] at hrun
      cases hst : st.exec p { env := e₁, priv, pub, groups } with
      | none => simp [hst] at hrun
      | some mid =>
          simp only [hst, Option.bind_eq_bind, Option.bind_some] at hrun
          have hfold : pruneList (st :: rest) out = pruneStep st (pruneList rest out) := rfl
          rw [hfold] at h ⊢
          -- Either the statement is kept, or it is a dead `bind`.
          by_cases hdead : ∃ v hint e, st = .bind v hint e ∧ (pruneList rest out).2.contains v = false
          · obtain ⟨v, hint, e, rfl, hv⟩ := hdead
            simp only [pruneStep, hv, Bool.false_eq_true, ite_false] at h ⊢
            simp only [Stmt.exec] at hst
            cases hx : e.eval p e₁ with
            | none => simp [hx] at hst
            | some x =>
                simp only [hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                  Option.some.injEq] at hst
                subst hst
                have hnot : v ∉ (pruneList rest out).2 := by
                  intro hmem
                  have : (pruneList rest out).2.contains v = true := by simpa using hmem
                  rw [hv] at this
                  exact absurd this (by simp)
                exact pruneList_run p out rest _ e₂ priv pub groups s₁ (h.set_left v x hnot) hrun
          · have hkeep : pruneStep st (pruneList rest out)
                = (st :: (pruneList rest out).1, uses st ++ (pruneList rest out).2) := by
              cases st with
              | bind v hint e =>
                  simp only [pruneStep]
                  split
                  · rfl
                  · next hc =>
                      exact absurd ⟨v, hint, e, rfl, by simpa using hc⟩ hdead
              | _ => rfl
            rw [hkeep] at h ⊢
            obtain ⟨e₂m, hst₂, hag⟩ := stmt_congr p st e₁ e₂ priv pub groups mid h hst
            simp only [execAll, hst₂, Option.bind_eq_bind, Option.bind_some]
            exact pruneList_run p out rest mid.env e₂m mid.priv mid.pub mid.groups s₁ hag.right hrun

/-- **Pruning preserves accepted runs.** If the circuit accepts a run, the
    circuit without its unused bindings accepts it with the same outcome. -/
theorem pruned_run (p : Prims) (c : Circuit) (inputs priv pub : List Fr) (o : Outcome)
    (h : c.run p inputs priv pub = some o) : (pruned c).run p inputs priv pub = some o := by
  simp only [Circuit.run] at h ⊢
  cases henv : bindInputs (fun _ => 0) c.inputs inputs with
  | none => simp [henv] at h
  | some env =>
      have hin : (pruned c).inputs = c.inputs := rfl
      have hout : (pruned c).outputs = c.outputs := rfl
      have hbody : (pruned c).body.toList = (pruneList c.body.toList (c.outputs.flatMap Expr.vars)).1 :=
        pruneDeadBinds_eq c
      simp only [henv, Option.bind_eq_bind, Option.bind_some, hin, hout, hbody] at h ⊢
      cases hrun : execAll p c.body.toList { env, priv, pub } with
      | none => simp [hrun] at h
      | some s₁ =>
          simp only [hrun, Option.bind_some] at h
          obtain ⟨e₂', hrun₂, hag⟩ := pruneList_run p (c.outputs.flatMap Expr.vars) c.body.toList
            env env priv pub [] s₁ (fun _ _ => rfl) hrun
          have hgroups : ({ env, priv, pub } : RunState) = { env, priv, pub, groups := [] } := rfl
          rw [hgroups, hrun₂]
          simp only [Option.bind_some]
          have houts : Expr.evalList p s₁.env c.outputs = Expr.evalList p e₂' c.outputs :=
            evalList_congr p c.outputs (by rw [varsList_eq_flatMap]; exact hag)
          rw [← houts]
          exact h

end Damp.Emit
