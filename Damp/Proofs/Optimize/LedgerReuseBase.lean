/-
Executor lemmas for the ledger-level passes (`LedgerReuse.lean`): what a step
does to the environment, that the public transcript does not influence a run,
and what the executor sends for a plain read or a cell write.
-/
import Damp.Proofs.Optimize.LedgerSound
import Damp.Proofs.Ledger.OptVm
import Damp.Optimize.LedgerReuse

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Damp.IR
open Damp.Impact Damp.Exec Damp.Ledger
open Damp.Zkir (Prims Group)

/-! ## Evaluating lists -/

theorem evalList_isSome_iff (p : Prims) (env : Env) :
    ∀ xs : List Expr, (Expr.evalList p env xs).isSome ↔ ∀ x ∈ xs, (x.eval p env).isSome
  | [] => by simp [Expr.evalList]
  | x :: xs => by
      have ih := evalList_isSome_iff p env xs
      cases hx : x.eval p env <;> cases hxs : Expr.evalList p env xs <;>
        simp_all [Expr.evalList]

theorem evalList_length {p : Prims} {env : Env} :
    ∀ {xs : List Expr} {ys : List Fr}, Expr.evalList p env xs = some ys → ys.length = xs.length
  | [], ys, h => by simp [Expr.evalList] at h; subst h; rfl
  | x :: xs, ys, h => by
      simp only [Expr.evalList] at h
      cases hx : x.eval p env <;> cases hxs : Expr.evalList p env xs <;> simp_all
      subst h; simp [evalList_length hxs]

theorem evalList_vars (p : Prims) (env : Env) :
    ∀ vs : List Var, Expr.evalList p env (vs.map Expr.var) = some (vs.map env)
  | [] => rfl
  | v :: vs => by simp [Expr.evalList, Expr.eval, evalList_vars p env vs]

theorem evalList_congr_of {p : Prims} {e₁ e₂ : Env} {xs : List Expr}
    (h : ∀ w ∈ Expr.varsList xs, e₁ w = e₂ w) : Expr.evalList p e₁ xs = Expr.evalList p e₂ xs :=
  Expr.evalList_congr_vars p xs h

theorem eval_congr_of {p : Prims} {e₁ e₂ : Env} {e : Expr}
    (h : ∀ w ∈ e.vars, e₁ w = e₂ w) : e.eval p e₁ = e.eval p e₂ :=
  Expr.eval_congr_vars p e h

theorem mem_varsList {x : Expr} {xs : List Expr} (hx : x ∈ xs) {w : Var} (hw : w ∈ x.vars) :
    w ∈ Expr.varsList xs := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [Expr.varsList, List.mem_append]
    rcases List.mem_cons.mp hx with rfl | h
    · exact Or.inl hw
    · exact Or.inr (ih h)

/-! ## Assigning variables -/

theorem assign_frame : ∀ {env env' : Env} {outs : List (Var × Option Range)} {xs : List Fr},
    Exec.assign env outs xs = some env' → ∀ w, w ∉ outs.map Prod.fst → env' w = env w
  | env, env', [], xs, h, w, _ => by
      cases xs <;> simp [Exec.assign] at h; subst h; rfl
  | env, env', (v, r) :: rest, xs, h, w, hw => by
      cases xs with
      | nil => simp [Exec.assign] at h
      | cons x xs =>
        simp only [List.map_cons, List.mem_cons, not_or] at hw
        have step : Exec.assign (env.set v x) rest xs = some env' := by
          cases r with
          | none => simpa [Exec.assign] using h
          | some r =>
            simp only [Exec.assign] at h
            split at h
            · exact h
            · simp at h
        rw [assign_frame step w hw.2]
        simp [Env.set, hw.1]

/-- Plain variables, no ranges: assigning succeeds exactly when the counts match. -/
theorem assign_plain : ∀ (env : Env) (rs : List Var) (xs : List Fr), xs.length = rs.length →
    ∃ env', Exec.assign env (rs.map fun v => (v, none)) xs = some env'
  | env, [], [], _ => ⟨env, rfl⟩
  | env, r :: rs, x :: xs, h => by
      obtain ⟨env', h'⟩ := assign_plain (env.set r x) rs xs (by simpa using h)
      exact ⟨env', by simpa [Exec.assign] using h'⟩
  | _, [], _ :: _, h => by simp at h
  | _, _ :: _, [], h => by simp at h

/-- After assigning distinct variables, they hold the values. -/
theorem assign_reads : ∀ {env env' : Env} {rs : List Var} {xs : List Fr}, rs.Nodup →
    Exec.assign env (rs.map fun v => (v, none)) xs = some env' → rs.map env' = xs
  | env, env', [], xs, _, h => by cases xs <;> simp [Exec.assign] at h ⊢
  | env, env', r :: rs, xs, hnd, h => by
      cases xs with
      | nil => simp [Exec.assign] at h
      | cons x xs =>
        simp only [List.map_cons, Exec.assign] at h
        have hnd' := List.nodup_cons.mp hnd
        have e1 := assign_frame h r (by simpa using hnd'.1)
        simp only [List.map_cons, assign_reads hnd'.2 h, e1, Env.set]
        simp

/-- Zeros, length of the list. -/
theorem map_zero_length {α : Type} (l : List α) : (l.map fun _ => (0 : Fr)).length = l.length := by simp

/-! ## The public transcript does not influence a step -/

variable {ω σ : Type}

/-- What `Pass.SoundLedger` compares of an executor state. -/
def _root_.Damp.Exec.State.obs (s : Exec.State ω σ) : Env × List Fr × ω × σ := (s.env, s.priv, s.private_, s.ledger)

/-- The state with the public transcript and public inputs emptied. -/
def _root_.Damp.Exec.State.norm (s : Exec.State ω σ) : Exec.State ω σ := { s with pub := [], groups := [] }

theorem norm_eq_of_obs {s t : Exec.State ω σ} (h : s.obs = t.obs) : s.norm = t.norm := by
  cases s; cases t
  simp only [Exec.State.obs, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  subst h1 h2 h3 h4; rfl

theorem step_norm (p : Prims) (O : Exec.Oracles ω σ) (s : Exec.State ω σ) (st : Stmt) :
    Exec.step p O s st =
      (Exec.step p O s.norm st).map fun r => { r with pub := s.pub ++ r.pub, groups := s.groups ++ r.groups } := by
  obtain ⟨env, priv, pub, groups, private_, ledger⟩ := s
  cases st with
  | bind v _ e =>
    simp only [Exec.step, Exec.State.norm]
    cases e.eval p env <;> simp
  | assert c _ =>
    simp only [Exec.step, Exec.State.norm]
    cases hc : c.eval p env with
    | none => simp
    | some x =>
      cases hb : asBool x with
      | none => simp [hb]
      | some b => cases b <;> simp [hb]
  | constrain e r =>
    simp only [Exec.step, Exec.State.norm]
    cases he : e.eval p env with
    | none => simp
    | some x => by_cases hr : r.holds x <;> simp [hr]
  | witness g name args outs sh =>
    simp only [Exec.step, Exec.State.norm]
    cases hg : g.eval p env with
    | none => simp
    | some gv =>
      simp only [Option.bind_some, Option.bind_eq_bind]
      by_cases ho : outs.isEmpty
      · simp only [ho, if_true]
        by_cases h1 : gv = 1
        · simp only [h1, if_true]
          cases ha : Expr.evalList p env args with
          | none => simp
          | some xs =>
            cases hw : O.witness name xs private_ with
            | none => simp [hw]
            | some res => by_cases he : res.1.isEmpty <;> simp [hw, he]
        · simp [h1]
      · simp only [ho]
        cases hb : asBool gv with
        | none => simp
        | some b =>
          cases b
          · simp
            cases Exec.assign env outs (outs.map fun _ => 0) <;> simp
          · simp
            cases ha : Expr.evalList p env args with
            | none => simp
            | some xs =>
              cases hw : O.witness name xs private_ with
              | none => simp [hw]
              | some res => simp [hw]; cases Exec.assign env outs res.1 <;> simp
  | ledger g rs ops =>
    simp only [Exec.step, Exec.State.norm]
    cases hg : g.eval p env with
    | none => simp
    | some gv =>
      simp only [Option.bind_some, Option.bind_eq_bind]
      by_cases he : (rs.isEmpty && ops.isEmpty) = true
      · simp only [he, if_true]; simp
      · simp only [he]
        cases hb : asBool gv with
        | none => simp
        | some b =>
          cases b
          · simp
            cases Exec.assign env (rs.map fun v => (v, none)) (rs.map fun _ => 0) <;> simp
            rename_i env'
            cases ledgerGroups p env' false ops <;> simp
          · simp
            cases Exec.request p env ops <;> simp
            rename_i req
            cases O.ledger req ledger <;> simp
            rename_i res
            cases Exec.assign env (rs.map fun v => (v, none)) res.1 <;> simp
            rename_i env'
            cases ledgerGroups p env' true ops <;> simp

theorem step_obs (p : Prims) (O : Exec.Oracles ω σ) {s t : Exec.State ω σ} (h : s.obs = t.obs) (st : Stmt) :
    (Exec.step p O s st).map Exec.State.obs = (Exec.step p O t st).map Exec.State.obs := by
  rw [step_norm p O s, step_norm p O t, norm_eq_of_obs h]
  cases Exec.step p O t.norm st <;> rfl

theorem steps_obs (p : Prims) (O : Exec.Oracles ω σ) :
    ∀ (l : List Stmt) {s t : Exec.State ω σ}, s.obs = t.obs →
      (Exec.steps p O l s).map Exec.State.obs = (Exec.steps p O l t).map Exec.State.obs
  | [], s, t, h => by simp [Exec.steps, h]
  | st :: l, s, t, h => by
      have e := step_obs p O h st
      simp only [Exec.steps]
      cases h1 : Exec.step p O s st <;> cases h2 : Exec.step p O t st <;> rw [h1, h2] at e <;> simp at e ⊢
      exact steps_obs p O l e

/-! ## What a step does -/

/-- A step changes the environment only at the variables it binds. -/
def Stmt.lrBinds : Stmt → List Var
  | .bind v _ _ => [v]
  | .witness _ _ _ outs _ => outs.map Prod.fst
  | .ledger _ rs _ => rs
  | _ => []

theorem step_frame (p : Prims) (O : Exec.Oracles ω σ) {s r : Exec.State ω σ} {st : Stmt}
    (h : Exec.step p O s st = some r) :
    (∀ w, w ∉ st.lrBinds → r.env w = s.env w) ∧ ((∀ g rs ops, st ≠ .ledger g rs ops) → r.ledger = s.ledger) ∧
      r.priv.length ≥ 0 := by
  obtain ⟨env, priv, pub, groups, private_, ledger⟩ := s
  refine ⟨?_, ?_, Nat.zero_le _⟩
  all_goals
  cases st with
  | bind v _ e =>
    simp only [Exec.step] at h
    cases he : e.eval p env with
    | none => simp [he] at h
    | some x =>
      simp [he] at h; subst h
      first
      | (intro w hw; simp [Env.set]; intro hh; exact absurd (by simp [Stmt.lrBinds, hh]) hw)
      | (intro _; rfl)
  | assert c _ =>
    simp only [Exec.step] at h
    cases hc : c.eval p env with
    | none => simp [hc] at h
    | some x =>
      cases hb : asBool x with
      | none => simp [hc, hb] at h
      | some b =>
        cases b <;> simp [hc, hb] at h
        subst h
        first | (intro w _; rfl) | (intro _; rfl)
  | constrain e rr =>
    simp only [Exec.step] at h
    cases he : e.eval p env with
    | none => simp [he] at h
    | some x =>
      by_cases hr : rr.holds x <;> simp [he, hr] at h
      subst h
      first | (intro w _; rfl) | (intro _; rfl)
  | witness g name args outs sh =>
    simp only [Exec.step] at h
    cases hg : g.eval p env with
    | none => simp [hg] at h
    | some gv =>
      simp only [hg, Option.bind_some, Option.bind_eq_bind] at h
      by_cases ho : outs.isEmpty
      · simp only [ho, if_true] at h
        by_cases h1 : gv = 1
        · simp only [h1, if_true] at h
          cases ha : Expr.evalList p env args with
          | none => simp [ha] at h
          | some xs =>
            cases hw : O.witness name xs private_ with
            | none => simp [ha, hw] at h
            | some res =>
              by_cases he : res.1 = [] <;> simp [ha, hw, he] at h
              subst h
              first | (intro w _; rfl) | (intro _; rfl)
        · simp [h1] at h; subst h
          first | (intro w _; rfl) | (intro _; rfl)
      · simp only [ho] at h
        cases hb : asBool gv with
        | none => simp [hb] at h
        | some b =>
          cases b
          · simp [hb] at h
            cases ha : Exec.assign env outs (outs.map fun _ => 0) with
            | none => simp [ha] at h
            | some env' =>
              simp [ha] at h; subst h
              first | (intro w hw; exact assign_frame ha w (by simpa [Stmt.lrBinds] using hw)) | (intro _; rfl)
          · simp [hb] at h
            cases ha : Expr.evalList p env args with
            | none => simp [ha] at h
            | some xs =>
              cases hw : O.witness name xs private_ with
              | none => simp [ha, hw] at h
              | some res =>
                cases hs : Exec.assign env outs res.1 with
                | none => simp [ha, hw, hs] at h
                | some env' =>
                  simp [ha, hw, hs] at h; subst h
                  first | (intro w hw; exact assign_frame hs w (by simpa [Stmt.lrBinds] using hw)) | (intro _; rfl)
  | ledger g rs ops =>
    first
    | (intro hne; exact absurd rfl (hne g rs ops))
    | (intro w hw
       have hw' : w ∉ (rs.map fun v => (v, (none : Option Range))).map Prod.fst := by
         simpa [Stmt.lrBinds] using hw
       simp only [Exec.step] at h
       cases hg : g.eval p env with
       | none => simp [hg] at h
       | some gv =>
         simp only [hg, Option.bind_some, Option.bind_eq_bind] at h
         by_cases he : (rs.isEmpty && ops.isEmpty) = true
         · simp [he] at h; subst h; rfl
         · simp only [he] at h
           cases hb : asBool gv with
           | none => simp [hb] at h
           | some b =>
             cases b
             · simp [hb] at h
               cases ha : Exec.assign env (rs.map fun v => (v, none)) (rs.map fun _ => 0) with
               | none => simp [ha] at h
               | some env' =>
                 cases hl : ledgerGroups p env' false ops with
                 | none => simp [ha, hl] at h
                 | some gs => simp [ha, hl] at h; subst h; exact assign_frame ha w hw'
             · simp [hb] at h
               cases hq : Exec.request p env ops with
               | none => simp [hq] at h
               | some req =>
                 cases ho : O.ledger req ledger with
                 | none => simp [hq, ho] at h
                 | some res =>
                   cases ha : Exec.assign env (rs.map fun v => (v, none)) res.1 with
                   | none => simp [hq, ho, ha] at h
                   | some env' =>
                     cases hl : ledgerGroups p env' true ops with
                     | none => simp [hq, ho, ha, hl] at h
                     | some gs => simp [hq, ho, ha, hl] at h; subst h; exact assign_frame ha w hw')

theorem step_env_frame (p : Prims) (O : Exec.Oracles ω σ) {s r : Exec.State ω σ} {st : Stmt}
    (h : Exec.step p O s st = some r) : ∀ w, w ∉ st.lrBinds → r.env w = s.env w := (step_frame p O h).1

/-- Only a ledger statement changes the ledger state; a witness call (a call
    of another contract included) changes the private state only. -/
theorem step_ledger_same (p : Prims) (O : Exec.Oracles ω σ) {s r : Exec.State ω σ} {st : Stmt}
    (h : Exec.step p O s st = some r) (hst : ∀ g rs ops, st ≠ .ledger g rs ops) : r.ledger = s.ledger :=
  (step_frame p O h).2.1 hst

/-- What a ledger statement's step is, spelled out. -/
theorem step_ledger_cases (p : Prims) (O : Exec.Oracles ω σ) {s r : Exec.State ω σ} {g : Expr} {rs : List Var}
    {ops : List (Op Expr)} (h : Exec.step p O s (.ledger g rs ops) = some r) :
    (rs.isEmpty && ops.isEmpty) = true ∧ r = s ∨
    ∃ gv, g.eval p s.env = some gv ∧
      ((asBool gv = some false ∧ r.ledger = s.ledger ∧
          Exec.assign s.env (rs.map fun v => (v, none)) (rs.map fun _ => 0) = some r.env ∧
          (ledgerGroups p r.env false ops).isSome) ∨
       (asBool gv = some true ∧ ∃ req xs, Exec.request p s.env ops = some req ∧
          O.ledger req s.ledger = some (xs, r.ledger) ∧
          Exec.assign s.env (rs.map fun v => (v, none)) xs = some r.env ∧
          (ledgerGroups p r.env true ops).isSome)) := by
  simp only [Exec.step] at h
  cases hg : g.eval p s.env <;> simp [hg] at h
  rename_i gv
  split at h
  · left; simp at h; exact ⟨by simp_all, h.symm⟩
  · right
    refine ⟨gv, rfl, ?_⟩
    cases hb : asBool gv <;> simp [hb] at h
    rename_i b
    cases b
    · left
      simp at h
      cases ha : Exec.assign s.env (rs.map fun v => (v, none)) (rs.map fun _ => 0) <;> simp [ha] at h
      rename_i env'
      cases hl : ledgerGroups p env' false ops <;> simp [hl] at h
      subst h; simp [hl]
    · right
      simp at h
      cases hq : Exec.request p s.env ops <;> simp [hq] at h
      rename_i req
      cases ho : O.ledger req s.ledger <;> simp [ho] at h
      rename_i res
      cases ha : Exec.assign s.env (rs.map fun v => (v, none)) res.1 <;> simp [ha] at h
      rename_i env'
      cases hl : ledgerGroups p env' true ops <;> simp [hl] at h
      subst h
      exact ⟨rfl, req, res.1, rfl, by simp [ho], ha, by simp [hl]⟩

/-! ## What is sent for a plain read and a cell write -/

theorem aligned_mapM_vals {α β : Type} (f : α → Option β) (k : Aligned α) (k' : Aligned β)
    (h : k.mapM f = some k') : k'.align = k.align ∧ k.vals.mapM f = some k'.vals := by
  unfold Aligned.mapM at h
  cases hv : k.vals.mapM f <;> simp [hv] at h
  subst h; simp

theorem request_plain (p : Prims) (env : Env) (n : Nat) (path : List (Aligned Expr)) (ci c : Bool)
    (a : List Zkir.AlignAtom) (rs : List Var) :
    Exec.request p env [.dup n, .idx ci false path, .popeq c a (rs.map Expr.var)] =
      (path.mapM (fun k : Aligned Expr => k.mapM (Expr.eval p env))).map fun path' => readOps n path' ci c a := by
  have hr : (rs.map Expr.var).mapM (Expr.eval p env) = some (rs.map env) := by
    rw [← evalList_eq_mapM]; exact evalList_vars p env rs
  cases hp : path.mapM (fun k : Aligned Expr => k.mapM (Expr.eval p env)) <;>
    simp [Exec.request, Op.mapM, hp, hr, Exec.blank, readOps]

theorem request_write (p : Prims) (env : Env) (k v : Aligned Expr) :
    Exec.request p env [.push false k, .push true v, .ins false 1] =
      (k.mapM (Expr.eval p env)).bind fun k' => (v.mapM (Expr.eval p env)).map fun v' => writeOps k' v' := by
  cases hk : k.mapM (Expr.eval p env) <;> cases hv : v.mapM (Expr.eval p env) <;>
    simp [Exec.request, Op.mapM, hk, hv, Exec.blank, writeOps]

end Damp.IR
