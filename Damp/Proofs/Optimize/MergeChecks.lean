/-
Soundness of `Circuit.mergeChecks` (`Damp/Optimize/MergeChecks.lean`).

The argument is made once for any "runner" of statements that, like
`execAll` and the executor's `steps`, (1) changes only the variables a
statement binds, (2) runs a check by leaving the state alone when it passes
and failing otherwise, and (3) runs a binding `v := e` by giving `v` the value
of `e` (`StepOK`). Then:

* `Defs` stay true along a run (`Defs.Valid`, `Defs.valid_after`), so a guard
  the pass reads as the negation of another is one (`Defs.resolve_eval`);
* a merged check passes exactly when both checks it replaces pass, in the same
  environment (`mergePair_ok`);
* a check that no statement before it rebinds a variable of can be evaluated
  at the start instead (`runL_check_later`): the run fails exactly when it
  did, and otherwise is the same.

So the merged body runs exactly as the original (`runL_mergeGo`), for
`Circuit.run` and for the executor: `Circuit.mergeChecks_sound`.
-/
import Damp.Optimize.MergeChecks
import Damp.Proofs.Optimize.HashRanges
import Damp.Proofs.Optimize.AssertEq
import Damp.Proofs.Optimize.Commute

namespace Damp.IR
open Damp.Zkir (Prims)
open Damp.Emit (Agree eval_congr)

/-! ## Checks -/

/-- Whether a check passes in an environment (every other statement "passes"). -/
def checkOk (p : Prims) (env : Env) : Stmt → Bool
  | .assert c _ => decide (c.eval p env = some 1)
  | .constrain e r => match e.eval p env with
    | some x => r.holds x
    | none => false
  | _ => true

theorem checkOk_congr (p : Prims) {env env' : Env} (t : Stmt) (h : Agree t.checkVars env env') :
    checkOk p env t = checkOk p env' t := by
  cases t <;> simp only [checkOk, Stmt.checkVars] at h ⊢
  · rw [eval_congr p _ h]
  · rw [eval_congr p _ h]

theorem constrain_bind (o : Option Fr) (r : Range) {α : Type} (s : α) :
    (do let x ← o; if r.holds x = true then pure s else none) =
      if (match o with | some x => r.holds x | none => false) = true then some s else none := by
  cases o with
  | none => simp
  | some x => by_cases h : r.holds x <;> simp [h]

theorem exec_check (p : Prims) (st : RunState) (t : Stmt) (ht : t.isCheck = true) :
    t.exec p st = if checkOk p st.env t then some st else none := by
  cases t with
  | assert c msg =>
      simp only [Stmt.exec]; rw [assert_bind]
      by_cases h : c.eval p st.env = some 1 <;> simp [checkOk, h]
  | constrain e r =>
      simp only [Stmt.exec]; rw [constrain_bind]; rfl
  | _ => simp [Stmt.isCheck] at ht

theorem step_check {ω σ : Type} (p : Prims) (O : Exec.Oracles ω σ) (st : Exec.State ω σ) (t : Stmt)
    (ht : t.isCheck = true) :
    Exec.step p O st t = if checkOk p st.env t then some st else none := by
  cases t with
  | assert c msg =>
      simp only [Exec.step]; rw [assert_bind]
      by_cases h : c.eval p st.env = some 1 <;> simp [checkOk, h]
  | constrain e r =>
      simp only [Exec.step]; rw [constrain_bind]; rfl
  | _ => simp [Stmt.isCheck] at ht

theorem check_binds {t : Stmt} (ht : t.isCheck = true) : t.binds = [] := by
  cases t <;> simp_all [Stmt.isCheck, Stmt.binds]

/-! ## Runners -/

section Runner
variable {S : Type} (p : Prims) (envOf : S → Env) (step : S → Stmt → Option S)

/-- Run statements in order with `step`. -/
def runL : List Stmt → S → Option S
  | [], s => some s
  | t :: ts, s => (step s t).bind (runL ts)

/-- What the proof needs of a runner. -/
structure StepOK : Prop where
  keeps : ∀ st st' t, step st t = some st' → ∀ u, u ∉ t.binds → envOf st' u = envOf st u
  check : ∀ st t, t.isCheck = true → step st t = if checkOk p (envOf st) t then some st else none
  bind : ∀ st st' v h e, step st (.bind v h e) = some st' → e.eval p (envOf st) = some (envOf st' v)

variable {p envOf step}

theorem runL_append_cons_check (hs : StepOK p envOf step) {t : Stmt} (ht : t.isCheck = true) :
    ∀ (pre post : List Stmt) (st : S), (∀ u ∈ pre, ∀ v ∈ t.checkVars, v ∉ u.binds) →
      runL step (pre ++ t :: post) st =
        if checkOk p (envOf st) t then runL step (pre ++ post) st else none
  | [], post, st, _ => by
      simp only [List.nil_append, runL, hs.check st t ht]
      split <;> simp
  | u :: pre, post, st, hpre => by
      simp only [List.cons_append, runL]
      cases hu : step st u with
      | none => simp
      | some st' =>
          simp only [Option.bind_some]
          rw [runL_append_cons_check hs ht pre post st' (fun u' hu' => hpre u' (by simp [hu']))]
          have hag : Agree t.checkVars (envOf st') (envOf st) := fun v hv =>
            hs.keeps st st' u hu v (hpre u (by simp) v hv)
          rw [checkOk_congr p t hag]

end Runner

/-! ## What is known -/

/-- Every recorded definition holds in `env`. -/
def Defs.Valid (p : Prims) (D : Defs) (env : Env) : Prop := ∀ v e, (v, e) ∈ D → e.eval p env = some (env v)

theorem defs_lookup_mem : ∀ (D : Defs) (v : Var) (e : Expr), D.lookup v = some e → (v, e) ∈ D
  | [], _, _, h => by simp [List.lookup] at h
  | (k, b) :: D, v, e, h => by
      simp only [List.lookup] at h
      by_cases hk : v = k
      · subst hk; simp at h; subst h; simp
      · have : (v == k) = false := by simpa using hk
        rw [this] at h
        exact List.mem_cons_of_mem _ (defs_lookup_mem D v e h)

theorem Defs.resolve_eval {p : Prims} {D : Defs} {env : Env} (hD : D.Valid p env) (e : Expr) :
    (D.resolve e).eval p env = e.eval p env := by
  cases e <;> simp only [Defs.resolve]
  rename_i v
  cases hl : D.lookup v with
  | none => rfl
  | some d => simp only [Option.getD_some, Expr.eval]; exact hD v d (defs_lookup_mem D v d hl)

section Runner
variable {S : Type} {p : Prims} {envOf : S → Env} {step : S → Stmt → Option S}

theorem Defs.valid_after (hs : StepOK p envOf step) {D : Defs} {st st' : S} {t : Stmt}
    (hD : D.Valid p (envOf st)) (h : step st t = some st') : (D.after t).Valid p (envOf st') := by
  have hkeep : ∀ v e, (v, e) ∈ D.filter (fun (v, e) => !t.binds.contains v && e.vars.all fun u => !t.binds.contains u) →
      e.eval p (envOf st') = some (envOf st' v) := by
    intro v e hm
    have hm' := List.mem_filter.mp hm
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hm'
    obtain ⟨hm, hc, he⟩ := hm'
    have hv : v ∉ t.binds := by simpa using hc
    have hag : Agree e.vars (envOf st') (envOf st) := fun u hu =>
      hs.keeps st st' t h u (by simpa using List.all_eq_true.mp he u hu)
    rw [eval_congr p e hag, hD v e hm, hs.keeps st st' t h v hv]
  unfold Defs.after
  split
  · rename_i v hint e
    split
    · exact hkeep
    · rename_i hv
      intro w d hm
      simp only [List.mem_cons] at hm
      rcases hm with hm | hm
      · simp only [Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        have hag : Agree d.vars (envOf st') (envOf st) := fun u hu =>
          hs.keeps st st' _ h u (by simp [Stmt.binds]; intro he; subst he; exact hv (by simpa using hu))
        rw [eval_congr p d hag]
        exact hs.bind st st' w hint d h
      · exact hkeep w d hm
  · exact hkeep

end Runner

/-! ## Merging two checks -/

theorem Range.same_eq : ∀ {r r' : Range}, r.same r' = true → r = r'
  | .zero, .zero, _ | .bool, .bool, _ => rfl
  | .bits n, .bits m, h => by simp [Range.same] at h; rw [h]
  | .below b w, .below b' w', h => by simp [Range.same] at h; rw [h.1, h.2]
  | .zero, .bool, h | .zero, .bits _, h | .zero, .below .., h
  | .bool, .zero, h | .bool, .bits _, h | .bool, .below .., h
  | .bits _, .zero, h | .bits _, .bool, h | .bits _, .below .., h
  | .below .., .zero, h | .below .., .bool, h | .below .., .bits _, h => by simp [Range.same] at h

/-- A conditional on values. -/
def selv (G A B : Option Fr) : Option Fr :=
  G.bind fun g => A.bind fun x => B.bind fun y => (asBool g).bind fun gb => some (if gb then x else y)

/-- The negation of a guard, on values. -/
def notv (G : Option Fr) : Option Fr := selv G (some 0) (some 1)

theorem eval_select (p : Prims) (env : Env) (c a b : Expr) :
    (Expr.select c a b).eval p env = selv (c.eval p env) (a.eval p env) (b.eval p env) := rfl

theorem eval_not (p : Prims) (env : Env) (g : Expr) :
    (Expr.select g (.const 0) (.const 1)).eval p env = notv (g.eval p env) := rfl

theorem asBool_cases (x : Fr) : asBool x = none ∨ (asBool x = some true ∧ x = 1) ∨ (asBool x = some false ∧ x = 0) := by
  by_cases h0 : x = 0
  · subst h0; exact Or.inr (Or.inr ⟨asBool_zero, rfl⟩)
  · by_cases h1 : x = 1
    · subst h1; exact Or.inr (Or.inl ⟨asBool_one, rfl⟩)
    · left; simp [asBool, h0, h1]

theorem selv_assert (G1 G2 C : Option Fr) (hn : G1 = notv G2 ∨ G2 = notv G1) :
    decide (selv G1 C C = some 1) =
      (decide (selv G1 C (some 1) = some 1) && decide (selv G2 C (some 1) = some 1)) := by
  rcases hn with rfl | rfl
  · cases G2 with
    | none => simp [selv, notv]
    | some y =>
        rcases asBool_cases y with h | ⟨h, rfl⟩ | ⟨h, rfl⟩
        · simp [selv, notv, h]
        · cases C <;> simp [selv, notv, asBool_zero, asBool_one]
        · cases C <;> simp [selv, notv, asBool_zero, asBool_one]
  · cases G1 with
    | none => cases C <;> simp [selv, notv]
    | some y =>
        rcases asBool_cases y with h | ⟨h, rfl⟩ | ⟨h, rfl⟩
        · cases C <;> simp [selv, notv, h]
        · cases C <;> simp [selv, notv, asBool_zero, asBool_one]
        · cases C <;> simp [selv, notv, asBool_zero, asBool_one]

/-- Whether a value passes a range check, failure being `false`. -/
def holdsv (r : Range) : Option Fr → Bool
  | some x => r.holds x
  | none => false

theorem selv_constrain (G1 G2 X : Option Fr) (r : Range) (h0 : r.holds 0 = true)
    (hn : G1 = notv G2 ∨ G2 = notv G1) :
    holdsv r (selv G1 X X) = (holdsv r (selv G1 X (some 0)) && holdsv r (selv G2 X (some 0))) := by
  rcases hn with rfl | rfl
  · cases G2 with
    | none => simp [selv, notv, holdsv]
    | some y =>
        rcases asBool_cases y with h | ⟨h, rfl⟩ | ⟨h, rfl⟩
        · simp [selv, notv, h, holdsv]
        · cases X <;> simp [selv, notv, asBool_zero, asBool_one, holdsv, h0]
        · cases X <;> simp [selv, notv, asBool_zero, asBool_one, holdsv, h0]
  · cases G1 with
    | none => cases X <;> simp [selv, notv, holdsv]
    | some y =>
        rcases asBool_cases y with h | ⟨h, rfl⟩ | ⟨h, rfl⟩
        · cases X <;> simp [selv, notv, h, holdsv]
        · cases X <;> simp [selv, notv, asBool_zero, asBool_one, holdsv, h0]
        · cases X <;> simp [selv, notv, asBool_zero, asBool_one, holdsv, h0]

/-- The asserts of a pair: `select g1 c 1` and `select g2 c 1`, one guard the
    negation of the other, both pass exactly when `select g1 c c` does. -/
theorem merge_assert_ok (p : Prims) (env : Env) (g1 g2 c c2 : Expr) (hc : c2.eval p env = c.eval p env)
    (hn : g1.eval p env = (Expr.select g2 (.const 0) (.const 1)).eval p env ∨
          g2.eval p env = (Expr.select g1 (.const 0) (.const 1)).eval p env) :
    decide ((Expr.select g1 c c).eval p env = some 1) =
      (decide ((Expr.select g1 c (.const 1)).eval p env = some 1) &&
        decide ((Expr.select g2 c2 (.const 1)).eval p env = some 1)) := by
  simp only [eval_not] at hn
  simp only [eval_select, Expr.eval, Fr.ofInt_one, hc]
  exact selv_assert _ _ _ hn

theorem checkOk_constrain (p : Prims) (env : Env) (e : Expr) (r : Range) :
    checkOk p env (.constrain e r) = holdsv r (e.eval p env) := by
  simp only [checkOk, holdsv]

/-- The range checks of a pair, likewise, when 0 passes the check. -/
theorem merge_constrain_ok (p : Prims) (env : Env) (g1 g2 x x2 : Expr) (r : Range) (h0 : r.holds 0 = true)
    (hx : x2.eval p env = x.eval p env)
    (hn : g1.eval p env = (Expr.select g2 (.const 0) (.const 1)).eval p env ∨
          g2.eval p env = (Expr.select g1 (.const 0) (.const 1)).eval p env) :
    holdsv r ((Expr.select g1 x x).eval p env) =
      (holdsv r ((Expr.select g1 x (.const 0)).eval p env) && holdsv r ((Expr.select g2 x2 (.const 0)).eval p env)) := by
  simp only [eval_not] at hn
  simp only [eval_select, Expr.eval, Fr.ofInt_zero, hx]
  exact selv_constrain _ _ _ r h0 hn

theorem isNot_eval {p : Prims} {D : Defs} {env : Env} (hD : D.Valid p env) {g' g : Expr}
    (h : D.isNot g' g = true) : g'.eval p env = (Expr.select g (.const 0) (.const 1)).eval p env := by
  unfold Defs.isNot at h
  rw [← Defs.resolve_eval hD g', eq_of_beq h]

/-- What `mergePair` returns is a check that passes exactly when both do. -/
theorem mergePair_ok {p : Prims} {D : Defs} {env : Env} (hD : D.Valid p env) {s t m : Stmt}
    (h : mergePair D s t = some m) :
    s.isCheck = true ∧ t.isCheck = true ∧ m.isCheck = true ∧
      checkOk p env m = (checkOk p env s && checkOk p env t) := by
  unfold mergePair at h
  split at h
  · rename_i g1 c1 msg g2 c2 _
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.or_eq_true] at hc
      obtain ⟨hc, hn⟩ := hc
      have hc : c2.eval p env = c1.eval p env := by
        rw [← Expr.commute_eval p env c2, ← Expr.commute_eval p env c1, eq_of_beq hc]
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨rfl, rfl, rfl, ?_⟩
      simp only [checkOk]
      exact merge_assert_ok p env g1 g2 c1 c2 hc (hn.imp (isNot_eval hD) (isNot_eval hD))
    · simp at h
  · rename_i g1 x1 r1 g2 x2 r2
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.or_eq_true] at hc
      obtain ⟨⟨⟨hx, hr⟩, h0⟩, hn⟩ := hc
      have hx : x2.eval p env = x1.eval p env := by
        rw [← Expr.commute_eval p env x2, ← Expr.commute_eval p env x1, eq_of_beq hx]
      have hr := Range.same_eq hr
      subst hr
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨rfl, rfl, rfl, ?_⟩
      simp only [checkOk_constrain]
      exact merge_constrain_ok p env g1 g2 x1 x2 r1 h0 hx (hn.imp (isNot_eval hD) (isNot_eval hD))
    · simp at h
  · simp at h

theorem findPartner_spec (D : Defs) (s : Stmt) :
    ∀ (bound : List Var) (l : List Stmt) (m : Stmt) (l' : List Stmt),
      findPartner D s bound l = some (m, l') →
      ∃ pre t post, l = pre ++ t :: post ∧ l' = pre ++ post ∧ mergePair D s t = some m ∧
        ∀ v ∈ t.checkVars, v ∉ bound ∧ ∀ u ∈ pre, v ∉ u.binds
  | _, [], _, _, h => by simp [findPartner] at h
  | bound, t :: ts, m, l', h => by
      have later : (findPartner D s (bound ++ t.binds) ts).map (fun r => (r.1, t :: r.2)) = some (m, l') →
          ∃ pre t' post, t :: ts = pre ++ t' :: post ∧ l' = pre ++ post ∧ mergePair D s t' = some m ∧
            ∀ v ∈ t'.checkVars, v ∉ bound ∧ ∀ u ∈ pre, v ∉ u.binds := by
        intro h'
        simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h'
        obtain ⟨⟨m', r⟩, hr, rfl, rfl⟩ := h'
        obtain ⟨pre, t', post, rfl, rfl, hm, hv⟩ := findPartner_spec D s (bound ++ t.binds) ts m' r hr
        refine ⟨t :: pre, t', post, rfl, rfl, hm, fun v hv' => ?_⟩
        obtain ⟨hb, hpre⟩ := hv v hv'
        simp only [List.mem_append, not_or] at hb
        refine ⟨hb.1, fun u hu => ?_⟩
        simp only [List.mem_cons] at hu
        rcases hu with rfl | hu
        · exact hb.2
        · exact hpre u hu
      simp only [findPartner] at h
      split at h
      · rename_i m' hm
        split at h
        · rename_i hall
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨[], t, ts, rfl, rfl, hm, fun v hv => ⟨?_, fun u hu => by simp at hu⟩⟩
          have := List.all_eq_true.mp hall v hv
          simpa using this
        · exact later h
      · exact later h

section Runner
variable {S : Type} {p : Prims} {envOf : S → Env} {step : S → Stmt → Option S}

/-- The merged body runs exactly as the original, from any state where what
    the pass knows holds. -/
theorem runL_mergeGo (hs : StepOK p envOf step) :
    ∀ (n : Nat) (D : Defs) (L : List Stmt) (st : S), D.Valid p (envOf st) →
      runL step (mergeGo n D L) st = runL step L st
  | 0, _, _, _, _ => rfl
  | _ + 1, _, [], _, _ => rfl
  | n + 1, D, s :: rest, st, hD => by
      simp only [mergeGo]
      split
      · rename_i hcheck
        split
        · rename_i m rest' hf
          obtain ⟨pre, t, post, rfl, rfl, hm, hv⟩ := findPartner_spec D s [] rest m rest' hf
          obtain ⟨_, ht, hmc, hok⟩ := mergePair_ok hD hm
          have hpre : ∀ u ∈ pre, ∀ v ∈ t.checkVars, v ∉ u.binds := fun u hu v hv' => (hv v hv').2 u hu
          simp only [runL, hs.check st m hmc, hs.check st s hcheck, hok]
          by_cases h1 : checkOk p (envOf st) s = true
          · by_cases h2 : checkOk p (envOf st) t = true
            · simp only [h1, h2, Bool.and_self, ite_true, Option.bind_some]
              rw [runL_append_cons_check hs ht pre post st hpre, h2, if_pos rfl, runL_mergeGo hs n D _ st hD]
            · simp only [h1, h2, Bool.and_false, ite_true, Option.bind_some, Bool.false_eq_true, ite_false,
                Option.bind_none]
              rw [runL_append_cons_check hs ht pre post st hpre]
              simp [h2]
          · simp [h1]
        · simp only [runL, hs.check st s hcheck]
          split
          · simp only [Option.bind_some]; exact runL_mergeGo hs n D rest st hD
          · rfl
      · simp only [runL]
        cases h : step st s with
        | none => rfl
        | some st' => exact runL_mergeGo hs n _ rest st' (Defs.valid_after hs hD h)

end Runner

/-! ## The two runners -/

theorem execAll_eq_runL (p : Prims) :
    ∀ (L : List Stmt) (st : RunState), execAll p L st = runL (fun st t => t.exec p st) L st
  | [], _ => rfl
  | t :: ts, st => by
      simp only [execAll, runL]
      cases t.exec p st <;> simp [execAll_eq_runL p ts]

theorem steps_eq_runL {ω σ : Type} (p : Prims) (O : Exec.Oracles ω σ) :
    ∀ (L : List Stmt) (st : Exec.State ω σ), Exec.steps p O L st = runL (fun st t => Exec.step p O st t) L st
  | [], _ => rfl
  | t :: ts, st => by
      simp only [Exec.steps, runL]
      cases Exec.step p O st t <;> simp [steps_eq_runL p O ts]

theorem exec_stepOK (p : Prims) : StepOK p (fun st : RunState => st.env) (fun st t => t.exec p st) where
  keeps st st' t h u hu := Stmt.exec_keeps t h u hu
  check st t ht := exec_check p st t ht
  bind st st' v hint e h := by
    simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨x, hx, rfl⟩ := h
    simp [Env.set, hx]

theorem step_stepOK {ω σ : Type} (p : Prims) (O : Exec.Oracles ω σ) :
    StepOK p (fun st : Exec.State ω σ => st.env) (fun st t => Exec.step p O st t) where
  keeps st st' t h u hu := Stmt.step_keeps t h u hu
  check st t ht := step_check p O st t ht
  bind st st' v hint e h := by
    simp only [Exec.step, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨x, hx, rfl⟩ := h
    simp [Env.set, hx]

theorem Defs.valid_nil (p : Prims) (env : Env) : Defs.Valid p [] env := by
  intro v e h; simp at h

/-- `Circuit.mergeChecks` does not change a run at all. -/
theorem Circuit.mergeChecks_run (p : Prims) (c : Circuit) (inputs priv pub : List Fr) :
    c.mergeChecks.run p inputs priv pub = c.run p inputs priv pub := by
  simp only [Circuit.run, Circuit.mergeChecks, List.toList_toArray]
  congr 1; funext env; congr 1
  rw [execAll_eq_runL, execAll_eq_runL, runL_mergeGo (exec_stepOK p) _ _ _ _ (Defs.valid_nil p _)]

/-- ... nor what the executor does. -/
theorem Circuit.mergeChecks_exec {ω σ : Type} (p : Prims) (O : Exec.Oracles ω σ) (c : Circuit)
    (inputs : List Fr) (private_ : ω) (ledger : σ) :
    Exec.run p O c.mergeChecks inputs private_ ledger = Exec.run p O c inputs private_ ledger := by
  simp only [Exec.run, Circuit.mergeChecks, List.toList_toArray]
  congr 1; funext env; congr 1
  rw [steps_eq_runL, steps_eq_runL, runL_mergeGo (step_stepOK p O) _ _ _ _ (Defs.valid_nil p _)]

theorem Circuit.mergeChecks_sound : Pass.Sound Circuit.mergeChecks :=
  ⟨fun p c i pr pu => by rw [Circuit.mergeChecks_run], fun p O c i w l => by rw [Circuit.mergeChecks_exec]⟩

/-! ## Ledger statements -/

theorem mergePair_check {D : Defs} {s t m : Stmt} (h : mergePair D s t = some m) : m.ledgerProblem = none := by
  unfold mergePair at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h; subst h; rfl
    · simp at h
  · split at h
    · simp only [Option.some.injEq] at h; subst h; rfl
    · simp at h
  · simp at h

/-- Every statement `mergeGo` returns was in its input, or is a merged check. -/
theorem mergeGo_ledgerProblem : ∀ (n : Nat) (D : Defs) (L : List Stmt), (∀ s ∈ L, s.ledgerProblem = none) →
    ∀ s ∈ mergeGo n D L, s.ledgerProblem = none
  | 0, _, _, h => h
  | _ + 1, _, [], _ => by simp [mergeGo]
  | n + 1, D, s :: rest, h => by
      simp only [mergeGo]
      split
      · split
        · rename_i m rest' hf
          obtain ⟨pre, t, post, rfl, rfl, hm, _⟩ := findPartner_spec D s [] rest m rest' hf
          intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact mergePair_check hm
          · exact mergeGo_ledgerProblem n D (pre ++ post)
              (fun y hy => h y (by simp only [List.mem_cons, List.mem_append] at hy ⊢; rcases hy with hy | hy <;> simp [hy])) x hx
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact h _ (by simp)
          · exact mergeGo_ledgerProblem n D rest (fun y hy => h y (by simp [hy])) x hx
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact h _ (by simp)
        · exact mergeGo_ledgerProblem n _ rest (fun y hy => h y (by simp [hy])) x hx

end Damp.IR
