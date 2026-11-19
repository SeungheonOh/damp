/-
Soundness of `Circuit.bounds2` (`Damp/Optimize/Bounds2.lean`).

The pass is `Circuit.bounds` with relational facts. The proof reuses
`Damp/Proofs/Optimize/Bounds.lean` for everything the two passes share (the
statements kept, `Bounds.tighten`, the bounds of variables) and adds:

* `Bounds2.RHolds`: every fact `(g, a, b)` is true of the environment;
  `Bounds2.assertRel_holds` (a passing assert of the `¬ a < b` shapes
  establishes one), `Bounds2.forgetRel_holds` (facts not mentioning the
  variables a statement binds survive it);
* `Bounds2.ub2_spec`: the bound `ub2` bounds the value; the new case is
  `(a + -b).val = a.val - b.val` when `b.val ≤ a.val` (`Bounds2.val_sub`).

As for `bounds`, the environment is never changed, so the rewritten circuit
runs through exactly the same states as the original.
-/
import Damp.Optimize.Bounds2
import Damp.Proofs.Optimize.Bounds
import Damp.Proofs.Prune

set_option linter.unusedSimpArgs false

namespace Damp.IR
namespace Bounds2
open Bounds
open Damp.Zkir (Prims)

/-! ## Field values -/

/-- Without wrap-around, `a + -b` is `a - b`. -/
theorem val_sub {A B : Fr} (h : B.val ≤ A.val) : (A + -B).val = A.val - B.val := by
  show (A.val + (Fr.modulus - B.val) % Fr.modulus) % Fr.modulus = A.val - B.val
  have hA := A.isLt
  by_cases hb : B.val = 0
  · rw [hb, Nat.sub_zero, Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt hA, Nat.sub_zero]
  · rw [Nat.mod_eq_of_lt (by omega : Fr.modulus - B.val < Fr.modulus),
      show A.val + (Fr.modulus - B.val) = (A.val - B.val) + Fr.modulus by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-! ## Facts -/

section Facts
variable (p : Prims)

/-- Every relational fact is true of the environment. -/
def RHolds (env : Env) (R : Rel) : Prop :=
  ∀ g a b, (g, a, b) ∈ R → ∀ G A B, g.eval p env = some G → a.eval p env = some A →
    b.eval p env = some B → G = 1 → B.val ≤ A.val

variable {p}

theorem rholds_nil (env : Env) : RHolds p env [] := fun _ _ _ h => nomatch h

/-- After binding the variables `vs`, the facts not mentioning them still hold. -/
theorem forgetRel_holds {env r : Env} {R : Rel} {vs : List Var} (h : RHolds p env R)
    (hout : ∀ w, w ∉ vs → r w = env w) : RHolds p r (forgetRel R vs) := by
  intro g a b hm G A B hg ha hb hG
  obtain ⟨hm, hc⟩ := List.mem_filter.mp hm
  simp only [Bool.not_eq_true'] at hc
  have hnot : ∀ u, u ∈ g.vars ++ a.vars ++ b.vars → u ∉ vs := by
    intro u hu huv
    have : (g.vars ++ a.vars ++ b.vars).any vs.contains = true :=
      List.any_eq_true.mpr ⟨u, hu, List.contains_iff_mem.mpr huv⟩
    rw [this] at hc
    simp at hc
  have ag : ∀ e : Expr, (∀ u, u ∈ e.vars → u ∈ g.vars ++ a.vars ++ b.vars) →
      e.eval p r = e.eval p env :=
    fun e he => Emit.eval_congr p e (fun u hu => hout u (hnot u (he u hu)))
  rw [ag g (fun u hu => by simp [hu])] at hg
  rw [ag a (fun u hu => by simp [hu])] at ha
  rw [ag b (fun u hu => by simp [hu])] at hb
  exact h g a b hm G A B hg ha hb hG

/-- `¬ a < b` has the value 1: then `b ≤ a`. -/
theorem notLt_spec {n : Nat} {a b : Expr} {A B : Fr}
    (h : (Expr.select (.lt n a b) (.const 0) (.const 1)).eval p env = some 1)
    (ha : a.eval p env = some A) (hb : b.eval p env = some B) : B.val ≤ A.val := by
  simp only [Expr.eval, ha, hb, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at h
  split at h
  · simp only [Option.bind_some, Option.bind_eq_some_iff] at h
    obtain ⟨bc, hbc, h⟩ := h
    have hbc' := asBool_some hbc
    cases bc
    · have hd : decide (A.val < B.val) = false := by
        cases hd : decide (A.val < B.val)
        · rfl
        · rw [hd] at hbc'; exact absurd hbc' (by decide)
      simp only [decide_eq_false_iff_not] at hd
      omega
    · simp only [ite_true, Option.some.injEq] at h
      exact absurd h (by decide)
  · simp at h

theorem select_eval_some {env : Env} {c a b : Expr} {x : Fr} (h : (Expr.select c a b).eval p env = some x) :
    ∃ C A B bc, c.eval p env = some C ∧ a.eval p env = some A ∧ b.eval p env = some B ∧
      asBool C = some bc ∧ x = if bc then A else B := by
  simp only [Expr.eval, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨C, hc, A, ha, B, hb, bc, hbc, h⟩ := h
  exact ⟨C, A, B, bc, hc, ha, hb, hbc, h.symm⟩

/-- After an assertion passes, the order it states holds. -/
theorem assertRel_holds {env : Env} {R : Rel} (h : RHolds p env R) {c : Expr} {x : Fr}
    (hx : c.eval p env = some x) (ht : asBool x = some true) : RHolds p env (assertRel R c) := by
  have hx1 : x = 1 := asBool_some ht
  subst hx1
  unfold assertRel
  split
  · next n a b =>
    intro g' a' b' hm G A B hg ha hb hG
    rcases List.mem_cons.mp hm with heq | hm
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      exact notLt_spec hx ha hb
    · exact h g' a' b' hm G A B hg ha hb hG
  · next g n a b =>
    intro g' a' b' hm G A B hg ha hb hG
    rcases List.mem_cons.mp hm with heq | hm
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      subst hG
      obtain ⟨G', I, O, bg, hg', hI, _, hbg, hx⟩ := select_eval_some hx
      rw [hg] at hg'
      cases hg'
      have : bg = true := by
        have := asBool_some hbg
        cases bg
        · exact absurd this (by decide)
        · rfl
      subst this
      simp only [ite_true] at hx
      subst hx
      exact notLt_spec hI ha hb
    · exact h g' a' b' hm G A B hg ha hb hG
  · exact h

end Facts

/-! ## Bounds of expressions -/

theorem contains_mem {R : Rel} {q : Expr × Expr × Expr} (h : R.contains q = true) : q ∈ R :=
  List.contains_iff_mem.mp h

/-- The bound `ub2` bounds the value of an expression, whenever it has one. -/
theorem ub2_spec (p : Prims) {env : Env} {f : UB} {R : Rel} (hf : Holds env f) (hR : RHolds p env R)
    (e : Expr) {x : Fr} {B : Nat} (he : e.eval p env = some x) (hb : ub2 f R e = some B) : x.val ≤ B := by
  unfold ub2 at hb
  split at hb
  · next a b =>
    split at hb
    · next hc =>
      simp only [Expr.eval, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        Option.some.injEq] at he
      obtain ⟨A, ha, Bv, ⟨B', hb', rfl⟩, rfl⟩ := he
      have hle := hR _ a b (contains_mem hc) 1 A B' rfl ha hb' rfl
      rw [val_sub hle]
      have := ub_spec p hf a ha hb
      omega
    · exact ub_spec p hf _ he hb
  · next g a b d =>
    split at hb
    · next hc =>
      have hfallback : ub f (.select g (.add a (.neg b)) d) = some B → x.val ≤ B :=
        fun h => ub_spec p hf _ he h
      cases hA : ub f a <;> cases hD : ub f d <;> simp only [hA, hD] at hb
      · exact hfallback hb
      · exact hfallback hb
      · exact hfallback hb
      · next ua ud =>
        simp only [Option.some.injEq] at hb
        subst hb
        obtain ⟨G, V, D, bg, hg, hv, hd, hbg, he⟩ := select_eval_some he
        simp only [Expr.eval, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
          Option.some.injEq] at hv
        obtain ⟨A, ha, Bv, ⟨B', hb', rfl⟩, rfl⟩ := hv
        have hG := asBool_some hbg
        cases bg
        · simp only [Bool.false_eq_true, ite_false] at he
          subst he
          have := ub_spec p hf d hd hD
          omega
        · simp only [ite_true] at he
          subst he
          have hle := hR _ a b (contains_mem hc) G A B' hg ha hb' hG
          rw [val_sub hle]
          have := ub_spec p hf a ha hA
          omega
    · exact ub_spec p hf _ he hb
  · exact ub_spec p hf _ he hb

/-- A range check that `implied2` accepts passes. -/
theorem implied2_spec (p : Prims) {env : Env} {f : UB} {R : Rel} (hf : Holds env f) (hR : RHolds p env R)
    {e : Expr} {r : Range} (h : implied2 f R e r = true) : ∃ x, e.eval p env = some x ∧ r.holds x = true := by
  simp only [implied2, Bool.and_eq_true] at h
  obtain ⟨ht, hw⟩ := h
  obtain ⟨x, hx⟩ := totalB_eval p hf e ht
  refine ⟨x, hx, ?_⟩
  split at hw
  · next B hB => exact within_spec (ub2_spec p hf hR e hx hB) hw
  · cases hw

/-! ## What a statement binds -/

/-- The variables a statement binds. -/
def boundVars : Stmt → List Var
  | .bind v _ _ => [v]
  | .witness _ _ _ outs _ => outs.map (·.1)
  | .ledger _ reads _ => reads
  | _ => []

theorem exec_frame (p : Prims) {s s' : RunState} (st : Stmt) (h : st.exec p s = some s') :
    ∀ w, w ∉ boundVars st → s'.env w = s.env w := by
  cases st with
  | bind v hint e =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨x, _, rfl⟩ := h
      intro w hw; simp only [boundVars, List.mem_singleton] at hw; simp [Env.set, hw]
  | assert c msg =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨x, _, b, _, h⟩ := h
      cases b
      · simp at h
      · simp only [ite_true, Option.pure_def, Option.some.injEq] at h; subst h; exact fun _ _ => rfl
  | constrain e r =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨x, _, h⟩ := h
      split at h
      · simp only [Option.pure_def, Option.some.injEq] at h; subst h; exact fun _ _ => rfl
      · cases h
  | witness g name args outs shape =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨gx, _, h⟩ := h
      split at h
      · simp only [Option.pure_def, Option.some.injEq] at h; subst h; exact fun _ _ => rfl
      · simp only [Option.bind_eq_some_iff] at h
        obtain ⟨act, _, ⟨r, pv⟩, hrd, h⟩ := h
        simp only [Option.pure_def, Option.some.injEq] at h; subst h
        exact (readAll_post hrd).1
  | ledger g reads ops =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨gx, _, h⟩ := h
      split at h
      · simp only [Option.pure_def, Option.some.injEq] at h; subst h; exact fun _ _ => rfl
      · simp only [Option.bind_eq_some_iff] at h
        obtain ⟨act, _, ⟨r, pv⟩, hrd, gs, _, h⟩ := h
        simp only [Option.pure_def, Option.some.injEq] at h; subst h
        have hout := (readAll_post hrd).1
        rw [reads_vars] at hout
        exact hout

theorem step_frame {ω σ : Type} (p : Prims) (O : Exec.Oracles ω σ) {s s' : Exec.State ω σ} (st : Stmt)
    (h : Exec.step p O s st = some s') : ∀ w, w ∉ boundVars st → s'.env w = s.env w := by
  cases st with
  | bind v hint e =>
      simp only [Exec.step, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨x, _, rfl⟩ := h
      intro w hw; simp only [boundVars, List.mem_singleton] at hw; simp [Env.set, hw]
  | assert c msg =>
      simp only [Exec.step, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨x, _, b, _, h⟩ := h
      cases b
      · simp at h
      · simp only [ite_true, Option.pure_def, Option.some.injEq] at h; subst h; exact fun _ _ => rfl
  | constrain e r =>
      simp only [Exec.step, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨x, _, h⟩ := h
      split at h
      · simp only [Option.pure_def, Option.some.injEq] at h; subst h; exact fun _ _ => rfl
      · cases h
  | witness g name args outs shape =>
      simp only [Exec.step, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨gx, _, h⟩ := h
      split at h
      · have he : s'.env = s.env := by
          split at h
          · simp only [Option.bind_eq_some_iff] at h
            obtain ⟨_, _, ⟨vals, pv⟩, _, h⟩ := h
            split at h
            · simp only [Option.pure_def, Option.some.injEq] at h; subst h; rfl
            · cases h
          · simp only [Option.pure_def, Option.some.injEq] at h; subst h; rfl
        rw [he]; exact fun _ _ => rfl
      · simp only [Option.bind_eq_some_iff] at h
        obtain ⟨act, _, h⟩ := h
        split at h
        · simp only [Option.bind_eq_some_iff] at h
          obtain ⟨_, _, ⟨vals, pv⟩, _, r, hasg, h⟩ := h
          simp only [Option.pure_def, Option.some.injEq] at h; subst h
          exact (assign_post hasg).1
        · simp only [Option.bind_eq_some_iff] at h
          obtain ⟨r, hasg, h⟩ := h
          simp only [Option.pure_def, Option.some.injEq] at h; subst h
          exact (assign_post hasg).1
  | ledger g reads ops =>
      simp only [Exec.step, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨gx, _, h⟩ := h
      split at h
      · simp only [Option.pure_def, Option.some.injEq] at h; subst h; exact fun _ _ => rfl
      · simp only [Option.bind_eq_some_iff] at h
        obtain ⟨act, _, h⟩ := h
        split at h
        · simp only [Option.bind_eq_some_iff] at h
          obtain ⟨_, _, ⟨vals, lg⟩, _, r, hasg, gs, _, h⟩ := h
          simp only [Option.pure_def, Option.some.injEq] at h; subst h
          have hout := (assign_post hasg).1
          rw [reads_vars] at hout
          exact hout
        · simp only [Option.bind_eq_some_iff] at h
          obtain ⟨r, hasg, gs, _, h⟩ := h
          simp only [Option.pure_def, Option.some.injEq] at h; subst h
          have hout := (assign_post hasg).1
          rw [reads_vars] at hout
          exact hout

/-- The relational facts after a statement, from those before it and how the
    statement leaves the environment. -/
theorem stmt_rel (p : Prims) {f : UB} {R : Rel} {env r : Env} (hR : RHolds p env R) (st : Stmt)
    (hframe : ∀ w, w ∉ boundVars st → r w = env w)
    (hassert : ∀ c msg, st = .assert c msg → r = env ∧ ∃ x, c.eval p env = some x ∧ asBool x = some true) :
    RHolds p r (stmt f R st).2.2 := by
  cases st with
  | bind v hint e => exact forgetRel_holds hR hframe
  | assert c msg =>
      obtain ⟨rfl, x, hx, ht⟩ := hassert c msg rfl
      exact assertRel_holds hR hx ht
  | constrain e r' =>
      have : r = env := funext fun w => hframe w (by simp [boundVars])
      subst this; exact hR
  | witness g name args outs shape => exact forgetRel_holds hR hframe
  | ledger g reads ops => exact forgetRel_holds hR hframe

/-! ## Statements, in the semantics -/

section Run
variable (p : Prims)

theorem stmt_exec {f : UB} {R : Rel} {s : RunState} (hf : Holds s.env f) (hR : RHolds p s.env R) (st : Stmt) :
    execAll p (stmt f R st).1 s = st.exec p s ∧
      ∀ s', st.exec p s = some s' → Holds s'.env (stmt f R st).2.1 ∧ RHolds p s'.env (stmt f R st).2.2 := by
  have hb := Bounds.stmt_exec p hf st
  have hrel : ∀ s', st.exec p s = some s' → RHolds p s'.env (stmt f R st).2.2 := by
    intro s' h
    refine stmt_rel p hR st (exec_frame p st h) ?_
    intro c msg hc
    subst hc
    simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, b, hbx, h⟩ := h
    cases b
    · simp at h
    · simp only [ite_true, Option.pure_def, Option.some.injEq] at h; subst h
      exact ⟨rfl, x, hx, hbx⟩
  cases st with
  | bind v hint e =>
      refine ⟨hb.1, fun s' h => ⟨?_, hrel s' h⟩⟩
      simp only [Stmt.exec, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨x, hx, rfl⟩ := h
      refine learn_holds (forget_holds hf ?_) ?_
      · intro w hw; simp at hw; simp [Env.set, hw]
      · intro B hB
        simp only [Env.set, ite_true]
        exact ub2_spec p hf hR e hx hB
  | assert c msg => exact ⟨hb.1, fun s' h => ⟨hb.2 s' h, hrel s' h⟩⟩
  | constrain e r =>
      refine ⟨?_, fun s' h => ⟨hb.2 s' h, hrel s' h⟩⟩
      simp only [stmt]
      split
      · next hi =>
        obtain ⟨x, hx, hh⟩ := implied2_spec p hf hR hi
        simp [execAll, Stmt.exec, Option.bind_eq_bind, hx, hh]
      · exact hb.1
  | witness g name args outs shape => exact ⟨hb.1, fun s' h => ⟨hb.2 s' h, hrel s' h⟩⟩
  | ledger g reads ops => exact ⟨hb.1, fun s' h => ⟨hb.2 s' h, hrel s' h⟩⟩

theorem stmts_exec : ∀ (f : UB) (R : Rel) (l : List Stmt) (s : RunState), Holds s.env f → RHolds p s.env R →
    execAll p (stmts f R l).1 s = execAll p l s ∧
      ∀ s', execAll p l s = some s' → Holds s'.env (stmts f R l).2
  | f, R, [], s, hf, _ => ⟨rfl, fun s' h => by cases h; exact hf⟩
  | f, R, st :: rest, s, hf, hR => by
      obtain ⟨h1, h2⟩ := stmt_exec p hf hR st
      simp only [stmts, execAll_append, h1, execAll, Option.bind_eq_bind]
      constructor
      · cases h : st.exec p s with
        | none => rfl
        | some s1 => exact (stmts_exec _ _ rest s1 (h2 s1 h).1 (h2 s1 h).2).1
      · intro s' h
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨s1, hs1, h⟩ := h
        exact (stmts_exec _ _ rest s1 (h2 s1 hs1).1 (h2 s1 hs1).2).2 s' h

end Run

/-! ## Statements, in the executor -/

section Executor
variable {ω σ : Type} (p : Prims) (O : Exec.Oracles ω σ)

theorem stmt_step {f : UB} {R : Rel} {s : Exec.State ω σ} (hf : Holds s.env f) (hR : RHolds p s.env R)
    (st : Stmt) :
    Exec.steps p O (stmt f R st).1 s = Exec.step p O s st ∧
      ∀ s', Exec.step p O s st = some s' →
        Holds s'.env (stmt f R st).2.1 ∧ RHolds p s'.env (stmt f R st).2.2 := by
  have hb := Bounds.stmt_step p O hf st
  have hrel : ∀ s', Exec.step p O s st = some s' → RHolds p s'.env (stmt f R st).2.2 := by
    intro s' h
    refine stmt_rel p hR st (step_frame p O st h) ?_
    intro c msg hc
    subst hc
    simp only [Exec.step, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, b, hbx, h⟩ := h
    cases b
    · simp at h
    · simp only [ite_true, Option.pure_def, Option.some.injEq] at h; subst h
      exact ⟨rfl, x, hx, hbx⟩
  cases st with
  | bind v hint e =>
      refine ⟨hb.1, fun s' h => ⟨?_, hrel s' h⟩⟩
      simp only [Exec.step, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨x, hx, rfl⟩ := h
      refine learn_holds (forget_holds hf ?_) ?_
      · intro w hw; simp at hw; simp [Env.set, hw]
      · intro B hB
        simp only [Env.set, ite_true]
        exact ub2_spec p hf hR e hx hB
  | assert c msg => exact ⟨hb.1, fun s' h => ⟨hb.2 s' h, hrel s' h⟩⟩
  | constrain e r =>
      refine ⟨?_, fun s' h => ⟨hb.2 s' h, hrel s' h⟩⟩
      simp only [stmt]
      split
      · next hi =>
        obtain ⟨x, hx, hh⟩ := implied2_spec p hf hR hi
        simp [Exec.steps, Exec.step, Option.bind_eq_bind, hx, hh]
      · exact hb.1
  | witness g name args outs shape => exact ⟨hb.1, fun s' h => ⟨hb.2 s' h, hrel s' h⟩⟩
  | ledger g reads ops => exact ⟨hb.1, fun s' h => ⟨hb.2 s' h, hrel s' h⟩⟩

theorem stmts_steps : ∀ (f : UB) (R : Rel) (l : List Stmt) (s : Exec.State ω σ), Holds s.env f →
    RHolds p s.env R →
    Exec.steps p O (stmts f R l).1 s = Exec.steps p O l s ∧
      ∀ s', Exec.steps p O l s = some s' → Holds s'.env (stmts f R l).2
  | f, R, [], s, hf, _ => ⟨rfl, fun s' h => by cases h; exact hf⟩
  | f, R, st :: rest, s, hf, hR => by
      obtain ⟨h1, h2⟩ := stmt_step p O hf hR st
      simp only [stmts, Exec.steps_append, h1, Exec.steps, Option.bind_eq_bind]
      constructor
      · cases h : Exec.step p O s st with
        | none => rfl
        | some s1 => exact (stmts_steps _ _ rest s1 (h2 s1 h).1 (h2 s1 h).2).1
      · intro s' h
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨s1, hs1, h⟩ := h
        exact (stmts_steps _ _ rest s1 (h2 s1 hs1).1 (h2 s1 hs1).2).2 s' h

end Executor

/-! ## Ledger well-formedness -/

theorem stmt_sub {f : UB} {R : Rel} (st : Stmt) : ∀ x ∈ (stmt f R st).1, x ∈ (Bounds.stmt f st).1 := by
  cases st with
  | constrain e r =>
      simp only [stmt]
      split
      · simp
      · exact fun _ h => h
  | _ => exact fun _ h => h

theorem stmts_ledgerProblem : ∀ (f : UB) (R : Rel) (l : List Stmt), (∀ s ∈ l, s.ledgerProblem = none) →
    ∀ x ∈ (stmts f R l).1, x.ledgerProblem = none
  | _, _, [], _ => by simp [stmts]
  | f, R, st :: rest, h => by
      intro x hx
      simp only [stmts, List.mem_append] at hx
      rcases hx with hx | hx
      · rw [Bounds.stmt_ledgerProblem st x (stmt_sub st x hx)]; exact h st (by simp)
      · exact stmts_ledgerProblem _ _ rest (fun s hs => h s (by simp [hs])) x hx

end Bounds2

open Damp.Zkir (Prims)

/-- The rewritten circuit runs exactly as the original. -/
theorem Circuit.bounds2_run (p : Prims) (c : Circuit) (inputs priv pub : List Fr) :
    c.bounds2.run p inputs priv pub = c.run p inputs priv pub := by
  simp only [Circuit.run, Circuit.bounds2, List.toList_toArray, Option.bind_eq_bind]
  cases bindInputs (fun _ => 0) c.inputs inputs with
  | none => rfl
  | some env0 =>
      simp only [Option.bind_some]
      obtain ⟨h1, h2⟩ := Bounds2.stmts_exec p [] [] c.body.toList { env := env0, priv, pub }
        (Bounds.holds_nil _) (Bounds2.rholds_nil _)
      rw [h1]
      cases h : execAll p c.body.toList { env := env0, priv, pub } with
      | none => rfl
      | some s' =>
          simp only [Option.bind_some]
          rw [Bounds.tighten_evalList p (h2 s' h)]

/-- The executor runs the rewritten circuit exactly as the original. -/
theorem Circuit.bounds2_runExec {ω σ : Type} (p : Prims) (O : Exec.Oracles ω σ) (c : Circuit)
    (inputs : List Fr) (private_ : ω) (ledger : σ) :
    Exec.run p O c.bounds2 inputs private_ ledger = Exec.run p O c inputs private_ ledger := by
  simp only [Exec.run, Circuit.bounds2, List.toList_toArray, Option.bind_eq_bind]
  cases bindInputs (fun _ => 0) c.inputs inputs with
  | none => rfl
  | some env0 =>
      simp only [Option.bind_some]
      obtain ⟨h1, h2⟩ := Bounds2.stmts_steps p O [] [] c.body.toList { env := env0, private_, ledger }
        (Bounds.holds_nil _) (Bounds2.rholds_nil _)
      rw [h1]
      cases h : Exec.steps p O c.body.toList { env := env0, private_, ledger } with
      | none => rfl
      | some s' =>
          simp only [Option.bind_some]
          rw [Bounds.tighten_evalList p (h2 s' h)]

/-- The value-range pass with relational facts is sound. -/
theorem Circuit.bounds2_sound : Pass.Sound Circuit.bounds2 :=
  ⟨fun p c i pr pu => by rw [Circuit.bounds2_run],
   fun p O c i w l => by rw [Circuit.bounds2_runExec]⟩

/-- The pass keeps every ledger statement as it is. -/
theorem Circuit.bounds2_checkLedger (c : Circuit) (h : c.checkLedger = .ok ()) :
    c.bounds2.checkLedger = .ok () := by
  simp only [Circuit.checkLedger, Circuit.bounds2, List.toList_toArray] at h ⊢
  rw [Bounds.checkLedgerFrom_ok] at h ⊢
  exact Bounds2.stmts_ledgerProblem [] [] _ h

end Damp.IR
