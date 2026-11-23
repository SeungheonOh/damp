/-
What is shipped means exactly the circuit it is emitted from, so the pass
theorems hold of the shipped ZKIR.

The emitter drops unused bindings (`Emit.pruneDeadBinds`), but only those whose
expression certainly has a value when control reaches them: `Bounds.totalB`
with the facts the statements before establish, and with the variables the
statements kept after it need to be 0 or 1 taken as 0 or 1 (if one is not, the
pruned circuit fails at that later statement anyway). A binding that might fail
is kept and emitted, as compactc keeps a checked cast nothing uses.

* `Emit.pruned_run_eq`: `(Emit.pruned c).run = c.run`, for every circuit,
  hash functions, inputs and transcripts: the same outcome, or both reject.
* `Emit.circuit_exact`: the ZKIR `Emit.circuit c` returns means exactly `c`.
* `Pass.SoundRun.pruned`, `Pass.SoundRunFor.pruned`: a pass's soundness
  transfers to the pruned circuits unchanged.
* `shipped_sameFor`, `shipped_preprocessFor`: the ZKIR shipped for `f c` and the
  ZKIR shipped for `c` (`--no-opt`) accept exactly the same proof data (inputs,
  private transcript, ledger reads, active public inputs, commitment), with the
  same outputs and active public inputs; at the default level and `--O2` for
  every hash functions, at `--O3` for `Crypto.prims`.
-/
import Damp.Proofs.Compiler
import Damp.Proofs.Optimize.Bounds

set_option linter.unusedSimpArgs false

namespace Damp.Emit
open Damp.IR
open Damp.Zkir (Prims Group Outcome)

theorem Agree.symm {L : List Var} {e₁ e₂ : Env} (h : Agree L e₁ e₂) : Agree L e₂ e₁ :=
  fun v hv => (h v hv).symm

/-! ## Variables that must be 0 or 1 -/

theorem val_le_one_of_asBool {x : Fr} {b : Bool} (h : asBool x = some b) : x.val ≤ 1 := by
  rw [Bounds.asBool_some h]; exact Bounds.val_ofBool_le b

theorem varOf_sub {e : Expr} {u : Var} (h : u ∈ varOf e) : e = .var u := by
  cases e <;> simp [varOf] at h
  subst h; rfl

theorem varOf_vars {e : Expr} {u : Var} (h : u ∈ varOf e) : u ∈ e.vars := by
  rw [varOf_sub h]; simp [Expr.vars]

mutual
theorem needsBool_vars : ∀ (e : Expr) {u : Var}, u ∈ needsBool e → u ∈ e.vars
  | .var _, _, h | .const _, _, h | .invalid _, _, h => by simp [needsBool] at h
  | .add a b, u, h | .mul a b, u, h | .eq a b, u, h | .lt _ a b, u, h => by
      simp only [needsBool, List.mem_append] at h
      simp only [Expr.vars, List.mem_append]
      rcases h with h | h
      · exact .inl (needsBool_vars a h)
      · exact .inr (needsBool_vars b h)
  | .neg a, u, h | .disclose a, u, h | .divmod _ _ a, u, h => by
      simp only [needsBool] at h
      simp only [Expr.vars]
      exact needsBool_vars a h
  | .select c a b, u, h => by
      simp only [needsBool, List.mem_append] at h
      simp only [Expr.vars, List.mem_append]
      rcases h with ((h | h) | h) | h
      · exact .inl (.inl (varOf_vars h))
      · exact .inl (.inl (needsBool_vars c h))
      · exact .inl (.inr (needsBool_vars a h))
      · exact .inr (needsBool_vars b h)
  | .hash xs, u, h | .phash _ _ xs, u, h => by
      simp only [needsBool] at h
      simp only [Expr.vars]
      exact needsBoolList_vars xs h
theorem needsBoolList_vars : ∀ (xs : List Expr) {u : Var}, u ∈ needsBoolList xs → u ∈ Expr.varsList xs
  | [], _, h => by simp [needsBoolList] at h
  | x :: xs, u, h => by
      simp only [needsBoolList, List.mem_append] at h
      simp only [Expr.varsList, List.mem_append]
      rcases h with h | h
      · exact .inl (needsBool_vars x h)
      · exact .inr (needsBoolList_vars xs h)
end

section Eval
variable (p : Prims) (env : Env)

mutual
/-- An expression that has a value finds the conditions it needs 0 or 1. -/
theorem needsBool_spec : ∀ (e : Expr) {x : Fr}, e.eval p env = some x → ∀ u ∈ needsBool e, (env u).val ≤ 1
  | .var _, _, _, _, h | .const _, _, _, _, h | .invalid _, _, _, _, h => by simp [needsBool] at h
  | .add a b, _, he, u, h | .mul a b, _, he, u, h | .eq a b, _, he, u, h => by
      simp only [Expr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
      obtain ⟨x, hx, y, hy, _⟩ := he
      simp only [needsBool, List.mem_append] at h
      rcases h with h | h
      · exact needsBool_spec a hx u h
      · exact needsBool_spec b hy u h
  | .lt _ a b, _, he, u, h => by
      simp only [Expr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
      obtain ⟨x, hx, y, hy, _⟩ := he
      simp only [needsBool, List.mem_append] at h
      rcases h with h | h
      · exact needsBool_spec a hx u h
      · exact needsBool_spec b hy u h
  | .neg a, _, he, u, h => by
      simp only [Expr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
      obtain ⟨x, hx, _⟩ := he
      exact needsBool_spec a hx u h
  | .disclose a, _, he, u, h => by
      simp only [Expr.eval] at he
      exact needsBool_spec a he u h
  | .divmod _ _ a, _, he, u, h => by
      simp only [Expr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
      obtain ⟨x, hx, _⟩ := he
      exact needsBool_spec a hx u h
  | .select c a b, _, he, u, h => by
      simp only [Expr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
      obtain ⟨cx, hc, x, hx, y, hy, b', hb, _⟩ := he
      simp only [needsBool, List.mem_append] at h
      rcases h with ((h | h) | h) | h
      · rw [varOf_sub h] at hc
        simp only [Expr.eval, Option.some.injEq] at hc
        subst hc
        exact val_le_one_of_asBool hb
      · exact needsBool_spec c hc u h
      · exact needsBool_spec a hx u h
      · exact needsBool_spec b hy u h
  | .hash xs, _, he, u, h => by
      simp only [Expr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
      obtain ⟨vs, hvs, _⟩ := he
      exact needsBoolList_spec xs hvs u h
  | .phash _ _ xs, _, he, u, h => by
      simp only [Expr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
      obtain ⟨vs, hvs, _⟩ := he
      exact needsBoolList_spec xs hvs u h
theorem needsBoolList_spec : ∀ (xs : List Expr) {vs : List Fr}, Expr.evalList p env xs = some vs →
    ∀ u ∈ needsBoolList xs, (env u).val ≤ 1
  | [], _, _, _, h => by simp [needsBoolList] at h
  | x :: xs, _, he, u, h => by
      simp only [Expr.evalList, Option.bind_eq_bind, Option.bind_eq_some_iff] at he
      obtain ⟨y, hy, ys, hys, _⟩ := he
      simp only [needsBoolList, List.mem_append] at h
      rcases h with h | h
      · exact needsBool_spec x hy u h
      · exact needsBoolList_spec xs hys u h
end

end Eval

theorem stmtNeedsBool_uses {st : Stmt} {u : Var} (h : u ∈ stmtNeedsBool st) : u ∈ uses st := by
  cases st with
  | bind v hint e => exact needsBool_vars e h
  | assert c _ =>
      simp only [stmtNeedsBool, List.mem_append] at h
      rcases h with h | h
      · exact varOf_vars h
      · exact needsBool_vars c h
  | constrain e _ => exact needsBool_vars e h
  | witness g _ args outs _ =>
      simp only [stmtNeedsBool, List.mem_append] at h
      simp only [uses, List.mem_append]
      rcases h with h | h
      · split at h
        · simp at h
        · exact .inl (varOf_vars h)
      · exact .inl (needsBool_vars g h)
  | ledger g reads ops =>
      simp only [stmtNeedsBool, List.mem_append] at h
      simp only [uses, List.mem_append]
      rcases h with h | h
      · split at h
        · simp at h
        · exact .inl (varOf_vars h)
      · exact .inl (needsBool_vars g h)

/-- A statement that runs finds the variables it needs 0 or 1 so. -/
theorem stmtNeedsBool_spec (p : Prims) (st : Stmt) {s s' : RunState} (h : st.exec p s = some s') :
    ∀ u ∈ stmtNeedsBool st, (s.env u).val ≤ 1 := by
  intro u hu
  cases st with
  | bind v hint e =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨x, hx, _⟩ := h
      exact needsBool_spec p s.env e hx u hu
  | assert c msg =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨x, hx, b, hb, _⟩ := h
      simp only [stmtNeedsBool, List.mem_append] at hu
      rcases hu with hu | hu
      · rw [varOf_sub hu] at hx
        simp only [Expr.eval, Option.some.injEq] at hx
        subst hx
        exact val_le_one_of_asBool hb
      · exact needsBool_spec p s.env c hx u hu
  | constrain e r =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨x, hx, _⟩ := h
      exact needsBool_spec p s.env e hx u hu
  | witness g name args outs shape =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨gx, hg, h⟩ := h
      simp only [stmtNeedsBool, List.mem_append] at hu
      rcases hu with hu | hu
      · split at hu
        · simp at hu
        · next hne =>
          simp only [hne, Bool.false_eq_true, ite_false, Option.bind_eq_some_iff] at h
          obtain ⟨act, hact, _⟩ := h
          rw [varOf_sub hu] at hg
          simp only [Expr.eval, Option.some.injEq] at hg
          subst hg
          exact val_le_one_of_asBool hact
      · exact needsBool_spec p s.env g hg u hu
  | ledger g reads ops =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨gx, hg, h⟩ := h
      simp only [stmtNeedsBool, List.mem_append] at hu
      rcases hu with hu | hu
      · split at hu
        · simp at hu
        · next hne =>
          simp only [hne, Bool.false_eq_true, ite_false, Option.bind_eq_some_iff] at h
          obtain ⟨act, hact, _⟩ := h
          rw [varOf_sub hu] at hg
          simp only [Expr.eval, Option.some.injEq] at hg
          subst hg
          exact val_le_one_of_asBool hact
      · exact needsBool_spec p s.env g hg u hu

/-- A statement changes only the variables it binds. -/
theorem exec_defs (p : Prims) (st : Stmt) {s s' : RunState} (h : st.exec p s = some s') :
    ∀ w, w ∉ defs st → s'.env w = s.env w := by
  intro w hw
  cases st with
  | bind v hint e =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨x, _, rfl⟩ := h
      simp only [defs, List.mem_singleton] at hw
      simp [Env.set, hw]
  | assert c msg =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨x, _, b, _, h⟩ := h
      cases b <;> simp at h
      subst h; rfl
  | constrain e r =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨x, _, h⟩ := h
      split at h
      · simp only [Option.pure_def, Option.some.injEq] at h; subst h; rfl
      · cases h
  | witness g name args outs shape =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨gx, _, h⟩ := h
      split at h
      · simp only [Option.pure_def, Option.some.injEq] at h; subst h; rfl
      · simp only [Option.bind_eq_some_iff] at h
        obtain ⟨act, _, ⟨r, pv⟩, hrd, h⟩ := h
        simp only [Option.pure_def, Option.some.injEq] at h; subst h
        exact readAll_unchanged hrd w hw
  | ledger g reads ops =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨gx, _, h⟩ := h
      split at h
      · simp only [Option.pure_def, Option.some.injEq] at h; subst h; rfl
      · simp only [Option.bind_eq_some_iff] at h
        obtain ⟨act, _, ⟨r, pv⟩, hrd, gs, _, h⟩ := h
        simp only [Option.pure_def, Option.some.injEq] at h; subst h
        exact readAll_unchanged hrd w (by rw [reads_vars]; exact hw)

/-! ## The backward pass -/

/-- What the kept statements need 0 or 1 they also read. -/
theorem pruneList_bools_live (out : List Var) :
    ∀ (ss : List (Stmt × Bounds.UB)) {u : Var}, u ∈ (pruneList ss out).bools → u ∈ (pruneList ss out).live
  | [], _, h => by simp [pruneList] at h
  | (st, f) :: rest, u, h => by
      have hfold : pruneList ((st, f) :: rest) out = pruneStep (st, f) (pruneList rest out) := rfl
      rw [hfold] at h ⊢
      rcases pruneStep_cases (st, f) (pruneList rest out) with hkeep | ⟨_, _, _, _, _, _, hdrop⟩
      · rw [hkeep] at h ⊢
        simp only [Acc.keep, List.mem_append, List.mem_filter] at h ⊢
        rcases h with h | ⟨h, _⟩
        · exact .inl (stmtNeedsBool_uses h)
        · exact .inr (pruneList_bools_live out rest h)
      · rw [hdrop] at h ⊢
        exact pruneList_bools_live out rest h

/-- Every run of the kept statements that succeeds starts from an environment
    where the variables they need 0 or 1 are. -/
theorem pruneList_bools (p : Prims) (out : List Var) :
    ∀ (ss : List (Stmt × Bounds.UB)) (s s' : RunState), execAll p (pruneList ss out).kept s = some s' →
      ∀ u ∈ (pruneList ss out).bools, (s.env u).val ≤ 1
  | [], _, _, _, u, h => by simp [pruneList] at h
  | (st, f) :: rest, s, s', hrun, u, h => by
      have hfold : pruneList ((st, f) :: rest) out = pruneStep (st, f) (pruneList rest out) := rfl
      rw [hfold] at h hrun
      rcases pruneStep_cases (st, f) (pruneList rest out) with hkeep | ⟨_, _, _, _, _, _, hdrop⟩
      · rw [hkeep] at h hrun
        simp only [Acc.keep, execAll, Option.bind_eq_bind, Option.bind_eq_some_iff] at hrun
        obtain ⟨mid, hst, hrest⟩ := hrun
        simp only [Acc.keep, List.mem_append, List.mem_filter, Bool.not_eq_true',
          List.contains_eq_any_beq, List.any_eq_false, beq_iff_eq] at h
        rcases h with h | ⟨h, hnd⟩
        · exact stmtNeedsBool_spec p st hst u h
        · have hu := pruneList_bools p out rest mid s' hrest u h
          rw [exec_defs p st hst u (fun hm => hnd u hm rfl)] at hu
          exact hu
      · rw [hdrop] at h hrun
        exact pruneList_bools p out rest s s' hrun u h

/-- **The converse of `pruneList_run`.** Running the kept statements from an
    environment that agrees on everything read from here on, the original
    statements run from there too, to the same transcripts and public inputs,
    provided the facts known here hold. -/
theorem pruneList_run_rev (p : Prims) (out : List Var) :
    ∀ (f : Bounds.UB) (ss : List Stmt) (e₁ e₂ : Env) (priv pub : List Fr) (groups : List Group)
      (s₂ : RunState),
      Bounds.Holds e₁ f →
      Agree (pruneList (annotate f ss) out).live e₁ e₂ →
      execAll p (pruneList (annotate f ss) out).kept { env := e₂, priv, pub, groups } = some s₂ →
      ∃ e₁', execAll p ss { env := e₁, priv, pub, groups }
          = some { env := e₁', priv := s₂.priv, pub := s₂.pub, groups := s₂.groups } ∧
        Agree out e₁' s₂.env
  | _, [], e₁, e₂, priv, pub, groups, s₂, _, h, hrun => by
      simp only [annotate, pruneList, List.foldr_nil, execAll, Option.some.injEq] at hrun h ⊢
      subst hrun
      exact ⟨e₁, rfl, h⟩
  | f, st :: rest, e₁, e₂, priv, pub, groups, s₂, hf, h, hrun => by
      have hfold : pruneList (annotate f (st :: rest)) out =
          pruneStep (st, f) (pruneList (annotate (Bounds.stmt f st).2 rest) out) := rfl
      rw [hfold] at h hrun
      rcases pruneStep_cases (st, f) (pruneList (annotate (Bounds.stmt f st).2 rest) out) with
        hkeep | ⟨v, hint, e, hst', hv, htot, hdrop⟩
      · rw [hkeep] at h hrun
        simp only [Acc.keep, execAll, Option.bind_eq_bind, Option.bind_eq_some_iff] at hrun h
        obtain ⟨mid, hst₂, hrest⟩ := hrun
        obtain ⟨e₁m, hst₁, hag⟩ := stmt_congr p st e₂ e₁ priv pub groups mid h.symm hst₂
        have hf' := (Bounds.stmt_exec p hf st).2 _ hst₁
        obtain ⟨e₁', hrun₁, hag'⟩ := pruneList_run_rev p out _ rest e₁m mid.env mid.priv mid.pub mid.groups s₂
          hf' hag.right.symm hrest
        refine ⟨e₁', ?_, hag'⟩
        simp only [execAll, hst₁, Option.bind_eq_bind, Option.bind_some]
        exact hrun₁
      · simp only at hst'
        subst hst'
        rw [hdrop] at h hrun
        -- The dropped binding has a value: its facts hold here.
        have hbools : Bounds.Holds e₁
            ((pruneList (annotate (Bounds.stmt f (.bind v hint e)).2 rest) out).bools.map (·, 1)) := by
          intro u b hm
          simp only [List.mem_map, Prod.mk.injEq] at hm
          obtain ⟨u', hu', rfl, rfl⟩ := hm
          have h1 := pruneList_bools p out _ _ _ hrun u' hu'
          rw [h u' (pruneList_bools_live out _ hu')]
          exact h1
        obtain ⟨x, hx⟩ := Bounds.totalB_eval p (Bounds.holds_append hbools hf) e htot
        have hst₁ : (Stmt.bind v hint e).exec p { env := e₁, priv, pub, groups }
            = some { env := e₁.set v x, priv, pub, groups } := by
          simp [Stmt.exec, hx]
        have hf' := (Bounds.stmt_exec p hf (.bind v hint e)).2 _ hst₁
        have hnot : v ∉ (pruneList (annotate (Bounds.stmt f (.bind v hint e)).2 rest) out).live := by
          intro hmem
          have : (pruneList (annotate (Bounds.stmt f (.bind v hint e)).2 rest) out).live.contains v = true := by
            simpa using hmem
          rw [hv] at this
          exact absurd this (by simp)
        obtain ⟨e₁', hrun₁, hag'⟩ := pruneList_run_rev p out _ rest (e₁.set v x) e₂ priv pub groups s₂
          hf' (h.set_left v x hnot) hrun
        refine ⟨e₁', ?_, hag'⟩
        simp only [execAll, hst₁, Option.bind_eq_bind, Option.bind_some]
        exact hrun₁

/-- **Pruning loses no rejection.** A run the pruned circuit accepts, the
    circuit accepts, with the same outcome. -/
theorem pruned_run_rev (p : Prims) (c : Circuit) (inputs priv pub : List Fr) (o : Outcome)
    (h : (pruned c).run p inputs priv pub = some o) : c.run p inputs priv pub = some o := by
  simp only [Circuit.run] at h ⊢
  have hin : (pruned c).inputs = c.inputs := rfl
  have hout : (pruned c).outputs = c.outputs := rfl
  have hbody : (pruned c).body.toList =
      (pruneList (annotate [] c.body.toList) (c.outputs.flatMap Expr.vars)).kept :=
    pruneDeadBinds_eq c
  rw [hin, hout, hbody] at h
  cases henv : bindInputs (fun _ => 0) c.inputs inputs with
  | none => simp [henv] at h
  | some env =>
      simp only [henv, Option.bind_eq_bind, Option.bind_some] at h ⊢
      cases hrun : execAll p (pruneList (annotate [] c.body.toList) (c.outputs.flatMap Expr.vars)).kept
          { env, priv, pub } with
      | none => simp [hrun] at h
      | some s₂ =>
          simp only [hrun, Option.bind_some] at h
          obtain ⟨e₁', hrun₁, hag⟩ := pruneList_run_rev p (c.outputs.flatMap Expr.vars) [] c.body.toList
            env env priv pub [] s₂ (Bounds.holds_nil env) (fun _ _ => rfl) hrun
          have hgroups : ({ env, priv, pub } : RunState) = { env, priv, pub, groups := [] } := rfl
          rw [hgroups, hrun₁]
          simp only [Option.bind_some]
          have houts : Expr.evalList p e₁' c.outputs = Expr.evalList p s₂.env c.outputs :=
            evalList_congr p c.outputs (by rw [varsList_eq_flatMap]; exact hag)
          rw [houts]
          exact h

/-- **The pruned circuit means exactly the circuit.** For every hash
    functions, inputs and transcripts, the circuit without its unused bindings
    (those that cannot fail) gives what the circuit gives: the same outcome,
    or both reject. -/
theorem pruned_run_eq (p : Prims) (c : Circuit) (inputs priv pub : List Fr) :
    (pruned c).run p inputs priv pub = c.run p inputs priv pub := by
  cases hc : c.run p inputs priv pub with
  | some o => exact pruned_run p c inputs priv pub o hc
  | none =>
      cases hp : (pruned c).run p inputs priv pub with
      | none => rfl
      | some o => rw [pruned_run_rev p c inputs priv pub o hp] at hc; cases hc

end Damp.Emit

namespace Damp
open Damp.IR
open Damp.Zkir (Prims Outcome Preimage)

/-- **The ZKIR means exactly the circuit it is emitted from.** Whatever
    `Emit.circuit c` returns gives, under Midnight's evaluator, what `c` gives
    under the IR semantics, unused bindings included: the same outcome, or both
    reject. -/
theorem Emit.circuit_exact (p : Prims) (c : Circuit) (src : Zkir.IrSource) (h : Emit.circuit c = .ok src)
    (inputs priv pub : List Fr) : src.run p inputs priv pub = c.run p inputs priv pub :=
  (Emit.circuitCore_correct p _ src (Emit.circuit_eq_core _ src h) inputs priv pub).trans
    (Emit.pruned_run_eq p c inputs priv pub)

/-- The shipped circuit (`IR.Circuit.shipped`, the optimized circuit pruned) means
    exactly the optimized circuit. -/
theorem IR.Circuit.shipped_run (p : Prims) (c : Circuit) (inputs priv pub : List Fr) :
    c.shipped.run p inputs priv pub = c.optimize.run p inputs priv pub :=
  Emit.pruned_run_eq p c.optimize inputs priv pub

/-- **`compile_exact`, unpruned.** The ZKIR shipped at the default level means
    exactly the optimized circuit. -/
theorem compile_exact_optimized (p : Prims) (c : Circuit) (src : Zkir.IrSource)
    (h : Emit.circuit c.optimize = .ok src) (inputs priv pub : List Fr) :
    src.run p inputs priv pub = c.optimize.run p inputs priv pub :=
  Emit.circuit_exact p c.optimize src h inputs priv pub

/-- A pass sound for `Circuit.run` is sound for the pruned circuits: what the
    emitter compiles for `f c` and for `c` give the same observable outcome. -/
theorem IR.Pass.SoundRun.pruned {f : Pass} (hf : Pass.SoundRun f) (p : Prims) (c : Circuit)
    (inputs priv pub : List Fr) :
    ((Emit.pruned (f c)).run p inputs priv pub).map Outcome.observable =
      ((Emit.pruned c).run p inputs priv pub).map Outcome.observable := by
  rw [Emit.pruned_run_eq, Emit.pruned_run_eq]; exact hf p c inputs priv pub

/-- The same at one choice of hash functions. -/
theorem IR.Pass.SoundRunFor.pruned {p : Prims} {f : Pass} (hf : Pass.SoundRunFor p f) (c : Circuit)
    (inputs priv pub : List Fr) :
    ((Emit.pruned (f c)).run p inputs priv pub).map Outcome.observable =
      ((Emit.pruned c).run p inputs priv pub).map Outcome.observable := by
  rw [Emit.pruned_run_eq, Emit.pruned_run_eq]; exact hf c inputs priv pub

/-- **What is shipped after a pass sound at `p` accepts what is shipped without
    it.** For `src` the ZKIR emitted for `f c` and `src₀` the ZKIR emitted for
    `c` itself (what `--no-opt` ships), on every inputs, private transcript and
    ledger reads: one accepts exactly when the other does, with the same
    outputs and the same public inputs of the instructions that ran. -/
theorem shipped_sameFor {p : Prims} {f : Pass} (hf : Pass.SoundFor p f) (c : Circuit)
    (src src₀ : Zkir.IrSource) (h : Emit.circuit (f c) = .ok src) (h₀ : Emit.circuit c = .ok src₀)
    (inputs priv pub : List Fr) :
    (src.run p inputs priv pub).map Outcome.observable =
      (src₀.run p inputs priv pub).map Outcome.observable := by
  rw [Emit.circuit_exact p _ src h, Emit.circuit_exact p _ src₀ h₀]
  exact hf.run c inputs priv pub

/-- `shipped_sameFor` for a pass sound for every hash functions. -/
theorem shipped_same {f : Pass} (hf : Pass.Sound f) (p : Prims) (c : Circuit)
    (src src₀ : Zkir.IrSource) (h : Emit.circuit (f c) = .ok src) (h₀ : Emit.circuit c = .ok src₀)
    (inputs priv pub : List Fr) :
    (src.run p inputs priv pub).map Outcome.observable =
      (src₀.run p inputs priv pub).map Outcome.observable :=
  shipped_sameFor (hf.soundFor p) c src src₀ h h₀ inputs priv pub

/-- Every ZKIR the emitter returns asks for the communications commitment
    (`IrSource.commCommitment` keeps its default). -/
theorem Emit.circuitCore_commCommitment (c : Circuit) (src : Zkir.IrSource) (h : Emit.circuitCore c = .ok src) :
    src.commCommitment = true := by
  unfold Emit.circuitCore at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · cases h; rfl

theorem Emit.circuit_commCommitment (c : Circuit) (src : Zkir.IrSource) (h : Emit.circuit c = .ok src) :
    src.commCommitment = true :=
  Emit.circuitCore_commCommitment _ src (Emit.circuit_eq_core c src h)

/-- `preprocess` looks at a run only through what `observable` keeps. -/
theorem preprocess_congr (p : Prims) (src src₀ : Zkir.IrSource) (pre : Preimage)
    (h : (src.run p pre.inputs pre.privateTranscript pre.publicTranscriptOutputs).map Outcome.observable =
      (src₀.run p pre.inputs pre.privateTranscript pre.publicTranscriptOutputs).map Outcome.observable)
    (hc : src.commCommitment = src₀.commCommitment) :
    (src.preprocess p pre).map Outcome.observable = (src₀.preprocess p pre).map Outcome.observable := by
  simp only [Zkir.IrSource.preprocess, hc]
  cases h₁ : src.run p pre.inputs pre.privateTranscript pre.publicTranscriptOutputs with
  | none =>
      rw [h₁] at h
      cases h₂ : src₀.run p pre.inputs pre.privateTranscript pre.publicTranscriptOutputs with
      | none => rfl
      | some o₀ => rw [h₂] at h; cases h
  | some o =>
      rw [h₁] at h
      cases h₂ : src₀.run p pre.inputs pre.privateTranscript pre.publicTranscriptOutputs with
      | none => rw [h₂] at h; cases h
      | some o₀ =>
          rw [h₂] at h
          simp only [Option.map_some, Option.some.injEq, Outcome.observable, Prod.mk.injEq] at h
          obtain ⟨hout, hact⟩ := h
          simp only [Option.bind_eq_bind, Option.bind_some]
          rw [hact]
          split
          · rfl
          · simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_some]
            split
            · split
              · rw [hout]; split <;> simp [Outcome.observable, hout, hact]
              · rfl
            · simp [Outcome.observable, hout, hact]

/-- **The checker accepts the same proof data.** For `src` the ZKIR shipped for
    `f c` and `src₀` the ZKIR shipped for `c` without optimization, Midnight's
    `preprocess` (what the proof server runs on a preimage: inputs, private
    transcript, ledger reads, the claimed public inputs and the commitment)
    accepts a preimage for one exactly when for the other, with the same
    outputs and active public inputs. -/
theorem shipped_preprocessFor {p : Prims} {f : Pass} (hf : Pass.SoundFor p f) (c : Circuit)
    (src src₀ : Zkir.IrSource) (h : Emit.circuit (f c) = .ok src) (h₀ : Emit.circuit c = .ok src₀)
    (pre : Preimage) :
    (src.preprocess p pre).map Outcome.observable = (src₀.preprocess p pre).map Outcome.observable :=
  preprocess_congr p src src₀ pre (shipped_sameFor hf c src src₀ h h₀ _ _ _)
    ((Emit.circuit_commCommitment _ src h).trans (Emit.circuit_commCommitment _ src₀ h₀).symm)

/-- The default level: the shipped ZKIR accepts exactly the proof data the
    unoptimized ZKIR accepts, whatever the hash functions. -/
theorem shipped_optimize_preprocess (p : Prims) (c : Circuit) (src src₀ : Zkir.IrSource)
    (h : Emit.circuit c.optimize = .ok src) (h₀ : Emit.circuit c = .ok src₀) (pre : Preimage) :
    (src.preprocess p pre).map Outcome.observable = (src₀.preprocess p pre).map Outcome.observable :=
  shipped_preprocessFor (Circuit.optimize_sound.soundFor p) c src src₀ h h₀ pre

/-- `--O2`: the same. -/
theorem shipped_optimizeFull_preprocess (p : Prims) (c : Circuit) (src src₀ : Zkir.IrSource)
    (h : Emit.circuit c.optimizeFull = .ok src) (h₀ : Emit.circuit c = .ok src₀) (pre : Preimage) :
    (src.preprocess p pre).map Outcome.observable = (src₀.preprocess p pre).map Outcome.observable :=
  shipped_preprocessFor (Circuit.optimizeFull_sound.soundFor p) c src src₀ h h₀ pre

/-- `--O3`: the same, for runs with `Crypto.prims`. -/
theorem shipped_optimizeMax_preprocess (c : Circuit) (src src₀ : Zkir.IrSource)
    (h : Emit.circuit c.optimizeMax = .ok src) (h₀ : Emit.circuit c = .ok src₀) (pre : Preimage) :
    (src.preprocess Crypto.prims pre).map Outcome.observable =
      (src₀.preprocess Crypto.prims pre).map Outcome.observable :=
  shipped_preprocessFor Circuit.optimizeMax_soundFor c src src₀ h h₀ pre

end Damp
