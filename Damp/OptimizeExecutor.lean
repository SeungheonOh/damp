/-
The optimizer does not change what the executor does.

`Circuit.optimize_correct` (`Damp/OptimizeCorrect.lean`) is about what the
circuit accepts. The executor (`Damp/Executor.lean`) runs the optimized
circuit, and does things the circuit semantics does not see: it asks the
witnesses, with evaluated arguments, and sends instructions to the ledger,
with operands evaluated before the reads are bound. This file proves that the
executor running the optimized circuit completes exactly when it would on the
original, asks its oracles the same questions, and leaves the same observable
result (`Exec.optimize_correct`, `Exec.optimize_asks_same`).

The expression-level facts of `Damp/OptimizeCorrect.lean` (rewriting under
`Facts`, `Facts.Holds` and its maintenance) are reused as they are. Statements
that do not talk to an oracle (`bind`, `assert`, `constrain`) run in the
executor exactly as in the semantics, so their soundness is taken from
`Stmt.optimize_sound`; witness calls and ledger statements are redone here.
-/
import Damp.Executor
import Damp.OptimizeCorrect

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Damp.Exec
open Damp.IR
open Damp.Zkir (Prims Group)

variable {ω σ : Type}

/-- What a completed call leaves that anyone can observe: the outputs, both
    transcripts, the public inputs of the instructions that ran, and the
    private and ledger states afterwards. -/
def Result.observable (r : Exec.Result ω σ) : List Fr × List Fr × List Fr × List Fr × ω × σ :=
  (r.outputs, r.priv, r.pub, (r.groups.filter (·.active)).flatMap (·.vals), r.private_, r.ledger)

/-! ## Rewriting the instructions sent to the ledger -/

section MapM
variable {α β γ : Type} (g : α → β) (h : β → Option γ) (k : α → Option γ) (hk : ∀ a, h (g a) = k a)
include hk

/-- Evaluating a mapped list is evaluating the original with the map folded in. -/
theorem list_mapM_map (xs : List α) : (xs.map g).mapM h = xs.mapM k := by
  rw [List.mapM_map]; congr 1; funext a; exact hk a

/-- `list_mapM_map` for an aligned value. -/
theorem Aligned.mapM_map (v : Impact.Aligned α) :
    (Id.run (v.mapM (m := Id) fun a => pure (g a))).mapM h = v.mapM k := by
  simp [Impact.Aligned.mapM, List.mapM_pure, list_mapM_map g h k hk]

mutual
/-- `list_mapM_map` for a state value. -/
theorem StateLit.mapM_map : ∀ v : Impact.StateLit α,
    (Id.run (v.mapM (m := Id) fun a => pure (g a))).mapM h = v.mapM k
  | .null => by simp [Impact.StateLit.mapM]
  | .cell v => by
      have := Aligned.mapM_map g h k hk v
      simp [Impact.StateLit.mapM] at this ⊢
      rw [this]
  | .emptyMap => by simp [Impact.StateLit.mapM]
  | .array es => by
      have := StateLit.mapMList_map es
      simp [Impact.StateLit.mapM] at this ⊢
      rw [this]
  | .emptyMerkleTree d => by simp [Impact.StateLit.mapM]
/-- `list_mapM_map` for a list of state values. -/
theorem StateLit.mapMList_map : ∀ es : List (Impact.StateLit α),
    Impact.StateLit.mapMList h (Id.run (Impact.StateLit.mapMList (m := Id) (fun a => pure (g a)) es)) =
      Impact.StateLit.mapMList k es
  | [] => by simp [Impact.StateLit.mapMList]
  | e :: es => by
      have h1 := StateLit.mapM_map e
      have h2 := StateLit.mapMList_map es
      simp [Impact.StateLit.mapMList] at h1 h2 ⊢
      rw [h1, h2]
end

/-- `list_mapM_map` for an instruction. -/
theorem Op.mapM_map (op : Impact.Op α) : (op.map g).mapM h = op.mapM k := by
  cases op <;> simp [Impact.Op.map, Impact.Op.mapM, List.mapM_pure, hk, list_mapM_map g h k hk]
  case push v => rw [Aligned.mapM_map g h k hk v]
  case idx path =>
    have : ((fun x => Impact.Aligned.mapM h x) ∘
        fun x => Id.run (Impact.Aligned.mapM (m := Id) (fun a => pure (g a)) x))
        = fun x => Impact.Aligned.mapM k x := funext (Aligned.mapM_map g h k hk)
    rw [this]
  case idxStack pre =>
    have : ((fun x => Impact.Aligned.mapM h x) ∘
        fun x => Id.run (Impact.Aligned.mapM (m := Id) (fun a => pure (g a)) x))
        = fun x => Impact.Aligned.mapM k x := funext (Aligned.mapM_map g h k hk)
    rw [this]
  case pushState v => rw [StateLit.mapM_map g h k hk v]

end MapM

/-- The instructions sent to the ledger, rewritten under facts that hold, are
    the ones the original sends, and fail to evaluate together. -/
theorem request_rw (p : Prims) {f : Facts} {env env' : Env} (h : f.Holds p env env') :
    ∀ ops : List (Impact.Op Expr), request p env' (ops.map (·.map f.rw)) = request p env ops
  | [] => rfl
  | op :: ops => by
      simp only [List.map_cons, request]
      rw [Op.mapM_map f.rw (Expr.eval p env') (Expr.eval p env) (Facts.rw_eval p h) op,
        request_rw p h ops]

/-! ## Assigning values -/

/-- Assigning the same values in two environments: both fail, or afterwards
    they agree on the variables assigned and are unchanged elsewhere. -/
theorem assign_pair : ∀ (outs : List (Var × Option Range)) (env env' : Env) (vals : List Fr),
    OptRel (fun a b => (∀ w ∈ outs.map (·.1), a w = b w) ∧
        (∀ w, w ∉ outs.map (·.1) → a w = env w ∧ b w = env' w))
      (assign env outs vals) (assign env' outs vals)
  | [], env, env', [] => by simp [assign, OptRel]
  | [], _, _, _ :: _ => by simp [assign, OptRel]
  | _ :: _, _, _, [] => by simp [assign, OptRel]
  | (v, rg) :: outs, env, env', x :: xs => by
      have step : OptRel (fun a b => (∀ w ∈ ((v, rg) :: outs).map (·.1), a w = b w) ∧
          (∀ w, w ∉ ((v, rg) :: outs).map (·.1) → a w = env w ∧ b w = env' w))
          (assign (env.set v x) outs xs) (assign (env'.set v x) outs xs) := by
        refine (assign_pair outs (env.set v x) (env'.set v x) xs).mono ?_
        intro a b ⟨hin, hout⟩
        refine ⟨?_, ?_⟩
        · intro w hw
          by_cases hwo : w ∈ outs.map (·.1)
          · exact hin w hwo
          · have := hout w hwo
            simp only [Env.set] at this
            have hwv : w = v := by
              simp at hw hwo
              rcases hw with h | ⟨y, hy⟩
              · exact h
              · exact absurd hy (hwo y)
            subst hwv; simp at this; rw [this.1, this.2]
        · intro w hw
          simp only [List.map_cons, List.mem_cons, not_or] at hw
          have := hout w hw.2
          simp only [Env.set, hw.1, ite_false] at this
          exact this
      cases rg with
      | none => simpa only [assign] using step
      | some r =>
          simp only [assign]
          split
          · exact step
          · simp [OptRel]

/-- Values the executor assigned are what the semantics reads from a stream
    that holds them. -/
theorem assign_readAll' :
    ∀ (outs : List (Var × Option Range)) (env : Env) (vals : List Fr) (r : Env),
      assign env outs vals = some r → readAll true env outs vals = some (r, [])
  | [], env, [], r, h => by
      simp only [assign, Option.some.injEq] at h
      simp [readAll, h]
  | [], _, _ :: _, _, h => by simp [assign] at h
  | _ :: _, _, [], _, h => by simp [assign] at h
  | (v, rg) :: rest, env, x :: xs, r, h => by
      simp only [assign] at h
      simp only [readAll, Zkir.readOne, ite_true, Option.bind_eq_bind, Option.bind_some]
      cases rg with
      | none =>
          simp only at h
          simp only [Option.pure_def, Option.bind_some]
          exact assign_readAll' rest _ xs r h
      | some rg =>
          simp only at h
          by_cases hh : rg.holds x
          · simp only [hh, ite_true] at h
            simp only [hh, ite_true, Option.pure_def, Option.bind_some]
            exact assign_readAll' rest _ xs r h
          · simp [hh] at h

/-- Assigning zeros succeeds when zero passes every range check, and sets the
    variables to zero. -/
theorem assign_zeros : ∀ (outs : List (Var × Option Range)) (env : Env),
    (outs.all fun (_, r) => r.all (Range.holds 0)) = true →
    ∃ r, assign env outs (outs.map fun _ => 0) = some r ∧ (∀ w ∈ outs.map (·.1), r w = 0) ∧
      (∀ w, w ∉ outs.map (·.1) → r w = env w)
  | [], env, _ => ⟨env, rfl, by simp, fun _ _ => rfl⟩
  | (v, rg) :: outs, env, h => by
      simp only [List.all_cons, Bool.and_eq_true] at h
      obtain ⟨r, hr, hin, hout⟩ := assign_zeros outs (env.set v 0) h.2
      refine ⟨r, ?_, ?_, ?_⟩
      · cases rg with
        | none => simpa [assign] using hr
        | some rg =>
            simp only [Option.all_some] at h
            simp [assign, h.1, hr]
      · intro w hw
        by_cases hwo : w ∈ outs.map (·.1)
        · exact hin w hwo
        · have hwv : w = v := by
            simp at hw hwo
            rcases hw with h | ⟨y, hy⟩
            · exact h
            · exact absurd hy (hwo y)
          rw [hout w hwo, hwv]; simp [Env.set]
      · intro w hw
        simp only [List.map_cons, List.mem_cons, not_or] at hw
        rw [hout w hw.2]; simp [Env.set, hw.1]

/-! ## Executor states -/

section Stmts
variable (p : Prims) (O : Oracles ω σ)

/-- The original executor state `s` and the optimized one `s'` correspond under
    the facts `f`: the facts hold of their environments, they have recorded the
    same transcripts and the same public inputs of instructions that ran, and
    the private and ledger states are the same. -/
structure ExecRel (f : Facts) (s s' : State ω σ) : Prop where
  facts : f.Holds p s.env s'.env
  priv : s'.priv = s.priv
  pub : s'.pub = s.pub
  groups : s'.groups.filter (·.active) = s.groups.filter (·.active)
  private_ : s'.private_ = s.private_
  ledger : s'.ledger = s.ledger

/-- Running one statement as a list. -/
theorem steps_single (st : Stmt) (s : State ω σ) : steps p O [st] s = step p O s st := by
  simp only [steps, Option.bind_eq_bind]
  cases step p O s st <;> rfl

/-- Running two lists of statements is running one after the other. -/
theorem steps_append : ∀ (a b : List Stmt) (s : State ω σ),
    steps p O (a ++ b) s = (steps p O a s).bind (steps p O b)
  | [], _, _ => rfl
  | st :: a, b, s => by
      simp only [List.cons_append, steps, Option.bind_eq_bind]
      cases step p O s st with
      | none => rfl
      | some s' => simp only [Option.bind_some]; exact steps_append a b s'

/-! ### Statements that ask no oracle -/

/-- A statement that asks no oracle: `bind`, `assert` or `constrain`. -/
def Stmt.isLocal : Stmt → Bool
  | .bind .. | .assert .. | .constrain .. => true
  | _ => false

/-- The environment of an executor state, as a run state with nothing recorded. -/
def State.toRun (s : State ω σ) : RunState := { env := s.env, priv := [], pub := [] }

/-- The executor runs a statement that asks no oracle as the semantics does. -/
theorem step_local {st : Stmt} (hl : Stmt.isLocal st = true) (s : State ω σ) :
    step p O s st = (st.exec p s.toRun).map fun r => { s with env := r.env } := by
  cases st with
  | bind v _ e =>
      simp only [step, Stmt.exec, State.toRun, Option.bind_eq_bind, Option.pure_def]
      cases e.eval p s.env <;> rfl
  | assert c _ =>
      simp only [step, Stmt.exec, State.toRun, Option.bind_eq_bind, Option.pure_def]
      cases c.eval p s.env with
      | none => rfl
      | some x =>
          simp only [Option.bind_some]
          cases asBool x with
          | none => rfl
          | some b => cases b <;> rfl
  | constrain e r =>
      simp only [step, Stmt.exec, State.toRun, Option.bind_eq_bind, Option.pure_def]
      cases e.eval p s.env with
      | none => rfl
      | some x =>
          simp only [Option.bind_some]
          split <;> rfl
  | witness => cases hl
  | ledger => cases hl

/-- A statement that asks no oracle records nothing in a run state. -/
theorem exec_local {st : Stmt} (hl : Stmt.isLocal st = true) {r0 r : RunState}
    (h : st.exec p r0 = some r) : r = { r0 with env := r.env } := by
  cases st with
  | bind v _ e =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨x, _, rfl⟩ := h; rfl
  | assert c _ =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨x, _, b, _, hb⟩ := h
      cases b <;> simp_all
  | constrain e rg =>
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨x, _, hb⟩ := h
      split at hb <;> simp_all
  | witness => cases hl
  | ledger => cases hl

/-- The executor runs statements that ask no oracle as the semantics does. -/
theorem steps_local : ∀ (out : List Stmt), (∀ st ∈ out, Stmt.isLocal st = true) → ∀ (s : State ω σ),
    steps p O out s = (execAll p out s.toRun).map fun r => { s with env := r.env }
  | [], _, s => rfl
  | st :: rest, hl, s => by
      simp only [steps, execAll, Option.bind_eq_bind]
      rw [step_local p O (hl st (by simp)) s]
      cases h : st.exec p s.toRun with
      | none => rfl
      | some r =>
          simp only [Option.map_some, Option.bind_some]
          rw [steps_local rest (fun x hx => hl x (by simp [hx])) _]
          have hr := exec_local p (hl st (by simp)) h
          have : ({ s with env := r.env } : State ω σ).toRun = r := by
            rw [hr]; rfl
          rw [this]

/-- A statement that asks no oracle is optimized into such statements. -/
theorem optimize_local {f f' : Facts} {st : Stmt} {out : List Stmt} (hl : Stmt.isLocal st = true)
    (ho : st.optimize f = some (out, f')) : ∀ x ∈ out, Stmt.isLocal x = true := by
  cases st with
  | bind v hint e =>
      simp only [Stmt.optimize] at ho
      split at ho
      · simp only [Option.some.injEq, Prod.mk.injEq] at ho; obtain ⟨rfl, -⟩ := ho; simp
      · simp only [Option.some.injEq, Prod.mk.injEq] at ho; obtain ⟨rfl, -⟩ := ho; simp
      · split at ho
        · cases ho
        · simp only [Option.some.injEq, Prod.mk.injEq] at ho; obtain ⟨rfl, -⟩ := ho
          simp [Stmt.isLocal]
  | assert c msg =>
      simp only [Stmt.optimize] at ho
      split at ho
      · simp only [Option.some.injEq, Prod.mk.injEq] at ho; obtain ⟨rfl, -⟩ := ho; simp
      · simp only [Option.some.injEq, Prod.mk.injEq] at ho; obtain ⟨rfl, -⟩ := ho
        simp [Stmt.isLocal]
  | constrain e r =>
      simp only [Stmt.optimize] at ho
      split at ho
      · simp only [Option.some.injEq, Prod.mk.injEq] at ho; obtain ⟨rfl, -⟩ := ho; simp
      · simp only [Option.some.injEq, Prod.mk.injEq] at ho; obtain ⟨rfl, -⟩ := ho
        simp [Stmt.isLocal]
  | witness => cases hl
  | ledger => cases hl

/-- A statement that asks no oracle is optimized soundly for the executor: this
    is `Stmt.optimize_sound`, since the executor runs it as the semantics does. -/
theorem optimize_local_exec {f f' : Facts} {st : Stmt} {out : List Stmt} (hl : Stmt.isLocal st = true)
    (ho : st.optimize f = some (out, f')) {s s' : State ω σ} (hr : ExecRel p f s s') :
    OptRel (ExecRel p f') (step p O s st) (steps p O out s') := by
  have hs := Stmt.optimize_sound p ho (s := s.toRun) (s' := s'.toRun) ⟨hr.facts, rfl, rfl, rfl⟩
  rw [step_local p O hl, steps_local p O out (optimize_local hl ho)]
  revert hs
  cases st.exec p s.toRun <;> cases execAll p out s'.toRun <;> simp only [OptRel, Option.map_none,
    Option.map_some, imp_self, false_implies]
  intro hs
  exact ⟨hs.facts, hr.priv, hr.pub, hr.groups, hr.private_, hr.ledger⟩

/-! ### Witness calls -/

/-- `witness` is optimized soundly for the executor: it is asked the same
    question with the same arguments, or, when its guard is the constant 0 and
    it was dropped, not asked on either side. -/
theorem optimize_witness_exec {f f' : Facts} {guard : Expr} {name : String} {args : List Expr}
    {outs : List (Var × Option Range)} {shape : Shape} {out : List Stmt}
    (ho : (Stmt.witness guard name args outs shape).optimize f = some (out, f')) {s s' : State ω σ}
    (hr : ExecRel p f s s') :
    OptRel (ExecRel p f') (step p O s (.witness guard name args outs shape)) (steps p O out s') := by
  have hrw := Facts.rw_eval p hr.facts guard
  simp only [Stmt.optimize] at ho
  split at ho
  · next hskip =>
    simp only [Option.some.injEq, Prod.mk.injEq] at ho
    obtain ⟨rfl, rfl⟩ := ho
    unfold witnessSkipped at hskip
    split at hskip
    · next c hc =>
      rw [hc] at hrw
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hskip
      obtain ⟨h0, hall⟩ := hskip
      simp only [step, ← hrw, Expr.eval, h0, Option.bind_eq_bind, Option.bind_some, steps]
      by_cases he : outs.isEmpty
      · have : outs = [] := List.isEmpty_iff.mp he
        subst this
        simp only [List.isEmpty_nil, ite_true, Fr.zero_ne_one, ite_false, OptRel, List.map_nil,
          List.nil_append]
        exact hr
      · obtain ⟨r, hrd, hin, hout⟩ := assign_zeros outs s.env hall
        simp only [he, Bool.false_eq_true, ite_false, asBool_zero, Option.bind_some, hrd,
          Option.pure_def, OptRel]
        exact ⟨⟨hr.facts.known.zeros p _ hin hout, hr.facts.bools, hr.facts.checked⟩, hr.priv,
          hr.pub, hr.groups, hr.private_, hr.ledger⟩
    · cases hskip
  · split at ho
    · cases ho
    · next hc =>
      simp only [Option.some.injEq, Prod.mk.injEq] at ho
      obtain ⟨rfl, rfl⟩ := ho
      rw [steps_single]
      have hargs := Facts.rw_evalList p hr.facts args
      simp only [step, Option.bind_eq_bind, hrw, hargs, hr.private_]
      cases guard.eval p s.env with
      | none => simp [OptRel]
      | some gx =>
        simp only [Option.bind_some]
        by_cases he : outs.isEmpty
        · have : outs = [] := List.isEmpty_iff.mp he
          subst this
          have hf := Facts.forget_holds p hr.facts (Bool.eq_false_iff.mpr hc) (r := s.env)
              (r' := s'.env) (by simp) (fun w _ => ⟨rfl, rfl⟩)
          simp only [List.isEmpty_nil, ite_true]
          split
          · cases Expr.evalList p s.env args with
            | none => simp [OptRel]
            | some av =>
              simp only [Option.bind_some]
              cases O.witness name av s.private_ with
              | none => simp [OptRel]
              | some res =>
                obtain ⟨vals, pv⟩ := res
                simp only [Option.bind_some]
                split
                · simp only [Option.pure_def, OptRel]
                  exact ⟨by simpa [witnessChecks, witnessBools] using hf, hr.priv, hr.pub, hr.groups,
                    rfl, hr.ledger⟩
                · simp [OptRel]
          · simp only [Option.pure_def, OptRel]
            exact ⟨by simpa [witnessChecks, witnessBools] using hf, hr.priv, hr.pub, hr.groups,
              hr.private_, hr.ledger⟩
        · simp only [he, Bool.false_eq_true, ite_false]
          cases asBool gx with
          | none => simp [OptRel]
          | some act =>
            simp only [Option.bind_some]
            -- Both sides assign the same values: the oracle's answer, or zeros.
            have key : ∀ (vals : List Fr) (pv : ω) (pv' : ω), pv' = pv →
                OptRel (ExecRel p { f.forget (outs.map (·.1)) with
                    checked := witnessChecks outs ++ (f.forget (outs.map (·.1))).checked,
                    bools := witnessBools outs ++ (f.forget (outs.map (·.1))).bools })
                  ((assign s.env outs vals).bind fun env => pure
                    ({ s with env, private_ := pv, priv := (if act then s.priv ++ vals else s.priv) }))
                  ((assign s'.env outs vals).bind fun env => pure
                    ({ s' with env, private_ := pv', priv := (if act then s'.priv ++ vals else s'.priv) })) := by
              intro vals pv pv' hpv
              have hp := assign_pair outs s.env s'.env vals
              cases h1 : assign s.env outs vals with
              | none =>
                rw [h1] at hp
                cases h2 : assign s'.env outs vals with
                | none => simp [OptRel]
                | some b => rw [h2] at hp; simp [OptRel] at hp
              | some r =>
                rw [h1] at hp
                cases h2 : assign s'.env outs vals with
                | none => rw [h2] at hp; simp [OptRel] at hp
                | some r' =>
                  rw [h2] at hp
                  simp only [OptRel] at hp
                  obtain ⟨hin, hout⟩ := hp
                  have hrd := assign_readAll' outs s.env vals r h1
                  simp only [Option.bind_some, Option.pure_def, OptRel]
                  refine ⟨?_, by rw [hr.priv], hr.pub, hr.groups, hpv, hr.ledger⟩
                  exact (Facts.forget_holds p hr.facts (Bool.eq_false_iff.mpr hc) hin hout).extend p
                    (witnessChecks_holds p hrd hin) (witnessBools_holds hrd hin)
            cases act
            · simpa using key (outs.map fun _ => 0) s.private_ s.private_ rfl
            · simp only [ite_true]
              cases Expr.evalList p s.env args with
              | none => simp [OptRel]
              | some av =>
                simp only [Option.bind_some]
                cases O.witness name av s.private_ with
                | none => simp [OptRel]
                | some res =>
                  obtain ⟨vals, pv⟩ := res
                  simpa using key vals pv pv rfl

/-! ### Ledger statements -/

/-- The variables a ledger statement reads, set to zero, as the executor sets them. -/
theorem reads_zeros (reads : List Var) :
    (reads.map fun v => ((v, (none : Option Range)))).map (fun _ => (0 : Fr)) = reads.map fun _ => 0 := by
  simp [List.map_map, Function.comp_def]

/-- Facts that hold before a ledger statement still hold, there, once the
    reads are forgotten, provided the pass knows no value for a read variable:
    then the read variables have the same value on both sides. -/
theorem Facts.forget_holds_before {f : Facts} {env env' : Env} {reads : List Var}
    (h : f.Holds p env env') (hc : f.clash reads = false) (hk : f.knows reads = false) :
    (f.forget reads).Holds p env env' := by
  refine Facts.forget_holds p h hc ?_ (fun _ _ => ⟨rfl, rfl⟩)
  intro w hw
  have hl : f.known.lookup w = none := by
    simp only [Facts.knows, List.any_eq_false] at hk
    have := hk w hw
    cases hl : f.known.lookup w
    · rfl
    · simp [hl] at this
  have := h.known w
  rw [subst_var_of_lookup_none hl] at this
  simpa [Expr.eval] using this.symm

/-- `ledger` is optimized soundly for the executor: the same instructions are
    sent to the ledger, or, when its guard is the constant 0 and it was dropped,
    nothing is sent on either side. -/
theorem optimize_ledger_exec {f f' : Facts} {guard : Expr} {reads : List Var}
    {ops : List (Impact.Op Expr)} {out : List Stmt}
    (ho : (Stmt.ledger guard reads ops).optimize f = some (out, f')) {s s' : State ω σ}
    (hr : ExecRel p f s s') :
    OptRel (ExecRel p f') (step p O s (.ledger guard reads ops)) (steps p O out s') := by
  have hrw := Facts.rw_eval p hr.facts guard
  simp only [Stmt.optimize] at ho
  split at ho
  · next hskip =>
    simp only [Option.some.injEq, Prod.mk.injEq] at ho
    obtain ⟨rfl, rfl⟩ := ho
    unfold ledgerSkipped at hskip
    split at hskip
    · next c hc =>
      rw [hc] at hrw
      simp only [step, ← hrw, Expr.eval, Option.bind_eq_bind, Option.bind_some, steps]
      by_cases he : (reads.isEmpty && ops.isEmpty) = true
      · simp only [Bool.and_eq_true] at he
        have : reads = [] := List.isEmpty_iff.mp he.1
        subst this
        simp only [List.isEmpty_nil, he.2, Bool.and_self, ite_true, OptRel, List.map_nil,
          List.nil_append]
        exact hr
      · have he' : (reads.isEmpty && ops.isEmpty) = false := by simpa using he
        simp only [List.isEmpty_map, he', Bool.false_or, Bool.and_eq_true, decide_eq_true_eq,
          List.all_eq_true] at hskip
        obtain ⟨h0, htot⟩ := hskip
        obtain ⟨r, hrd, hin, hout⟩ := assign_zeros (reads.map fun v => (v, none)) s.env (by simp)
        rw [reads_vars] at hin hout
        rw [reads_zeros] at hrd
        have hf0 : Facts.Holds p { f with known := reads.map (fun v => (v, Expr.const 0)) ++ f.known }
            r s'.env := ⟨hr.facts.known.zeros p reads hin hout, hr.facts.bools, hr.facts.checked⟩
        obtain ⟨gs, hgs, hgf⟩ := ledgerGroups_inactive p r ops (by
          intro op hop
          have := htot (op.map _) (List.mem_map_of_mem hop)
          obtain ⟨ys, hys⟩ := Expr.totalList_eval p s'.env _ hr.facts.bools _ this
          refine ⟨ys, ?_⟩
          simp only [opOperands] at hys
          rw [Op.encode_map _ (Facts.rw_const _), Facts.rw_evalList p hf0] at hys
          exact hys)
        simp only [he', Bool.false_eq_true, ite_false, h0, asBool_zero, Option.bind_some, hrd,
          hgs, Option.pure_def, OptRel]
        refine ⟨hf0, hr.priv, hr.pub, ?_, hr.private_, hr.ledger⟩
        simp [List.filter_append, hgf, hr.groups]
    · cases hskip
  · split at ho
    · cases ho
    · next hc =>
      split at ho
      · cases ho
      · next hk =>
        simp only [Option.some.injEq, Prod.mk.injEq] at ho
        obtain ⟨rfl, rfl⟩ := ho
        rw [steps_single]
        have hc' := Bool.eq_false_iff.mpr hc
        have hk' := Bool.eq_false_iff.mpr hk
        have hreq := request_rw p (Facts.forget_holds_before p hr.facts hc' hk') ops
        simp only [step, Option.bind_eq_bind, hrw, List.isEmpty_map, hreq, hr.ledger]
        cases guard.eval p s.env with
        | none => simp [OptRel]
        | some gx =>
          simp only [Option.bind_some]
          split
          · next he =>
            simp only [Bool.and_eq_true] at he
            have : reads = [] := List.isEmpty_iff.mp he.1
            subst this
            simp only [OptRel]
            exact ⟨Facts.forget_holds p hr.facts hc' (r := s.env) (r' := s'.env)
              (by simp) (fun w _ => ⟨rfl, rfl⟩), hr.priv, hr.pub, hr.groups, hr.private_, hr.ledger⟩
          · cases asBool gx with
            | none => simp [OptRel]
            | some act =>
              simp only [Option.bind_some]
              -- Both sides assign the same values to the reads: the ledger's answer, or zeros.
              have key : ∀ (vals : List Fr) (l : σ),
                  OptRel (ExecRel p (f.forget reads))
                    ((assign s.env (reads.map fun v => (v, none)) vals).bind fun env =>
                      (ledgerGroups p env act ops).bind fun groups => pure
                        ({ s with env, ledger := l, pub := (if act then s.pub ++ vals else s.pub), groups := s.groups ++ groups }))
                    ((assign s'.env (reads.map fun v => (v, none)) vals).bind fun env =>
                      (ledgerGroups p env act (ops.map (·.map (f.forget reads).rw))).bind fun groups =>
                        pure ({ s' with env, ledger := l, pub := (if act then s'.pub ++ vals else s'.pub), groups := s'.groups ++ groups })) := by
                intro vals l
                have hp := assign_pair (reads.map fun v => (v, none)) s.env s'.env vals
                cases h1 : assign s.env (reads.map fun v => (v, none)) vals with
                | none =>
                  rw [h1] at hp
                  cases h2 : assign s'.env (reads.map fun v => (v, none)) vals with
                  | none => simp [OptRel]
                  | some b => rw [h2] at hp; simp [OptRel] at hp
                | some r =>
                  rw [h1] at hp
                  cases h2 : assign s'.env (reads.map fun v => (v, none)) vals with
                  | none => rw [h2] at hp; simp [OptRel] at hp
                  | some r' =>
                    rw [h2] at hp
                    simp only [OptRel] at hp
                    obtain ⟨hin, hout⟩ := hp
                    rw [reads_vars] at hin hout
                    have hf := Facts.forget_holds p hr.facts hc' hin hout
                    simp only [Option.bind_some, ledgerGroups_rw p hf]
                    cases ledgerGroups p r act ops with
                    | none => simp [OptRel]
                    | some gs =>
                      simp only [Option.bind_some, Option.pure_def, OptRel]
                      refine ⟨hf, hr.priv, by rw [hr.pub], ?_, hr.private_, rfl⟩
                      simp [List.filter_append, hr.groups]
              cases act
              · simpa [reads_zeros] using key (reads.map fun _ => 0) s.ledger
              · simp only [ite_true]
                cases request p s.env ops with
                | none => simp [OptRel]
                | some req =>
                  simp only [Option.bind_some]
                  cases O.ledger req s.ledger with
                  | none => simp [OptRel]
                  | some res =>
                    obtain ⟨vals, l⟩ := res
                    simpa using key vals l

/-! ### Statement lists -/

/-- Every statement is optimized soundly for the executor. -/
theorem Stmt.optimize_exec {f f' : Facts} {stmt : Stmt} {out : List Stmt}
    (ho : stmt.optimize f = some (out, f')) {s s' : State ω σ} (hr : ExecRel p f s s') :
    OptRel (ExecRel p f') (step p O s stmt) (steps p O out s') := by
  cases stmt with
  | bind => exact optimize_local_exec p O rfl ho hr
  | assert => exact optimize_local_exec p O rfl ho hr
  | constrain => exact optimize_local_exec p O rfl ho hr
  | witness => exact optimize_witness_exec p O ho hr
  | ledger => exact optimize_ledger_exec p O ho hr

/-- A list of statements is optimized soundly for the executor. -/
theorem Stmt.optimizeAll_exec : ∀ {f f' : Facts} {stmts out : List Stmt},
    Stmt.optimizeAll f stmts = some (out, f') → ∀ {s s' : State ω σ}, ExecRel p f s s' →
    OptRel (ExecRel p f') (steps p O stmts s) (steps p O out s')
  | f, f', [], out, ho, s, s', hr => by
      simp only [Stmt.optimizeAll, Option.some.injEq, Prod.mk.injEq] at ho
      obtain ⟨rfl, rfl⟩ := ho
      exact hr
  | f, f', st :: rest, out, ho, s, s', hr => by
      simp only [Stmt.optimizeAll, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at ho
      obtain ⟨⟨a, f1⟩, h1, ⟨b, f2⟩, h2, hab⟩ := ho
      simp only [Prod.mk.injEq] at hab
      obtain ⟨rfl, rfl⟩ := hab
      have hs := Stmt.optimize_exec p O h1 hr
      simp only [steps, steps_append, Option.bind_eq_bind]
      revert hs
      cases step p O s st <;> cases steps p O a s' <;> simp only [OptRel, Option.bind_none,
        Option.bind_some, imp_self, false_implies]
      intro hs
      exact Stmt.optimizeAll_exec h2 hs

end Stmts

/-! ## Circuits -/

/-- Optimizing a circuit does not change what the executor does with it: run
    on the optimized circuit, it completes exactly when it would on the
    original, and leaves the same outputs, transcripts, public inputs of the
    instructions that ran, private state and ledger state. This holds for
    every witness and ledger oracle, so the oracles are asked the same
    questions (see `optimize_asks_same`). -/
theorem optimize_correct (p : Prims) (O : Oracles ω σ) (c : Circuit)
    (inputs : List Fr) (private_ : ω) (ledger : σ) :
    (run p O c.optimize inputs private_ ledger).map Result.observable
      = (run p O c inputs private_ ledger).map Result.observable := by
  unfold Circuit.optimize
  split
  · next body f ho =>
    simp only [run, Option.bind_eq_bind]
    cases bindInputs (fun _ => 0) c.inputs inputs with
    | none => rfl
    | some env0 =>
      simp only [Option.bind_some]
      have hr0 : ExecRel p {} ({ env := env0, private_, ledger } : State ω σ)
          { env := env0, private_, ledger } :=
        ⟨⟨fun v => by simp [Expr.subst, List.lookup, Expr.eval], (fun _ h => nomatch h),
          (fun _ _ h => nomatch h)⟩, rfl, rfl, rfl, rfl, rfl⟩
      have hs := Stmt.optimizeAll_exec p O ho hr0
      rw [List.toList_toArray]
      revert hs
      cases steps p O c.body.toList { env := env0, private_, ledger } <;>
        cases steps p O body { env := env0, private_, ledger } <;> simp only [OptRel, false_implies]
      · intro _; rfl
      · next t t' =>
        intro hrel
        simp only [Option.bind_some]
        rw [Facts.rw_evalList p hrel.facts]
        cases Expr.evalList p t.env c.outputs with
        | none => rfl
        | some outs =>
          simp [Result.observable, hrel.priv, hrel.pub, hrel.groups, hrel.private_, hrel.ledger]
  · rfl

/-! ## The questions the oracles are asked -/

/-- The oracles `O`, each also writing down, in order, every question it
    answers: the witness its name and arguments, the ledger the instructions
    it is sent. -/
def Oracles.logged (O : Oracles ω σ) :
    Oracles (ω × List (String × List Fr)) (σ × List (List (Impact.Op Fr))) where
  witness name args st :=
    (O.witness name args st.1).map fun (vals, w) => (vals, (w, st.2 ++ [(name, args)]))
  ledger req st :=
    (O.ledger req st.1).map fun (vals, l) => (vals, (l, st.2 ++ [req]))

/-- On the optimized circuit the executor asks the witnesses exactly the same
    questions (names and arguments), in the same order, and sends the ledger
    exactly the same instructions, in the same order, as on the original; and
    the calls complete together. -/
theorem optimize_asks_same (p : Prims) (O : Oracles ω σ) (c : Circuit)
    (inputs : List Fr) (private_ : ω) (ledger : σ) :
    (run p O.logged c.optimize inputs (private_, []) (ledger, [])).map (fun r => (r.private_.2, r.ledger.2))
      = (run p O.logged c inputs (private_, []) (ledger, [])).map (fun r => (r.private_.2, r.ledger.2)) := by
  have h := optimize_correct p O.logged c inputs (private_, []) (ledger, [])
  have h' := congrArg (Option.map fun (o : List Fr × List Fr × List Fr × List Fr × _ × _) =>
    (o.2.2.2.2.1.2, o.2.2.2.2.2.2)) h
  simpa [Option.map_map, Function.comp_def, Result.observable] using h'

end Damp.Exec
