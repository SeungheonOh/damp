/-
Control: `require`, `val`, guards, `when_` and `cond` (`if%`), as `Runs` statements, and
what each statement form does under a guard that is off.

* `require c msg` succeeds exactly when the guard is off or `c` is true, and changes
  nothing (`Runs.require`).
* `cond c t e` builds `t` under the guard `g ∧ c` and `e` under `g ∧ ¬c`, where `g`
  is the guard in force, and selects the result: it succeeds exactly when both
  branches do under their guards, and its result is the taken branch's
  (`Runs.cond`). What "under a guard that is off" means for each statement form
  is spelled out at the statement level: an assert built by `require` passes
  (`exec_require_off`), a range check built by a checked operation passes on its
  zeroed value (`exec_guarded_check_off`), a witness call reads nothing from the
  private transcript and binds zeros (`exec_witness_off`), and a ledger operation
  reads nothing from the public transcript, binds zeros and contributes inactive
  groups with zeroed values (`exec_ledger_off`).
-/
import Damp.Proofs.Interface.Arith

namespace Damp
open IR

variable {p : Zkir.Prims}

/-! ## `require` -/

section Require
variable {s : Build} {st : RunState} {gb cb : Bool}

/-- `require c` succeeds exactly when the guard is off or `c` holds, and changes nothing. -/
theorem Runs.require {c : Boolean} (msg : String) (hg : GuardIs p s st gb)
    (hc : Stable s.next st.env (fun e => Boolean.Is p e c cb)) :
    Runs p (Damp.require c msg) s st (gb = true → cb = true) (fun _ _ => True) :=
  (Runs.ofCheck (require_run c msg s) (require_correct msg hg.holds hc.holds) fun _ => Stable.const trivial).conseq
    (by cases gb <;> simp) (fun _ _ h => h)

/-- `require c` at the top level of a circuit succeeds exactly when `c` holds. -/
theorem Runs.require_top {c : Boolean} (msg : String) (hs : s.guard = .const 1)
    (hc : Stable s.next st.env (fun e => Boolean.Is p e c cb)) :
    Runs p (Damp.require c msg) s st (cb = true) (fun _ _ => True) :=
  (Runs.require (gb := true) msg (fun e _ => by rw [hs]; exact guard_one_is) hc).conseq (by simp)
    (fun _ _ h => h)

end Require

/-! ## Statement forms under a guard that is off -/

section Off
variable {st : RunState}

/-- An assert built by `require` under a guard that is off passes, whatever its condition
    (as long as the condition has a truth value), and changes nothing. -/
theorem exec_require_off {g c : Expr} {cb : Bool} (msg : String) (hg : Boolean.Is p st.env ⟨g⟩ false)
    (hc : Boolean.Is p st.env ⟨c⟩ cb) : Stmt.exec p st (.assert (requireCond g c) msg) = some st := by
  have := require_correct (c := ⟨c⟩) msg hg hc
  rw [execAll_single] at this; rw [this]; rfl

/-- The range check of a checked operation under a guard that is off checks the value 0, which
    every `Uint` range accepts; it passes and changes nothing. -/
theorem exec_guarded_check_off {g e : Expr} {v : Fr} {k : Nat} (hk : k < 2 ^ 254)
    (hg : Boolean.Is p st.env ⟨g⟩ false) (he : e.eval p st.env = some v) :
    Stmt.exec p st (.constrain (guardedExpr g e) (uintRange k)) = some st := by
  have := (guarded_check_correct hk he hg).1
  rw [execAll_single] at this; rw [this]; rfl

/-- Reading values from a stream while inactive consumes nothing and binds zeros (given every
    range accepts 0). -/
theorem readAll_off (env : Env) (stream : List Fr) : ∀ outs : List (Var × Option Range),
    (∀ o ∈ outs, ∀ r, o.2 = some r → r.holds 0 = true) →
    readAll false env outs stream = some (outs.foldl (fun e o => e.set o.1 0) env, stream)
  | [], _ => rfl
  | (v, none) :: outs, h => by
    simp only [readAll, Zkir.readOne, Bool.false_eq_true, ↓reduceIte, bind, Option.bind]
    exact readAll_off _ stream outs fun o ho r hr => h o (List.mem_cons_of_mem _ ho) r hr
  | (v, some r) :: outs, h => by
    have hr0 : r.holds 0 = true := h (v, some r) (List.mem_cons_self ..) r rfl
    simp only [readAll, Zkir.readOne, Bool.false_eq_true, ↓reduceIte, bind, Option.bind, hr0]
    exact readAll_off _ stream outs fun o ho r hr => h o (List.mem_cons_of_mem _ ho) r hr

/-- A witness call under a guard that is off: nothing is read from the private transcript and
    the outputs are bound to 0. -/
theorem exec_witness_off {g : Expr} {name : String} {args : List Expr} {outs : List (Var × Option Range)}
    {shape : Shape} (hg : g.eval p st.env = some 0) (hr : ∀ o ∈ outs, ∀ r, o.2 = some r → r.holds 0 = true) :
    Stmt.exec p st (.witness g name args outs shape) =
      some { st with env := outs.foldl (fun e o => e.set o.1 0) st.env } := by
  simp only [Stmt.exec, hg]
  cases outs with
  | nil => rfl
  | cons o os =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
    simp only [bind, Option.bind, show asBool (0 : Fr) = some false from rfl, readAll_off _ _ _ hr]
    rfl

/-- The public-input groups of a ledger operation under a guard that is off: every operand is
    still evaluated, the groups are inactive and their values zeroed. -/
theorem ledgerGroups_off (env : Env) : ∀ ops : List (Impact.Op Expr), ∀ gs,
    ledgerGroups p env true ops = some gs →
    ledgerGroups p env false ops = some (gs.map fun g => { active := false, vals := g.vals.map fun _ => 0 })
  | [], gs, h => by simp [ledgerGroups] at h; subst h; rfl
  | op :: ops, gs, h => by
    simp only [ledgerGroups, bind, Option.bind] at h ⊢
    cases hv : Expr.evalList p env (op.encode Expr.const) with
    | none => simp [hv] at h
    | some vals =>
      cases hr : ledgerGroups p env true ops with
      | none => simp [hv, hr] at h
      | some rest =>
        simp only [hv, hr] at h
        have h' := (Option.some.inj h).symm
        subst h'
        simp [ledgerGroups_off env ops rest hr]

/-- A ledger operation under a guard that is off: nothing is read from the public transcript,
    the read variables are bound to 0, and its groups are inactive with zeroed values. -/
theorem exec_ledger_off {g : Expr} {reads : List Var} {ops : List (Impact.Op Expr)} {gs : List Zkir.Group}
    (hg : g.eval p st.env = some 0) (hne : (reads.isEmpty && ops.isEmpty) = false)
    (hgs : ledgerGroups p (reads.foldl (fun e v => e.set v 0) st.env) true ops = some gs) :
    Stmt.exec p st (.ledger g reads ops) =
      some { st with env := reads.foldl (fun e v => e.set v 0) st.env,
                     groups := st.groups ++ gs.map fun g => { active := false, vals := g.vals.map fun _ => 0 } } := by
  have hro := readAll_off st.env st.pub (reads.map fun v => (v, none)) (by simp)
  have hfold : ∀ (vs : List Var) (e : Env), ((vs.map fun v => ((v, none) : Var × Option Range)).foldl
      (fun e o => e.set o.1 0) e) = vs.foldl (fun e v => e.set v 0) e := by
    intro vs; induction vs with
    | nil => intro; rfl
    | cons v vs ih => intro e; exact ih _
  rw [hfold] at hro
  simp only [Stmt.exec, hg, hne, Bool.false_eq_true, ↓reduceIte]
  simp only [bind, Option.bind, show asBool (0 : Fr) = some false from rfl, hro,
    ledgerGroups_off _ ops gs hgs]
  rfl

end Off

/-! ## Builder steps that emit nothing -/

section Simple
variable {s : Build} {st : RunState}

/-- A computation that builds nothing and leaves the state as it is. -/
theorem Runs.ofRun {α : Type} {m : CircuitM α} {a : α} {Q : α → Env → Prop} (hrun : m.run s = (a, s))
    (hQ : Stable s.next st.env (Q a)) : Runs p m s st True Q := by
  refine ⟨by rw [hrun]; exact Nat.le_refl _, by rw [hrun], [], by rw [hrun]; simp, by simp [execAll],
    fun st' h' => ?_⟩
  simp only [execAll, Option.some.injEq] at h'; subst h'
  exact ⟨Agree.refl _ _, rfl, rfl, rfl, by rw [hrun]; exact hQ⟩

theorem Runs.currentGuard : Runs p Damp.currentGuard s st True (fun g _ => g = s.guard) :=
  Runs.ofRun (a := s.guard) rfl (fun _ _ => rfl)

/-- Anything that only records errors. -/
theorem Runs.ofErrors {α : Type} {m : CircuitM α} {Q : α → Env → Prop}
    (h : ∀ s, (m.run s).2 = { s with errors := (m.run s).2.errors })
    (hQ : Stable s.next st.env (Q (m.run s).1)) : Runs p m s st True Q := by
  have hs := h s
  refine ⟨by rw [hs]; exact Nat.le_refl _, by rw [hs], [], by rw [hs]; simp, by simp [execAll], fun st' h' => ?_⟩
  simp only [execAll, Option.some.injEq] at h'; subst h'
  exact ⟨Agree.refl _ _, rfl, rfl, rfl, by rw [hs]; exact hQ⟩

end Simple

/-! ## `val`: computing a value once -/

/-- The bindings `val` emits for a list of expressions, to variables from `k` on. -/
def bindList (k : Nat) (hint : String) (es : List Expr) : List Stmt :=
  ((List.range' k es.length).zip es).map fun (v, e) => .bind v hint e

/-- The allocation-and-bind loop of `val`. -/
abbrev valLoop (hint : String) (es : List Expr) : CircuitM (List Expr) :=
  es.mapM fun e => do
    let v ← freshVar
    emit (.bind v hint e)
    pure (Expr.var v)

theorem valLoop_run (hint : String) : ∀ (es : List Expr) (s : Build),
    ((valLoop hint es).run s).1 = argVars s.next es.length ∧
    ((valLoop hint es).run s).2.next = s.next + es.length ∧
    ((valLoop hint es).run s).2.guard = s.guard ∧
    ((valLoop hint es).run s).2.stmts.toList = s.stmts.toList ++ bindList s.next hint es
  | [], s => ⟨rfl, rfl, rfl, by show s.stmts.toList = _; simp [bindList]⟩
  | e :: es, s => by
    have h1 : ((do let v ← freshVar; emit (.bind v hint e); pure (Expr.var v)) : CircuitM Expr).run s =
        (.var s.next, { s with next := s.next + 1, stmts := s.stmts.push (.bind s.next hint e) }) := rfl
    have hc : (valLoop hint (e :: es)).run s =
        (Prod.fst ((valLoop hint es).run { s with next := s.next + 1, stmts := s.stmts.push (.bind s.next hint e) })
          |> fun vs => Expr.var s.next :: vs,
         ((valLoop hint es).run { s with next := s.next + 1, stmts := s.stmts.push (.bind s.next hint e) }).2) := by
      simp only [valLoop, List.mapM_cons]
      rw [CircuitM.bind_run, h1, CircuitM.bind_run]; rfl
    obtain ⟨r1, r2, r3, r4⟩ := valLoop_run hint es { s with next := s.next + 1, stmts := s.stmts.push (.bind s.next hint e) }
    rw [hc]
    refine ⟨?_, ?_, r3, ?_⟩
    · simp only at r1 ⊢; rw [r1]; simp [argVars, List.range'_succ]
    · simp only at r2 ⊢; rw [r2, List.length_cons, Nat.add_assoc, Nat.add_comm 1]
    · simp only at r4 ⊢; rw [r4]; simp [bindList, List.range'_succ]

/-- Executing the bindings: each variable gets the value of its expression; nothing below `k₀`
    changes. -/
theorem exec_bindList (hint : String) (k₀ : Nat) : ∀ (es : List Expr) (k : Nat) (st : RunState) (xs : List Fr),
    k₀ ≤ k → Stable k₀ st.env (fun e => Expr.evalList p e es = some xs) →
    ∃ env', execAll p (bindList k hint es) st = some { st with env := env' } ∧
      Agree k st.env env' ∧ (List.range' k es.length).map env' = xs
  | [], k, st, xs, _, h => by
    have := h.holds; simp [Expr.evalList] at this; subst this
    exact ⟨st.env, by simp [bindList, execAll], Agree.refl _ _, rfl⟩
  | e :: es, k, st, xs, hk, h => by
    have hx := h.holds
    obtain ⟨x, xs', he, hes, rfl⟩ := evalList_cons.1 hx
    let st₁ : RunState := { st with env := st.env.set k x }
    have hag : Agree k₀ st.env st₁.env := Agree.set hk x
    have h₁ : Stable k₀ st₁.env (fun e => Expr.evalList p e es = some xs') :=
      (h.transfer hag).imp fun e hh => by obtain ⟨_, _, _, h2, h3⟩ := evalList_cons.1 hh; cases h3; exact h2
    obtain ⟨env', hex, hagr, hvals⟩ := exec_bindList hint k₀ es (k + 1) st₁ xs' (by omega) h₁
    refine ⟨env', ?_, ?_, ?_⟩
    · simp only [bindList, List.length_cons, List.range'_succ, List.zip_cons_cons, List.map_cons, execAll]
      simp only [Stmt.exec, he, bind, Option.bind]
      exact hex
    · exact (Agree.set (Nat.le_refl k) x).trans (hagr.mono (Nat.le_succ k))
    · simp only [List.length_cons, List.range'_succ, List.map_cons, hvals, List.cons.injEq, and_true]
      rw [← hagr k (Nat.lt_succ_self k)]
      simp [st₁, Env.set]

/-- `val x` computes `x` once: it always succeeds, and its result means what `x` meant. -/
theorem Runs.val {α : Type} [Value α] (hrt : Value.RoundTrip α) {x : α} {xs : List Fr} (hint : String)
    {s : Build} {st : RunState} (hlen : (Value.toExprs x).length = Value.width α)
    (hx : Stable s.next st.env (fun e => Value.Is p e x xs)) :
    Runs p (Damp.val x hint) s st True (fun r e => Value.Is p e r xs) := by
  obtain ⟨r1, r2, r3, r4⟩ := valLoop_run hint (Value.toExprs x) s
  have hrun : (Damp.val x hint).run s =
      (Value.ofExprs ((valLoop hint (Value.toExprs x)).run s).1, ((valLoop hint (Value.toExprs x)).run s).2) := by
    show (valLoop hint (Value.toExprs x) >>= fun vs => Pure.pure (Value.ofExprs vs)).run s = _
    rw [CircuitM.bind_run]; rfl
  obtain ⟨env', hex, hag, hvals⟩ := exec_bindList (p := p) hint s.next (Value.toExprs x) s.next st xs
    (Nat.le_refl _) hx
  refine ⟨by rw [hrun, r2]; exact Nat.le_add_right _ _, by rw [hrun, r3], bindList s.next hint (Value.toExprs x),
    by rw [hrun, r4], by rw [hex]; simp, fun st' h' => ?_⟩
  rw [hex, Option.some.injEq] at h'; subst h'
  refine ⟨hag, rfl, rfl, rfl, ?_⟩
  rw [hrun, r1, r2]
  intro e he
  unfold Value.Is
  rw [hlen] at he hvals ⊢
  rw [hrt _ (by simp [argVars]) p e, evalList_argVars, ← hvals]
  congr 1
  exact List.map_congr_left fun v hv => by
    have := List.mem_range'_1.1 hv; exact (he v (by omega)).symm

/-- `val` on a `Uint`: the result means the same number. -/
theorem Runs.val_uint {m n : Nat} {a : Uint m} (hint : String) {s : Build} {st : RunState}
    (ha : Stable s.next st.env (fun e => Uint.Means p e a n)) :
    Runs p (Damp.val a hint) s st True (fun r e => Uint.Means p e r n) := by
  have hb := ha.holds.bound
  refine (Runs.val (roundTrip_uint hb) (xs := [Fr.ofNat n]) hint (by rw [Value.width_uint]; rfl)
    (ha.imp fun e h => by simp [Value.Is, Value.toExprs, Expr.evalList, h.eval])).conseq Iff.rfl ?_
  intro r e h
  have : r.expr.eval p e = some (Fr.ofNat n) := by
    simp only [Value.Is, Value.toExprs, Expr.evalList] at h
    cases hr : r.expr.eval p e <;> simp [hr, Option.bind] at h; rw [h]
  exact ⟨hb, ha.holds.le, this⟩

/-- `val` on a `Boolean`. -/
theorem Runs.val_boolean {c : Boolean} {u : Bool} (hint : String) {s : Build} {st : RunState}
    (hc : Stable s.next st.env (fun e => Boolean.Is p e c u)) :
    Runs p (Damp.val c hint) s st True (fun r e => Boolean.Is p e r u) := by
  refine (Runs.val roundTrip_boolean (xs := [Fr.ofBool u]) hint rfl
    (hc.imp fun e h => by unfold Boolean.Is at h; simp [Value.Is, Value.toExprs, Expr.evalList, h])).conseq Iff.rfl ?_
  intro r e h
  simp only [Value.Is, Value.toExprs, Expr.evalList] at h
  cases hr : r.expr.eval p e <;> simp [hr, Option.bind] at h
  show r.expr.eval p e = _; rw [hr, h]

/-! ## Guards -/

/-- `guardAnd g c` means `g ∧ c`. -/
theorem guardAnd_eval {env : Env} {g c : Expr} {gb cb : Bool} (hg : g.eval p env = some (Fr.ofBool gb))
    (hc : c.eval p env = some (Fr.ofBool cb)) : (guardAnd g c).eval p env = some (Fr.ofBool (gb && cb)) := by
  unfold guardAnd
  split
  · rw [const_one_is hg]; exact hc
  · rw [Expr.eval_sel' hc hg rfl]; cases cb <;> cases gb <;> rfl

/-- `nameGuard e` names `e` with a fresh variable unless it is atomic; the name means what `e` means. -/
theorem Runs.nameGuard {e : Expr} {v : Fr} {s : Build} {st : RunState}
    (he : Stable s.next st.env (fun env => e.eval p env = some v)) :
    Runs p (Damp.nameGuard e) s st True (fun r env => r.eval p env = some v) := by
  unfold Damp.nameGuard
  split
  · exact Runs.pure he
  · exact Runs.pure he
  · have hrun : ((do let w ← freshVar; emit (.bind w "t" e); Pure.pure (Expr.var w)) : CircuitM Expr).run s =
        (.var s.next, { s with next := s.next + 1, stmts := s.stmts.push (.bind s.next "t" e) }) := rfl
    refine ⟨by rw [hrun]; exact Nat.le_succ _, by rw [hrun], [.bind s.next "t" e],
      by rw [hrun]; exact Array.toList_push, ?_, fun st' h' => ?_⟩
    · simp [execAll, Stmt.exec, he.holds, Option.bind]
    · have hx : execAll p [Stmt.bind s.next "t" e] st = some { st with env := st.env.set s.next v } := by
        rw [execAll_single]; simp only [Stmt.exec, he.holds]; rfl
      rw [hx] at h'; cases h'
      refine ⟨Agree.set (Nat.le_refl _) v, rfl, rfl, rfl, ?_⟩
      rw [hrun]
      intro env hag
      show some (env s.next) = some v
      rw [← hag s.next (Nat.lt_succ_self _)]
      simp [Env.set]

/-- `underGuard g body` runs `body` with `g` as the guard, then restores the guard. -/
theorem Runs.underGuard {α : Type} {g : Expr} {body : CircuitM α} {s : Build} {st : RunState} {ok : Prop}
    {Q : α → Env → Prop} (h : Runs p body { s with guard := g } st ok Q) :
    Runs p (Damp.underGuard g body) s st ok Q := by
  have hrun : (Damp.underGuard g body).run s =
      ((body.run { s with guard := g }).1, { (body.run { s with guard := g }).2 with guard := s.guard }) := rfl
  obtain ⟨hn, -, T, hT, hs, hst⟩ := h
  exact ⟨by rw [hrun]; exact hn, by rw [hrun], T, by rw [hrun]; exact hT, hs, by rw [hrun]; exact hst⟩

/-! ## `cond` (`if%`) and `when_` -/

/-- The assumptions a branch of a conditional may make about the state it is built in: it starts
    no earlier than the conditional, from a run state that agrees with the one the conditional
    started from below the conditional's counter, with the same transcripts, and its guard
    means `g`. -/
def BranchCtx (p : Zkir.Prims) (s : Build) (st : RunState) (g : Bool) (s' : Build) (st' : RunState) : Prop :=
  s.next ≤ s'.next ∧ Agree s.next st.env st'.env ∧ st'.priv = st.priv ∧ st'.pub = st.pub ∧
    st'.groups = st.groups ∧ GuardIs p s' st' g

theorem BranchCtx.transfer {s : Build} {st : RunState} {g : Bool} {s' : Build} {st' : RunState}
    (h : BranchCtx p s st g s' st') {P : Env → Prop} (hP : Stable s.next st.env P) : Stable s'.next st'.env P :=
  (hP.transfer h.2.1).mono h.1

/-- **`if%`.** Under a guard meaning `gb`, with the condition meaning `cb`: the conditional
    succeeds exactly when the `then` branch succeeds under the guard `gb ∧ cb` and the `else`
    branch under `gb ∧ ¬cb`; its result is `select c a b` of the branch results, so it is the
    taken branch's value (`select_*`). Each branch is described for every state it may be built
    in (`BranchCtx`), so its effects are the ones of its statements under that guard: with the
    guard off, see `exec_require_off` and the other `*_off` lemmas. -/
theorem Runs.cond {α : Type} [Value α] {c : Boolean} {t e : CircuitM α} {s : Build} {st : RunState}
    {gb cb : Bool} {okt oke : Prop} {Qt Qe : α → Env → Prop}
    (hg : GuardIs p s st gb) (hc : Stable s.next st.env (fun env => Boolean.Is p env c cb))
    (gt : Grows t) (ge : Grows e)
    (ht : ∀ s' st', BranchCtx p s st (gb && cb) s' st' → Runs p t s' st' okt Qt)
    (he : ∀ s' st', BranchCtx p s st (gb && !cb) s' st' → Runs p e s' st' oke Qe) :
    Runs p (Damp.cond c t e) s st (okt ∧ oke)
      (fun r env => ∃ a b, r = select c a b ∧ Qt a env ∧ Qe b env ∧ Boolean.Is p env c cb) := by
  rw [cond_eq]
  -- outer guard
  refine (Runs.bind' Runs.currentGuard (Grows.bind (Grows.nameGuard _) fun _ => Grows.bind (Grows.nameGuard _)
    fun _ => Grows.bind (Grows.underGuard _ gt) fun _ => Grows.bind (Grows.underGuard _ ge) fun _ =>
    Grows.bind (Grows.of_errors (condProblems_run _ _)) fun _ => Grows.pure' _) fun st₀ ha₀ hp₀ hq₀ hgr₀ hQ₀ => ?_)
  have hout : (Damp.currentGuard.run s).1 = s.guard := rfl
  have hs₀ : (Damp.currentGuard.run s).2 = s := rfl
  rw [hout, hs₀]
  rw [hs₀] at hQ₀
  have hg₀ : GuardIs p s st₀ gb := hg.transfer ha₀
  have hc₀ := hc.transfer ha₀
  -- then-guard
  have hgt : Stable s.next st₀.env (fun env => (guardAnd s.guard c.expr).eval p env = some (Fr.ofBool (gb && cb))) :=
    (hg₀.and hc₀).imp fun env h => guardAnd_eval h.1 h.2
  refine Runs.bind' (Runs.nameGuard hgt) (Grows.bind (Grows.nameGuard _)
    fun _ => Grows.bind (Grows.underGuard _ gt) fun _ => Grows.bind (Grows.underGuard _ ge) fun _ =>
    Grows.bind (Grows.of_errors (condProblems_run _ _)) fun _ => Grows.pure' _) fun st₁ ha₁ hp₁ hq₁ hgr₁ hQ₁ => ?_
  have hn₁ := (Grows.nameGuard (guardAnd s.guard c.expr) s).1
  generalize (Damp.nameGuard (guardAnd s.guard c.expr)).run s = q₁ at hQ₁ hn₁ ⊢
  obtain ⟨gtE, s₁⟩ := q₁
  simp only at hQ₁ hn₁ ⊢
  -- else-guard
  have hnc : Stable s.next st₁.env (fun env => Boolean.Is p env c.not (!cb)) :=
    (hc₀.transfer ha₁).imp fun env h => Boolean.not_is h
  have hge : Stable s₁.next st₁.env
      (fun env => (guardAnd s.guard c.not.expr).eval p env = some (Fr.ofBool (gb && !cb))) :=
    (((hg₀.transfer ha₁).and hnc).imp fun env h => guardAnd_eval h.1 h.2).mono hn₁
  refine Runs.bind' (Runs.nameGuard hge) (Grows.bind (Grows.underGuard _ gt) fun _ =>
    Grows.bind (Grows.underGuard _ ge) fun _ =>
    Grows.bind (Grows.of_errors (condProblems_run _ _)) fun _ => Grows.pure' _) fun st₂ ha₂ hp₂ hq₂ hgr₂ hQ₂ => ?_
  have hn₂ := (Grows.nameGuard (guardAnd s.guard c.not.expr) s₁).1
  generalize (Damp.nameGuard (guardAnd s.guard c.not.expr)).run s₁ = q₂ at hQ₂ hn₂ ⊢
  obtain ⟨geE, s₂⟩ := q₂
  simp only at hQ₂ hn₂ ⊢
  -- then-branch
  have ctxT : BranchCtx p s st (gb && cb) { s₂ with guard := gtE } st₂ :=
    ⟨Nat.le_trans hn₁ hn₂, ha₀.trans ((ha₁.trans (ha₂.mono hn₁))), hp₂.trans (hp₁.trans hp₀),
      hq₂.trans (hq₁.trans hq₀), hgr₂.trans (hgr₁.trans hgr₀), (hQ₁.transfer ha₂).mono hn₂⟩
  refine (Runs.bind (Runs.underGuard (ht _ _ ctxT)) (Grows.bind (Grows.underGuard _ ge) fun _ =>
    Grows.bind (Grows.of_errors (condProblems_run _ _)) fun _ => Grows.pure' _)
    fun st₃ ha₃ hp₃ hq₃ hgr₃ hQ₃ => ?_).conseq Iff.rfl (fun _ _ h => h)
  have hn₃ := (Grows.underGuard gtE gt s₂).1
  have hg₃ := (Grows.underGuard gtE gt s₂).2.1
  generalize (Damp.underGuard gtE t).run s₂ = q₃ at hQ₃ hn₃ hg₃ ⊢
  obtain ⟨a, s₃⟩ := q₃
  simp only at hQ₃ hn₃ hg₃ ⊢
  -- else-branch
  have ctxE : BranchCtx p s st (gb && !cb) { s₃ with guard := geE } st₃ :=
    ⟨Nat.le_trans hn₁ (Nat.le_trans hn₂ hn₃), ctxT.2.1.trans (ha₃.mono ctxT.1),
      hp₃.trans ctxT.2.2.1, hq₃.trans ctxT.2.2.2.1, hgr₃.trans ctxT.2.2.2.2.1,
      (hQ₂.transfer ha₃).mono hn₃⟩
  refine (Runs.bind (Runs.underGuard (he _ _ ctxE)) (Grows.bind (Grows.of_errors (condProblems_run _ _))
    fun _ => Grows.pure' _) fun st₄ ha₄ hp₄ hq₄ hgr₄ hQ₄ => ?_).conseq (ok := oke ∧ True) (by simp)
    (fun _ _ h => h)
  have hn₄ := (Grows.underGuard geE ge s₃).1
  generalize (Damp.underGuard geE e).run s₃ = q₄ at hQ₄ hn₄ ⊢
  obtain ⟨b, s₄⟩ := q₄
  simp only at hQ₄ hn₄ ⊢
  have hn₄' : s₃.next ≤ s₄.next := hn₄
  refine Runs.bind' (Runs.ofErrors (condProblems_run a b) (Q := fun _ _ => True) (Stable.const trivial))
    (Grows.pure' _) fun st₅ ha₅ _ _ _ _ => ?_
  have hs₅ := condProblems_run a b s₄
  generalize (condProblems a b).run s₄ = q₅ at hs₅ ⊢
  obtain ⟨u, s₅⟩ := q₅
  simp only at hs₅ ⊢
  have hn₅ : s₅.next = s₄.next := by rw [hs₅]
  refine Runs.pure fun env hag => ⟨a, b, rfl, ?_, ?_, ?_⟩
  · -- the then-result, established at `s₃`
    have := ((hQ₃.transfer (ha₄.mono (by exact Nat.le_refl _))).mono hn₄').transfer (ha₅.mono (Nat.le_refl _))
    exact this env (by rw [hn₅] at hag; exact hag)
  · have := hQ₄.transfer ha₅
    exact this env (by rw [hn₅] at hag; exact hag)
  · have hA : Agree s.next st.env st₅.env :=
      ((ctxE.2.1.trans (ha₄.mono ctxE.1)).trans (ha₅.mono (Nat.le_trans ctxE.1 hn₄')))
    exact (hc.transfer hA) env (hag.mono (by rw [hn₅]; exact Nat.le_trans ctxE.1 hn₄'))

/-- `when_ c body` (`if%` without `else`): `body` is built under the guard `g ∧ c`; the whole
    succeeds exactly when `body` does under that guard. -/
theorem Runs.when_ {c : Boolean} {body : CircuitM Unit} {s : Build} {st : RunState} {gb cb : Bool} {ok : Prop}
    (hg : GuardIs p s st gb) (hc : Stable s.next st.env (fun env => Boolean.Is p env c cb))
    (gbody : Grows body)
    (hb : ∀ s' st', BranchCtx p s st (gb && cb) s' st' → Runs p body s' st' ok (fun _ _ => True)) :
    Runs p (Damp.when_ c body) s st ok (fun _ _ => True) := by
  unfold Damp.when_
  refine (Runs.bind' Runs.currentGuard (Grows.bind (Grows.nameGuard _) fun _ => Grows.underGuard _ gbody)
    fun st₀ ha₀ hp₀ hq₀ hgr₀ _ => ?_)
  have hout : (Damp.currentGuard.run s).1 = s.guard := rfl
  have hs₀ : (Damp.currentGuard.run s).2 = s := rfl
  rw [hout, hs₀]
  have hgt : Stable s.next st₀.env (fun env => (guardAnd s.guard c.expr).eval p env = some (Fr.ofBool (gb && cb))) :=
    ((hg.transfer ha₀).and (hc.transfer ha₀)).imp fun env h => guardAnd_eval h.1 h.2
  refine Runs.bind' (Runs.nameGuard hgt) (Grows.underGuard _ gbody) fun st₁ ha₁ hp₁ hq₁ hgr₁ hQ₁ => ?_
  have hn₁ := (Grows.nameGuard (guardAnd s.guard c.expr) s).1
  generalize (Damp.nameGuard (guardAnd s.guard c.expr)).run s = q₁ at hQ₁ hn₁ ⊢
  obtain ⟨g, s₁⟩ := q₁
  simp only at hQ₁ hn₁ ⊢
  exact Runs.underGuard (hb _ _ ⟨hn₁, ha₀.trans (ha₁.mono (Nat.le_refl _)), hp₁.trans hp₀, hq₁.trans hq₀,
    hgr₁.trans hgr₀, hQ₁⟩)

end Damp
