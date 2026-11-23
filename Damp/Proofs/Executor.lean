/-
Every call the executor completes is one the circuit accepts.

`Exec.run` (`Damp/Executor/Spec.lean`) runs a circuit against the user's witnesses
and the ledger and records the private transcript, the values read from the
ledger, the public inputs and the outputs. This file proves that those
records are exactly an accepted run of the circuit under the IR semantics
(`run_accepted`), and therefore, by the compiler's correctness, of the ZKIR
that is shipped (`run_accepted_by_zkir`).

Whatever the witnesses and the ledger answer, a completed call cannot hand the
prover something the circuit rejects, and the public inputs the circuit
declares are the ones the executor recorded.
-/
import Damp.Executor.Spec
import Damp.Proofs.Compiler

set_option linter.unusedSimpArgs false

namespace Damp.Exec
open Damp.IR
open Damp.Zkir (Prims Group Outcome)

variable {ω σ : Type}

/-! ## Reading recorded values back -/

/-- Values the executor assigned are read back, in order, by the semantics. -/
theorem assign_readAll :
    ∀ (outs : List (Var × Option Range)) (env : Env) (vals : List Fr) (env' : Env),
      assign env outs vals = some env' →
      ∀ tail, readAll true env outs (vals ++ tail) = some (env', tail)
  | [], env, [], env', h, tail => by
      simp only [assign, Option.some.injEq] at h
      simp [readAll, h]
  | [], env, _ :: _, env', h, tail => by simp [assign] at h
  | (v, range) :: rest, env, [], env', h, tail => by simp [assign] at h
  | (v, range) :: rest, env, x :: xs, env', h, tail => by
      simp only [assign] at h
      simp only [readAll, List.cons_append, Zkir.readOne, ite_true, Option.bind_eq_bind,
        Option.bind_some]
      cases range with
      | none =>
          simp only at h
          simp only [Option.pure_def, Option.bind_some]
          exact assign_readAll rest _ xs env' h tail
      | some r =>
          simp only at h
          by_cases hh : r.holds x
          · simp only [hh, ite_true] at h
            simp only [hh, ite_true, Option.pure_def, Option.bind_some]
            exact assign_readAll rest _ xs env' h tail
          · simp [hh] at h

/-- Zeros the executor assigned for a skipped statement are what the semantics
    gives without reading anything. -/
theorem assign_zeros_readAll :
    ∀ (outs : List (Var × Option Range)) (env env' : Env),
      assign env outs (outs.map fun _ => 0) = some env' →
      ∀ stream, readAll false env outs stream = some (env', stream)
  | [], env, env', h, stream => by
      simp only [List.map_nil, assign, Option.some.injEq] at h
      simp [readAll, h]
  | (v, range) :: rest, env, env', h, stream => by
      simp only [List.map_cons, assign] at h
      simp only [readAll, Zkir.readOne, Bool.false_eq_true, ite_false, Option.bind_eq_bind,
        Option.bind_some]
      cases range with
      | none =>
          simp only at h
          simp only [Option.pure_def, Option.bind_some]
          exact assign_zeros_readAll rest _ env' h stream
      | some r =>
          simp only at h
          by_cases hh : r.holds 0
          · simp only [hh, ite_true] at h
            simp only [hh, ite_true, Option.pure_def, Option.bind_some]
            exact assign_zeros_readAll rest _ env' h stream
          · simp [hh] at h

/-! ## One statement -/

/-- A statement the executor completes is one the semantics accepts, reading
    exactly what the executor recorded and leaving the rest of each transcript. -/
theorem step_sim (p : Prims) (O : Oracles ω σ) (s s' : State ω σ) (st : Stmt)
    (h : step p O s st = some s') :
    ∃ dp dq, s'.priv = s.priv ++ dp ∧ s'.pub = s.pub ++ dq ∧
      ∀ tp tq, st.exec p { env := s.env, priv := dp ++ tp, pub := dq ++ tq, groups := s.groups }
        = some { env := s'.env, priv := tp, pub := tq, groups := s'.groups } := by
  cases st with
  | bind v hint e =>
      simp only [step] at h
      cases hx : e.eval p s.env with
      | none => simp [hx] at h
      | some x =>
          simp only [hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
            Option.some.injEq] at h
          subst h
          exact ⟨[], [], by simp, by simp, fun tp tq => by simp [Stmt.exec, hx]⟩
  | assert cond msg =>
      simp only [step] at h
      cases hx : cond.eval p s.env with
      | none => simp [hx] at h
      | some x =>
          simp only [hx, Option.bind_eq_bind, Option.bind_some] at h
          cases hb : asBool x with
          | none => simp [hb] at h
          | some b =>
              simp only [hb, Option.bind_some] at h
              cases b with
              | false => simp at h
              | true =>
                  simp only [ite_true, Option.pure_def, Option.some.injEq] at h
                  subst h
                  exact ⟨[], [], by simp, by simp, fun tp tq => by simp [Stmt.exec, hx, hb]⟩
  | constrain e r =>
      simp only [step] at h
      cases hx : e.eval p s.env with
      | none => simp [hx] at h
      | some x =>
          simp only [hx, Option.bind_eq_bind, Option.bind_some] at h
          by_cases hh : r.holds x
          · simp only [hh, ite_true, Option.pure_def, Option.some.injEq] at h
            subst h
            exact ⟨[], [], by simp, by simp, fun tp tq => by simp [Stmt.exec, hx, hh]⟩
          · simp [hh] at h
  | witness guard name args outs shape =>
      simp only [step] at h
      cases hx : guard.eval p s.env with
      | none => simp [hx] at h
      | some g =>
          simp only [hx, Option.bind_eq_bind, Option.bind_some] at h
          by_cases hempty : outs.isEmpty
          · simp only [hempty, ite_true] at h
            -- The circuit does nothing here; the executor at most updates the private state.
            have henv : s'.env = s.env ∧ s'.priv = s.priv ∧ s'.pub = s.pub ∧ s'.groups = s.groups := by
              by_cases hg : g = 1
              · simp only [hg, ite_true] at h
                cases hargs : Expr.evalList p s.env args with
                | none => simp [hargs] at h
                | some argVals =>
                    simp only [hargs, Option.bind_some] at h
                    cases hw : O.witness name argVals s.private_ s.ledger with
                    | none => simp [hw] at h
                    | some res =>
                        obtain ⟨vals, ps', ls'⟩ := res
                        simp only [hw, Option.bind_some] at h
                        by_cases hv : vals.isEmpty
                        · simp only [hv, ite_true, Option.pure_def, Option.some.injEq] at h
                          subst h
                          exact ⟨rfl, rfl, rfl, rfl⟩
                        · simp [hv] at h
              · simp only [hg, ite_false, Option.pure_def, Option.some.injEq] at h
                subst h
                exact ⟨rfl, rfl, rfl, rfl⟩
            obtain ⟨he, hp, hq, hgr⟩ := henv
            exact ⟨[], [], by simp [hp], by simp [hq], fun tp tq => by
              simp [Stmt.exec, hx, hempty, he, hgr]⟩
          · simp only [hempty, Bool.false_eq_true, ite_false] at h
            cases hb : asBool g with
            | none => simp [hb] at h
            | some active =>
                simp only [hb, Option.bind_some] at h
                cases active with
                | true =>
                    simp only [ite_true] at h
                    cases hargs : Expr.evalList p s.env args with
                    | none => simp [hargs] at h
                    | some argVals =>
                        simp only [hargs, Option.bind_some] at h
                        cases hw : O.witness name argVals s.private_ s.ledger with
                        | none => simp [hw] at h
                        | some res =>
                            obtain ⟨vals, ps', ls'⟩ := res
                            simp only [hw, Option.bind_some] at h
                            cases ha : assign s.env outs vals with
                            | none => simp [ha] at h
                            | some env' =>
                                simp only [ha, Option.bind_some, Option.pure_def,
                                  Option.some.injEq] at h
                                subst h
                                refine ⟨vals, [], rfl, by simp, fun tp tq => ?_⟩
                                simp [Stmt.exec, hx, hempty, hb, assign_readAll outs s.env vals env' ha tp]
                | false =>
                    simp only [Bool.false_eq_true, ite_false] at h
                    cases ha : assign s.env outs (outs.map fun _ => 0) with
                    | none => simp [ha] at h
                    | some env' =>
                        simp only [ha, Option.bind_some, Option.pure_def, Option.some.injEq] at h
                        subst h
                        refine ⟨[], [], by simp, by simp, fun tp tq => ?_⟩
                        simp [Stmt.exec, hx, hempty, hb, assign_zeros_readAll outs s.env env' ha tp]
  | ledger guard reads ops =>
      simp only [step] at h
      cases hx : guard.eval p s.env with
      | none => simp [hx] at h
      | some g =>
          simp only [hx, Option.bind_eq_bind, Option.bind_some] at h
          by_cases hempty : (reads.isEmpty && ops.isEmpty) = true
          · simp only [hempty, ite_true, Option.pure_def, Option.some.injEq] at h
            subst h
            exact ⟨[], [], by simp, by simp, fun tp tq => by simp [Stmt.exec, hx, hempty]⟩
          · simp only [hempty, Bool.false_eq_true, ite_false] at h
            cases hb : asBool g with
            | none => simp [hb] at h
            | some active =>
                simp only [hb, Option.bind_some] at h
                cases active with
                | true =>
                    simp only [ite_true] at h
                    cases hreq : request p s.env ops with
                    | none => simp [hreq] at h
                    | some req =>
                        simp only [hreq, Option.bind_some] at h
                        cases hl : O.ledger req s.ledger with
                        | none => simp [hl] at h
                        | some res =>
                            obtain ⟨vals, ls'⟩ := res
                            simp only [hl, Option.bind_some] at h
                            cases ha : assign s.env (reads.map fun v => (v, none)) vals with
                            | none => simp [ha] at h
                            | some env' =>
                                simp only [ha, Option.bind_some] at h
                                cases hg : ledgerGroups p env' true ops with
                                | none => simp [hg] at h
                                | some gs =>
                                    simp only [hg, Option.bind_some, Option.pure_def,
                                      Option.some.injEq] at h
                                    subst h
                                    refine ⟨[], vals, by simp, rfl, fun tp tq => ?_⟩
                                    simp [Stmt.exec, hx, hempty, hb, hg,
                                      assign_readAll _ s.env vals env' ha tq]
                | false =>
                    simp only [Bool.false_eq_true, ite_false] at h
                    cases ha : assign s.env (reads.map fun v => (v, none)) (reads.map fun _ => 0) with
                    | none => simp [ha] at h
                    | some env' =>
                        simp only [ha, Option.bind_some] at h
                        cases hg : ledgerGroups p env' false ops with
                        | none => simp [hg] at h
                        | some gs =>
                            simp only [hg, Option.bind_some, Option.pure_def, Option.some.injEq] at h
                            subst h
                            have ha' : assign s.env (reads.map fun v => (v, (none : Option Range)))
                                ((reads.map fun v => (v, (none : Option Range))).map fun _ => 0)
                                  = some env' := by
                              rw [List.map_map]; exact ha
                            refine ⟨[], [], by simp, by simp, fun tp tq => ?_⟩
                            simp [Stmt.exec, hx, hempty, hb, hg,
                              assign_zeros_readAll _ s.env env' ha' tq]

/-! ## A whole body -/

/-- The same for a list of statements: the semantics reads what the executor
    recorded, statement by statement. -/
theorem steps_sim (p : Prims) (O : Oracles ω σ) :
    ∀ (stmts : List Stmt) (s s' : State ω σ), steps p O stmts s = some s' →
      ∃ dp dq, s'.priv = s.priv ++ dp ∧ s'.pub = s.pub ++ dq ∧
        ∀ tp tq, execAll p stmts { env := s.env, priv := dp ++ tp, pub := dq ++ tq, groups := s.groups }
          = some { env := s'.env, priv := tp, pub := tq, groups := s'.groups }
  | [], s, s', h => by
      simp only [steps, Option.some.injEq] at h
      subst h
      exact ⟨[], [], by simp, by simp, fun tp tq => by simp [execAll]⟩
  | st :: rest, s, s', h => by
      simp only [steps] at h
      cases hst : step p O s st with
      | none => simp [hst] at h
      | some mid =>
          simp only [hst, Option.bind_eq_bind, Option.bind_some] at h
          obtain ⟨dp₁, dq₁, hp₁, hq₁, h₁⟩ := step_sim p O s mid st hst
          obtain ⟨dp₂, dq₂, hp₂, hq₂, h₂⟩ := steps_sim p O rest mid s' h
          refine ⟨dp₁ ++ dp₂, dq₁ ++ dq₂, by simp [hp₂, hp₁], by simp [hq₂, hq₁], fun tp tq => ?_⟩
          simp only [execAll, List.append_assoc, h₁ (dp₂ ++ tp) (dq₂ ++ tq), Option.bind_eq_bind,
            Option.bind_some]
          exact h₂ tp tq

/-! ## A whole call -/

/-- **A completed call is an accepted run.** If the executor completes a call,
    the circuit accepts the inputs with the private transcript and ledger reads
    the executor recorded, and yields the outputs and public inputs it recorded. -/
theorem run_accepted (p : Prims) (O : Oracles ω σ) (c : Circuit) (inputs : List Fr)
    (private_ : ω) (ledger : σ) (r : Result ω σ)
    (h : run p O c inputs private_ ledger = some r) :
    c.run p inputs r.priv r.pub = some { outputs := r.outputs, groups := r.groups } := by
  simp only [run] at h
  simp only [Circuit.run]
  cases henv : bindInputs (fun _ => 0) c.inputs inputs with
  | none => simp [henv] at h
  | some env =>
      simp only [henv, Option.bind_eq_bind, Option.bind_some] at h ⊢
      cases hs : steps p O c.body.toList { env, private_, ledger } with
      | none => simp [hs] at h
      | some s' =>
          simp only [hs, Option.bind_some] at h
          cases hout : Expr.evalList p s'.env c.outputs with
          | none => simp [hout] at h
          | some outputs =>
              simp only [hout, Option.bind_some, Option.pure_def, Option.some.injEq] at h
              subst h
              obtain ⟨dp, dq, hp, hq, hsim⟩ := steps_sim p O c.body.toList _ s' hs
              simp only [List.nil_append] at hp hq
              have := hsim [] []
              simp only [List.append_nil] at this
              simp only [hp, hq]
              rw [this]
              simp [hout]

/-- What the executor records on a circuit is accepted by the ZKIR emitted
    for that circuit, whichever passes produced it. -/
theorem run_accepted_by_emitted (p : Prims) (O : Oracles ω σ) (c : Circuit) (src : Zkir.IrSource)
    (hsrc : Emit.circuit c = .ok src) (inputs : List Fr) (private_ : ω) (ledger : σ)
    (r : Result ω σ) (h : run p O c inputs private_ ledger = some r) :
    src.run p inputs r.priv r.pub = some { outputs := r.outputs, groups := r.groups } := by
  rw [Emit.circuitCore_correct p _ src (Emit.circuit_eq_core _ src hsrc) inputs r.priv r.pub]
  exact Emit.pruned_run p c inputs r.priv r.pub _ (run_accepted p O _ inputs private_ ledger r h)

/-- **And so is accepted by the shipped ZKIR.** The executor interprets the
    optimized circuit; the ZKIR emitted from that circuit accepts what the
    executor recorded, with the same outputs and public inputs. -/
theorem run_accepted_by_zkir (p : Prims) (O : Oracles ω σ) (c : Circuit) (src : Zkir.IrSource)
    (hsrc : Emit.circuit c.optimize = .ok src) (inputs : List Fr) (private_ : ω) (ledger : σ)
    (r : Result ω σ) (h : run p O c.optimize inputs private_ ledger = some r) :
    src.run p inputs r.priv r.pub = some { outputs := r.outputs, groups := r.groups } :=
  run_accepted_by_emitted p O _ src hsrc inputs private_ ledger r h

end Damp.Exec
