/-
The executor fails only when it must.

`Damp/Proofs/Executor.lean` shows that a call the executor completes is one
the circuit accepts. This file shows the other direction: if the executor
gives up, then either

* it could not get a usable answer from a witness or from the ledger
  (`Trouble`): the oracle refused, answered with the wrong number of values,
  or the question itself could not be formed; or
* no proof was possible anyway: the circuit rejects every pair of transcripts
  that begins with what the executor had recorded so far, followed by the
  answer it had just been given.

So the executor never abandons a call that could still have been proved from
the answers it was given.
-/
import Damp.Proofs.Executor

set_option linter.unusedSimpArgs false

namespace Damp.Exec
open Damp.IR
open Damp.Zkir (Prims Group Outcome)

variable {ω σ : Type}

/-- The executor could not get a usable answer for this statement: a question
    it had to ask could not be formed, was refused, or came back with the wrong
    number of values. -/
def Trouble (p : Prims) (O : Oracles ω σ) (s : State ω σ) : Stmt → Prop
  | .witness guard name args outs _ =>
      ∃ g, guard.eval p s.env = some g ∧
        ((outs.isEmpty = true ∧ g = 1) ∨ (outs.isEmpty = false ∧ asBool g = some true)) ∧
        (Expr.evalList p s.env args = none ∨
          ∃ argVals, Expr.evalList p s.env args = some argVals ∧
            (O.witness name argVals s.private_ s.ledger = none ∨
              ∃ vals ps ls, O.witness name argVals s.private_ s.ledger = some (vals, ps, ls) ∧
                vals.length ≠ outs.length))
  | .ledger guard reads ops =>
      ∃ g, guard.eval p s.env = some g ∧ (reads.isEmpty && ops.isEmpty) = false ∧
        asBool g = some true ∧
        (request p s.env ops = none ∨
          ∃ req, request p s.env ops = some req ∧
            (O.ledger req s.ledger = none ∨
              ∃ vals ls, O.ledger req s.ledger = some (vals, ls) ∧ vals.length ≠ reads.length))
  | _ => False

/-- What the oracle answered at this statement, if the executor asked and got
    an answer: a witness's values for the private transcript, the ledger's
    reads for the public one. Empty otherwise. -/
def answer (p : Prims) (O : Oracles ω σ) (s : State ω σ) : Stmt → List Fr × List Fr
  | .witness guard name args outs _ =>
      match guard.eval p s.env with
      | some g =>
          if outs.isEmpty then ([], [])
          else
            match asBool g with
            | some true =>
                match Expr.evalList p s.env args with
                | some argVals =>
                    match O.witness name argVals s.private_ s.ledger with
                    | some (vals, _) => (vals, [])
                    | none => ([], [])
                | none => ([], [])
            | _ => ([], [])
      | none => ([], [])
  | .ledger guard reads ops =>
      match guard.eval p s.env with
      | some g =>
          if reads.isEmpty && ops.isEmpty then ([], [])
          else
            match asBool g with
            | some true =>
                match request p s.env ops with
                | some req =>
                    match O.ledger req s.ledger with
                    | some (vals, _) => ([], vals)
                    | none => ([], [])
                | none => ([], [])
            | _ => ([], [])
      | none => ([], [])
  | _ => ([], [])

/-- The circuit rejects this statement on every pair of transcripts that begins
    with the oracle's answer. -/
def Rejects (p : Prims) (O : Oracles ω σ) (s : State ω σ) (st : Stmt) : Prop :=
  ∀ tp tq, st.exec p { env := s.env, priv := (answer p O s st).1 ++ tp,
                       pub := (answer p O s st).2 ++ tq, groups := s.groups } = none

/-! ## Answers the circuit rejects -/

/-- If values of the right number cannot be assigned, the circuit rejects any
    transcript that begins with them: one of them fails its range check. -/
theorem assign_none_readAll :
    ∀ (outs : List (Var × Option Range)) (env : Env) (vals : List Fr),
      assign env outs vals = none → vals.length = outs.length →
      ∀ tail, readAll true env outs (vals ++ tail) = none
  | [], env, [], h, _, _ => by simp [assign] at h
  | [], env, _ :: _, _, hlen, _ => by simp at hlen
  | _ :: _, env, [], _, hlen, _ => by simp at hlen
  | (v, range) :: rest, env, x :: xs, h, hlen, tail => by
      simp only [assign] at h
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [readAll, List.cons_append, Zkir.readOne, ite_true, Option.bind_eq_bind,
        Option.bind_some]
      cases range with
      | none =>
          simp only at h
          simp only [Option.pure_def, Option.bind_some]
          exact assign_none_readAll rest _ xs h hlen tail
      | some r =>
          simp only at h
          by_cases hh : r.holds x
          · simp only [hh, ite_true] at h
            simp only [hh, ite_true, Option.pure_def, Option.bind_some]
            exact assign_none_readAll rest _ xs h hlen tail
          · simp [hh]

/-- If the zeros of a skipped statement cannot be assigned, the circuit rejects
    whatever the transcripts are. -/
theorem assign_zeros_none :
    ∀ (outs : List (Var × Option Range)) (env : Env),
      assign env outs (outs.map fun _ => 0) = none →
      ∀ stream, readAll false env outs stream = none
  | [], env, h, _ => by simp [assign] at h
  | (v, range) :: rest, env, h, stream => by
      simp only [List.map_cons, assign] at h
      simp only [readAll, Zkir.readOne, Bool.false_eq_true, ite_false, Option.bind_eq_bind,
        Option.bind_some]
      cases range with
      | none =>
          simp only at h
          simp only [Option.pure_def, Option.bind_some]
          exact assign_zeros_none rest _ h stream
      | some r =>
          simp only at h
          by_cases hh : r.holds 0
          · simp only [hh, ite_true] at h
            simp only [hh, ite_true, Option.pure_def, Option.bind_some]
            exact assign_zeros_none rest _ h stream
          · simp [hh]

/-! ## One statement -/

/-- If the executor fails at a statement, it had trouble with an oracle, or the
    circuit rejects every transcript that begins with what the oracle answered. -/
theorem step_none (p : Prims) (O : Oracles ω σ) (s : State ω σ) (st : Stmt)
    (h : step p O s st = none) : Trouble p O s st ∨ Rejects p O s st := by
  unfold Rejects
  cases st with
  | bind v hint e =>
      refine .inr (fun tp tq => ?_)
      simp only [step] at h
      cases hx : e.eval p s.env with
      | none => simp [Stmt.exec, hx]
      | some x => simp [hx] at h
  | assert cond msg =>
      refine .inr (fun tp tq => ?_)
      simp only [step] at h
      cases hx : cond.eval p s.env with
      | none => simp [Stmt.exec, hx]
      | some x =>
          simp only [hx, Option.bind_eq_bind, Option.bind_some] at h
          cases hb : asBool x with
          | none => simp [Stmt.exec, hx, hb]
          | some b =>
              cases b with
              | false => simp [Stmt.exec, hx, hb]
              | true => simp [hb] at h
  | constrain e r =>
      refine .inr (fun tp tq => ?_)
      simp only [step] at h
      cases hx : e.eval p s.env with
      | none => simp [Stmt.exec, hx]
      | some x =>
          simp only [hx, Option.bind_eq_bind, Option.bind_some] at h
          by_cases hh : r.holds x
          · simp [hh] at h
          · simp [Stmt.exec, hx, hh]
  | witness guard name args outs shape =>
      simp only [step] at h
      cases hx : guard.eval p s.env with
      | none => exact .inr (fun tp tq => by simp [Stmt.exec, hx])
      | some g =>
          simp only [hx, Option.bind_eq_bind, Option.bind_some] at h
          by_cases hempty : outs.isEmpty
          · -- Nothing to read: only the oracle can make this fail.
            simp only [hempty, ite_true] at h
            by_cases hg : g = 1
            · simp only [hg, ite_true] at h
              left
              refine ⟨g, hx, .inl ⟨hempty, hg⟩, ?_⟩
              cases hargs : Expr.evalList p s.env args with
              | none => exact .inl rfl
              | some argVals =>
                  refine .inr ⟨argVals, rfl, ?_⟩
                  simp only [hargs, Option.bind_some] at h
                  cases hw : O.witness name argVals s.private_ s.ledger with
                  | none => exact .inl rfl
                  | some res =>
                      obtain ⟨vals, ps', ls'⟩ := res
                      simp only [hw, Option.bind_some] at h
                      refine .inr ⟨vals, ps', ls', rfl, ?_⟩
                      have hlen : outs.length = 0 := by
                        cases outs with
                        | nil => rfl
                        | cons _ _ => simp at hempty
                      by_cases hv : vals.isEmpty
                      · simp [hv] at h
                      · rw [hlen]
                        cases vals with
                        | nil => simp at hv
                        | cons _ _ => simp
            · simp [hg] at h
          · simp only [hempty, Bool.false_eq_true, ite_false] at h
            have hne : outs.isEmpty = false := by simpa using hempty
            cases hb : asBool g with
            | none => exact .inr (fun tp tq => by simp [Stmt.exec, hx, hempty, hb])
            | some active =>
                simp only [hb, Option.bind_some] at h
                cases active with
                | true =>
                    simp only [ite_true] at h
                    cases hargs : Expr.evalList p s.env args with
                    | none => exact .inl ⟨g, hx, .inr ⟨hne, hb⟩, .inl hargs⟩
                    | some argVals =>
                        simp only [hargs, Option.bind_some] at h
                        cases hw : O.witness name argVals s.private_ s.ledger with
                        | none => exact .inl ⟨g, hx, .inr ⟨hne, hb⟩, .inr ⟨argVals, hargs, .inl hw⟩⟩
                        | some res =>
                            obtain ⟨vals, ps', ls'⟩ := res
                            simp only [hw, Option.bind_some] at h
                            cases ha : assign s.env outs vals with
                            | some env' => simp [ha] at h
                            | none =>
                                by_cases hlen : vals.length = outs.length
                                · -- The witness answered, and its answer fails a range check.
                                  refine .inr (fun tp tq => ?_)
                                  have hans : answer p O s (.witness guard name args outs shape)
                                      = (vals, []) := by
                                    simp [answer, hx, hempty, hb, hargs, hw]
                                  rw [hans]
                                  simp [Stmt.exec, hx, hempty, hb,
                                    assign_none_readAll outs s.env vals ha hlen tp]
                                · exact .inl ⟨g, hx, .inr ⟨hne, hb⟩,
                                    .inr ⟨argVals, hargs, .inr ⟨vals, ps', ls', hw, hlen⟩⟩⟩
                | false =>
                    simp only [Bool.false_eq_true, ite_false] at h
                    cases ha : assign s.env outs (outs.map fun _ => 0) with
                    | some env' => simp [ha] at h
                    | none =>
                        refine .inr (fun tp tq => ?_)
                        have hans : answer p O s (.witness guard name args outs shape)
                            = ([], []) := by
                          simp [answer, hx, hempty, hb]
                        rw [hans]
                        simp [Stmt.exec, hx, hempty, hb, assign_zeros_none outs s.env ha tp]
  | ledger guard reads ops =>
      simp only [step] at h
      cases hx : guard.eval p s.env with
      | none => exact .inr (fun tp tq => by simp [Stmt.exec, hx])
      | some g =>
          simp only [hx, Option.bind_eq_bind, Option.bind_some] at h
          by_cases hempty : (reads.isEmpty && ops.isEmpty) = true
          · simp [hempty] at h
          · simp only [hempty, Bool.false_eq_true, ite_false] at h
            have hne : (reads.isEmpty && ops.isEmpty) = false := by simpa using hempty
            cases hb : asBool g with
            | none => exact .inr (fun tp tq => by simp [Stmt.exec, hx, hempty, hb])
            | some active =>
                simp only [hb, Option.bind_some] at h
                cases active with
                | true =>
                    simp only [ite_true] at h
                    cases hreq : request p s.env ops with
                    | none => exact .inl ⟨g, hx, hne, hb, .inl hreq⟩
                    | some req =>
                        simp only [hreq, Option.bind_some] at h
                        cases hl : O.ledger req s.ledger with
                        | none => exact .inl ⟨g, hx, hne, hb, .inr ⟨req, hreq, .inl hl⟩⟩
                        | some res =>
                            obtain ⟨vals, ls'⟩ := res
                            simp only [hl, Option.bind_some] at h
                            cases ha : assign s.env (reads.map fun v => (v, none)) vals with
                            | none =>
                                by_cases hlen : vals.length = reads.length
                                · refine .inr (fun tp tq => ?_)
                                  have hans : answer p O s (.ledger guard reads ops) = ([], vals) := by
                                    simp [answer, hx, hempty, hb, hreq, hl]
                                  rw [hans]
                                  have := assign_none_readAll _ s.env vals ha (by simpa using hlen) tq
                                  simp [Stmt.exec, hx, hempty, hb, this]
                                · exact .inl ⟨g, hx, hne, hb,
                                    .inr ⟨req, hreq, .inr ⟨vals, ls', hl, hlen⟩⟩⟩
                            | some env' =>
                                simp only [ha, Option.bind_some] at h
                                cases hg : ledgerGroups p env' true ops with
                                | some gs => simp [hg] at h
                                | none =>
                                    -- The ledger answered, and an operand then fails to evaluate.
                                    refine .inr (fun tp tq => ?_)
                                    have hans : answer p O s (.ledger guard reads ops) = ([], vals) := by
                                      simp [answer, hx, hempty, hb, hreq, hl]
                                    rw [hans]
                                    simp [Stmt.exec, hx, hempty, hb, hg,
                                      assign_readAll _ s.env vals env' ha tq]
                | false =>
                    simp only [Bool.false_eq_true, ite_false] at h
                    cases ha : assign s.env (reads.map fun v => (v, none)) (reads.map fun _ => 0) with
                    | none =>
                        have ha' : assign s.env (reads.map fun v => (v, (none : Option Range)))
                            ((reads.map fun v => (v, (none : Option Range))).map fun _ => 0) = none := by
                          rw [List.map_map]; exact ha
                        refine .inr (fun tp tq => ?_)
                        have hans : answer p O s (.ledger guard reads ops) = ([], []) := by
                          simp [answer, hx, hempty, hb]
                        rw [hans]
                        simp [Stmt.exec, hx, hempty, hb, assign_zeros_none _ s.env ha' tq]
                    | some env' =>
                        simp only [ha, Option.bind_some] at h
                        have ha' : assign s.env (reads.map fun v => (v, (none : Option Range)))
                            ((reads.map fun v => (v, (none : Option Range))).map fun _ => 0)
                              = some env' := by
                          rw [List.map_map]; exact ha
                        cases hg : ledgerGroups p env' false ops with
                        | some gs => simp [hg] at h
                        | none =>
                            refine .inr (fun tp tq => ?_)
                            have hans : answer p O s (.ledger guard reads ops) = ([], []) := by
                              simp [answer, hx, hempty, hb]
                            rw [hans]
                            simp [Stmt.exec, hx, hempty, hb, hg,
                              assign_zeros_readAll _ s.env env' ha' tq]

/-! ## A whole body -/

/-- The executor completed the statements before `st` and then stopped at it
    for a reason `Why`. -/
def StoppedAt (p : Prims) (O : Oracles ω σ) (stmts : List Stmt) (s : State ω σ)
    (Why : State ω σ → Stmt → Prop) : Prop :=
  ∃ pre st post mid, stmts = pre ++ st :: post ∧ steps p O pre s = some mid ∧ Why mid st

/-- If the executor fails in a list of statements, it stopped at one of them,
    either in trouble with an oracle or because the circuit rejects the answer. -/
theorem steps_none (p : Prims) (O : Oracles ω σ) :
    ∀ (stmts : List Stmt) (s : State ω σ), steps p O stmts s = none →
      StoppedAt p O stmts s (fun mid st => Trouble p O mid st ∨ Rejects p O mid st)
  | [], s, h => by simp [steps] at h
  | st :: rest, s, h => by
      simp only [steps] at h
      cases hst : step p O s st with
      | none => exact ⟨[], st, rest, s, rfl, rfl, step_none p O s st hst⟩
      | some mid =>
          simp only [hst, Option.bind_eq_bind, Option.bind_some] at h
          obtain ⟨pre, st', post, mid', heq, hpre, hwhy⟩ := steps_none p O rest mid h
          exact ⟨st :: pre, st', post, mid', by simp [heq], by simp [steps, hst, hpre], hwhy⟩

/-- Running two lists of statements in a row. -/
theorem execAll_append (p : Prims) :
    ∀ (a b : List Stmt) (s : RunState),
      execAll p (a ++ b) s = (execAll p a s).bind (execAll p b)
  | [], b, s => rfl
  | st :: a, b, s => by
      simp only [List.cons_append, execAll]
      cases st.exec p s with
      | none => rfl
      | some s' => simp [execAll_append p a b s']

/-! ## A whole call -/

/-- Why a call failed. -/
inductive Failure (p : Prims) (O : Oracles ω σ) (c : Circuit) (inputs : List Fr)
    (private_ : ω) (ledger : σ) : Prop where
  /-- The inputs are not the circuit's: it rejects them whatever the transcripts. -/
  | inputs (h : ∀ priv pub, c.run p inputs priv pub = none)
  /-- A witness or the ledger gave no usable answer at statement `st`, after
      the statements `pre` had completed. -/
  | trouble (env : Env) (pre : List Stmt) (st : Stmt) (post : List Stmt) (mid : State ω σ)
      (henv : bindInputs (fun _ => 0) c.inputs inputs = some env)
      (hbody : c.body.toList = pre ++ st :: post)
      (hpre : steps p O pre { env, private_, ledger } = some mid)
      (h : Trouble p O mid st)
  /-- The circuit rejects every private transcript and every sequence of ledger
      reads that begin with what the executor had recorded (`mid.priv`,
      `mid.pub`) followed by what the oracle then answered at statement `st`. -/
  | rejected (env : Env) (pre : List Stmt) (st : Stmt) (post : List Stmt) (mid : State ω σ)
      (henv : bindInputs (fun _ => 0) c.inputs inputs = some env)
      (hbody : c.body.toList = pre ++ st :: post)
      (hpre : steps p O pre { env, private_, ledger } = some mid)
      (h : ∀ tp tq, c.run p inputs (mid.priv ++ (answer p O mid st).1 ++ tp)
                                    (mid.pub ++ (answer p O mid st).2 ++ tq) = none)
  /-- Every statement completed, and the circuit rejects everything that begins
      with the complete record: an output could not be evaluated. -/
  | outputs (env : Env) (s' : State ω σ)
      (henv : bindInputs (fun _ => 0) c.inputs inputs = some env)
      (hbody : steps p O c.body.toList { env, private_, ledger } = some s')
      (h : ∀ tp tq, c.run p inputs (s'.priv ++ tp) (s'.pub ++ tq) = none)

/-- **The executor fails only when it must.** If a call fails, then the
    executor had trouble getting a usable answer from a witness or the ledger,
    or the circuit rejects every transcript that begins with exactly what the
    executor had recorded and been answered: no proof was possible. -/
theorem run_none (p : Prims) (O : Oracles ω σ) (c : Circuit) (inputs : List Fr)
    (private_ : ω) (ledger : σ) (h : run p O c inputs private_ ledger = none) :
    Failure p O c inputs private_ ledger := by
  simp only [run] at h
  cases henv : bindInputs (fun _ => 0) c.inputs inputs with
  | none => exact .inputs (fun priv pub => by simp [Circuit.run, henv])
  | some env =>
      simp only [henv, Option.bind_eq_bind, Option.bind_some] at h
      cases hs : steps p O c.body.toList { env, private_, ledger } with
      | none =>
          obtain ⟨pre, st, post, mid, hbody, hpre, hwhy⟩ := steps_none p O c.body.toList _ hs
          rcases hwhy with ht | hrej
          · exact .trouble env pre st post mid henv hbody hpre ht
          · refine .rejected env pre st post mid henv hbody hpre (fun tp tq => ?_)
            obtain ⟨dp, dq, hp, hq, hsim⟩ := steps_sim p O pre _ mid hpre
            simp only [List.nil_append] at hp hq
            simp only [Circuit.run, henv, Option.bind_eq_bind, Option.bind_some, hbody,
              execAll_append, hp, hq, List.append_assoc]
            have := hsim ((answer p O mid st).1 ++ tp) ((answer p O mid st).2 ++ tq)
            rw [this]
            simp only [Option.bind_some, execAll]
            rw [hrej tp tq]
            rfl
      | some s' =>
          simp only [hs, Option.bind_some] at h
          cases hout : Expr.evalList p s'.env c.outputs with
          | some outputs => simp [hout] at h
          | none =>
              refine .outputs env s' henv hs (fun tp tq => ?_)
              obtain ⟨dp, dq, hp, hq, hsim⟩ := steps_sim p O c.body.toList _ s' hs
              simp only [List.nil_append] at hp hq
              simp only [Circuit.run, henv, Option.bind_eq_bind, Option.bind_some, hp, hq]
              rw [hsim tp tq]
              simp [hout]

end Damp.Exec
