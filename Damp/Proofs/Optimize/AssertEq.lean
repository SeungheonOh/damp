/-
Soundness of `Circuit.assertEq` (`Damp/Optimize/AssertEq.lean`).

An `assert` statement depends on its condition only through whether it
evaluates to 1 (`assert_exec`, `assert_step`), and `assertCond c` evaluates to
1 exactly when `c` does (`assertCond_one`). So every statement runs exactly as
before, in `Circuit.run` and in the executor, and the pass is sound
(`Circuit.assertEq_sound`); it touches no ledger statement, so it keeps
`checkLedger` (`Circuit.assertEq_checkLedger`).
-/
import Damp.Optimize.AssertEq
import Damp.Proofs.Optimize.Sound
import Damp.IR.LedgerCheck

namespace Damp.IR
open Damp.Zkir (Prims)

/-- A condition evaluates to 1 exactly when the value of `ofBool` is `true`. -/
theorem Fr.ofBool_eq_one (b : Bool) : Fr.ofBool b = 1 ↔ b = true := by
  cases b
  · constructor
    · intro h
      have h0 : Fr.ofBool false = 0 := rfl
      exact absurd (h0.symm.trans h) Fr.zero_ne_one
    · intro h; cases h
  · exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem assert_bind (o : Option Fr) {α : Type} (s : α) :
    (do let c ← o; let c ← asBool c; if c = true then pure s else none) = if o = some 1 then some s else none := by
  cases o with
  | none => simp
  | some x =>
      simp only [Option.bind_eq_bind, Option.bind_some, Option.some.injEq]
      unfold asBool
      by_cases h0 : x = 0
      · subst h0; simp [Fr.zero_ne_one]
      · by_cases h1 : x = 1
        · subst h1; simp [Fr.zero_ne_one.symm]
        · simp [h0, h1]

/-- `assertCond c` evaluates to 1 exactly when `c` does. -/
theorem assertCond_one (p : Prims) (env : Env) (c : Expr) :
    (assertCond c).eval p env = some 1 ↔ c.eval p env = some 1 := by
  unfold assertCond
  split
  · rename_i e k
    split
    · rename_i hk
      cases he : e.eval p env with
      | none => simp [Expr.eval, he]
      | some x => simp [Expr.eval, he, hk, Fr.ofBool_eq_one]
    · exact Iff.rfl
  · rename_i k e _
    split
    · rename_i hk
      cases he : e.eval p env with
      | none => simp [Expr.eval, he]
      | some x =>
          simp [Expr.eval, he, hk, Fr.ofBool_eq_one]
          exact ⟨fun h => h.symm, fun h => h.symm⟩
    · exact Iff.rfl
  · exact Iff.rfl

theorem ite_one_congr {α : Type} {p : Prims} {env : Env} (c : Expr) (a b : α) :
    (if (assertCond c).eval p env = some 1 then a else b) = (if c.eval p env = some 1 then a else b) := by
  by_cases h : c.eval p env = some 1
  · simp only [h, ((assertCond_one p env c).mpr h), ite_true]
  · have h' : ¬(assertCond c).eval p env = some 1 := fun h' => h ((assertCond_one p env c).mp h')
    simp only [h, h', ite_false]

theorem Stmt.assertEq_exec (p : Prims) (s : RunState) (st : Stmt) :
    st.assertEq.exec p s = st.exec p s := by
  cases st with
  | assert c msg =>
      simp only [Stmt.assertEq, Stmt.exec]
      rw [assert_bind, assert_bind, ite_one_congr]
  | _ => rfl

theorem Stmt.assertEq_step {ω σ : Type} (p : Prims) (O : Exec.Oracles ω σ) (s : Exec.State ω σ) (st : Stmt) :
    Exec.step p O s st.assertEq = Exec.step p O s st := by
  cases st with
  | assert c msg =>
      simp only [Stmt.assertEq, Exec.step]
      rw [assert_bind, assert_bind, ite_one_congr]
  | _ => rfl

theorem execAll_assertEq (p : Prims) :
    ∀ (stmts : List Stmt) (s : RunState), execAll p (stmts.map Stmt.assertEq) s = execAll p stmts s
  | [], _ => rfl
  | st :: rest, s => by
      simp only [List.map_cons, execAll, Stmt.assertEq_exec, execAll_assertEq p rest]

theorem steps_assertEq {ω σ : Type} (p : Prims) (O : Exec.Oracles ω σ) :
    ∀ (stmts : List Stmt) (s : Exec.State ω σ), Exec.steps p O (stmts.map Stmt.assertEq) s = Exec.steps p O stmts s
  | [], _ => rfl
  | st :: rest, s => by
      simp only [List.map_cons, Exec.steps, Stmt.assertEq_step, steps_assertEq p O rest]

/-- `Circuit.assertEq` does not change a run at all. -/
theorem Circuit.assertEq_run (p : Prims) (c : Circuit) (inputs priv pub : List Fr) :
    (Circuit.assertEq c).run p inputs priv pub = c.run p inputs priv pub := by
  simp only [Circuit.run, Circuit.assertEq, Array.toList_map, execAll_assertEq]

/-- ... nor what the executor does. -/
theorem Circuit.assertEq_exec {ω σ : Type} (p : Prims) (O : Exec.Oracles ω σ) (c : Circuit) (inputs : List Fr)
    (private_ : ω) (ledger : σ) :
    Exec.run p O (Circuit.assertEq c) inputs private_ ledger = Exec.run p O c inputs private_ ledger := by
  simp only [Exec.run, Circuit.assertEq, Array.toList_map, steps_assertEq]

theorem Circuit.assertEq_sound : Pass.Sound Circuit.assertEq :=
  ⟨fun p c i pr pu => by rw [Circuit.assertEq_run], fun p O c i w l => by rw [Circuit.assertEq_exec]⟩

theorem checkLedgerFrom_assertEq (name : String) :
    ∀ (i : Nat) (stmts : List Stmt), checkLedgerFrom name i stmts = .ok () →
      checkLedgerFrom name i (stmts.map Stmt.assertEq) = .ok ()
  | _, [], _ => rfl
  | i, st :: rest, h => by
      have hst : st.assertEq.ledgerProblem = st.ledgerProblem := by cases st <;> rfl
      cases hp : st.ledgerProblem with
      | some w => simp [checkLedgerFrom, hp] at h
      | none =>
          simp only [checkLedgerFrom, hp] at h
          simp only [List.map_cons, checkLedgerFrom, hst, hp]
          exact checkLedgerFrom_assertEq name (i + 1) rest h

theorem Circuit.assertEq_checkLedger (c : Circuit) (h : c.checkLedger = .ok ()) :
    (Circuit.assertEq c).checkLedger = .ok () := by
  simp only [Circuit.checkLedger, Circuit.assertEq, Array.toList_map] at h ⊢
  exact checkLedgerFrom_assertEq _ 0 _ h

end Damp.IR
