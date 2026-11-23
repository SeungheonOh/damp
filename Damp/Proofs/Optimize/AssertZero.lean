/-
Soundness of `Circuit.assertZero` (`Damp/Optimize/AssertZero.lean`).

`eqDiff a b` evaluates exactly when `a` and `b` do, and to 0 exactly when
they are equal (`eqDiff_zero`). So `constrain (eqDiff a b) zero` passes and
fails on the same runs as `assert (a == b)` (`Stmt.assertZero_exec`,
`Stmt.assertZero_step`), every other statement is untouched, and the pass is
sound (`Circuit.assertZero_sound`). It changes no ledger statement, so it
keeps `checkLedger` (`Circuit.assertZero_checkLedger`).
-/
import Damp.Optimize.AssertZero
import Damp.Proofs.Optimize.AssertEq
import Damp.Proofs.Optimize.Algebra

namespace Damp.IR
open Damp.Zkir (Prims)

theorem fr_add_neg_eq_zero (x y : Fr) : x + -y = 0 ↔ x = y := by
  rw [Algebra.fr_add_eq_iff]
  show x = 0 + - -y ↔ x = y
  rw [Fr.neg_neg, Fr.zero_add]

theorem Expr.asConst_eq {e : Expr} {k : Int} (h : e.asConst = some k) : e = .const k := by
  cases e <;> simp_all [Expr.asConst]

theorem negConst_eval (p : Prims) (env : Env) (k : Int) : (negConst k).eval p env = some (-(Fr.ofInt k)) := by
  simp only [negConst, Expr.eval, Fr.ofInt_ofNat_val]

/-- `subConst e k` evaluates when `e` does, to 0 exactly when `e` is `k`. -/
theorem subConst_eval (p : Prims) (env : Env) (e : Expr) (k : Int) :
    ((subConst e k).eval p env).map (fun x => decide (x = 0)) = (e.eval p env).map (fun x => decide (x = Fr.ofInt k)) := by
  unfold subConst
  split
  · rename_i hk
    cases e.eval p env <;> simp [hk]
  · cases he : e.eval p env with
    | none => simp [Expr.eval, he]
    | some x => simp [Expr.eval, he, negConst_eval, fr_add_neg_eq_zero]

/-- `eqDiff a b` evaluates exactly when `a` and `b` do, to 0 exactly when they are equal. -/
theorem eqDiff_zero (p : Prims) (env : Env) (a b : Expr) :
    ((eqDiff a b).eval p env).map (fun x => decide (x = 0)) =
      (do let x ← a.eval p env; let y ← b.eval p env; pure (decide (x = y))) := by
  unfold eqDiff
  cases hb : b.asConst with
  | some k =>
      have : b = .const k := Expr.asConst_eq hb
      subst this
      simp only [subConst_eval]
      cases a.eval p env <;> simp [Expr.eval]
  | none =>
  cases ha' : a.asConst with
  | some k =>
      have : a = .const k := Expr.asConst_eq ha'
      subst this
      simp only [subConst_eval]
      cases b.eval p env <;> simp [Expr.eval, eq_comm]
  | none =>
    cases ha : a.eval p env with
    | none => simp [Expr.eval, ha]
    | some x =>
        cases hb : b.eval p env with
        | none => simp [Expr.eval, ha, hb]
        | some y => simp [Expr.eval, ha, hb, fr_add_neg_eq_zero]

/-- A `constrain e zero` passes exactly when `e` evaluates to 0. -/
theorem constrain_zero_bind (o : Option Fr) {α : Type} (s : α) :
    (do let x ← o; if Range.holds x .zero = true then pure s else none) =
      if o.map (fun x => decide (x = 0)) = some true then some s else none := by
  cases o with
  | none => simp
  | some x => by_cases h : x = 0 <;> simp [Range.holds, h]

theorem assertZero_cond (p : Prims) (env : Env) (a b : Expr) :
    ((eqDiff a b).eval p env).map (fun x => decide (x = 0)) = some true ↔ (Expr.eq a b).eval p env = some 1 := by
  rw [eqDiff_zero]
  cases ha : a.eval p env with
  | none => simp [Expr.eval, ha]
  | some x =>
      cases hb : b.eval p env with
      | none => simp [Expr.eval, ha, hb]
      | some y => simp [Expr.eval, ha, hb, Fr.ofBool_eq_one]

theorem assertZero_ite {α : Type} (p : Prims) (env : Env) (a b : Expr) (s : α) :
    (if ((eqDiff a b).eval p env).map (fun x => decide (x = 0)) = some true then some s else none) =
      (if (Expr.eq a b).eval p env = some 1 then some s else none) := by
  by_cases h : (Expr.eq a b).eval p env = some 1
  · simp only [(assertZero_cond p env a b).mpr h, h, ite_true]
  · have h' : ¬((eqDiff a b).eval p env).map (fun x => decide (x = 0)) = some true := fun h' => h ((assertZero_cond p env a b).mp h')
    simp only [h, h', ite_false]

theorem Stmt.assertZero_exec (p : Prims) (s : RunState) (st : Stmt) :
    st.assertZero.exec p s = st.exec p s := by
  unfold Stmt.assertZero
  split
  · rename_i a b msg
    simp only [Stmt.exec]
    rw [constrain_zero_bind, assert_bind, assertZero_ite]
  · rfl

theorem Stmt.assertZero_step {ω σ : Type} (p : Prims) (O : Exec.Oracles ω σ) (s : Exec.State ω σ) (st : Stmt) :
    Exec.step p O s st.assertZero = Exec.step p O s st := by
  unfold Stmt.assertZero
  split
  · rename_i a b msg
    simp only [Exec.step]
    rw [constrain_zero_bind, assert_bind, assertZero_ite]
  · rfl

theorem execAll_assertZero (p : Prims) :
    ∀ (stmts : List Stmt) (s : RunState), execAll p (stmts.map Stmt.assertZero) s = execAll p stmts s
  | [], _ => rfl
  | st :: rest, s => by
      simp only [List.map_cons, execAll, Stmt.assertZero_exec, execAll_assertZero p rest]

theorem steps_assertZero {ω σ : Type} (p : Prims) (O : Exec.Oracles ω σ) :
    ∀ (stmts : List Stmt) (s : Exec.State ω σ),
      Exec.steps p O (stmts.map Stmt.assertZero) s = Exec.steps p O stmts s
  | [], _ => rfl
  | st :: rest, s => by
      simp only [List.map_cons, Exec.steps, Stmt.assertZero_step, steps_assertZero p O rest]

/-- `Circuit.assertZero` does not change a run at all. -/
theorem Circuit.assertZero_run (p : Prims) (c : Circuit) (inputs priv pub : List Fr) :
    (Circuit.assertZero c).run p inputs priv pub = c.run p inputs priv pub := by
  simp only [Circuit.run, Circuit.assertZero, Array.toList_map, execAll_assertZero]

/-- ... nor what the executor does. -/
theorem Circuit.assertZero_exec {ω σ : Type} (p : Prims) (O : Exec.Oracles ω σ) (c : Circuit)
    (inputs : List Fr) (private_ : ω) (ledger : σ) :
    Exec.run p O (Circuit.assertZero c) inputs private_ ledger = Exec.run p O c inputs private_ ledger := by
  simp only [Exec.run, Circuit.assertZero, Array.toList_map, steps_assertZero]

theorem Circuit.assertZero_sound : Pass.Sound Circuit.assertZero :=
  ⟨fun p c i pr pu => by rw [Circuit.assertZero_run], fun p O c i w l => by rw [Circuit.assertZero_exec]⟩

theorem checkLedgerFrom_assertZero (name : String) :
    ∀ (i : Nat) (stmts : List Stmt), checkLedgerFrom name i stmts = .ok () →
      checkLedgerFrom name i (stmts.map Stmt.assertZero) = .ok ()
  | _, [], _ => rfl
  | i, st :: rest, h => by
      have hst : st.assertZero.ledgerProblem = st.ledgerProblem := by
        unfold Stmt.assertZero; split <;> rfl
      cases hp : st.ledgerProblem with
      | some w => simp [checkLedgerFrom, hp] at h
      | none =>
          simp only [checkLedgerFrom, hp] at h
          simp only [List.map_cons, checkLedgerFrom, hst, hp]
          exact checkLedgerFrom_assertZero name (i + 1) rest h

theorem Circuit.assertZero_checkLedger (c : Circuit) (h : c.checkLedger = .ok ()) :
    (Circuit.assertZero c).checkLedger = .ok () := by
  simp only [Circuit.checkLedger, Circuit.assertZero, Array.toList_map] at h ⊢
  exact checkLedgerFrom_assertZero _ 0 _ h

end Damp.IR
