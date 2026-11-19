/-
Soundness of `Circuit.commuteOpt` (`Damp/Optimize/Commute.lean`).

Swapping the operands of `add`, `mul` or `eq` preserves `Expr.eval` exactly:
the result fails when either operand does, in either order, and the field
operations and equality are commutative. So `Expr.commute` preserves
evaluation (`Expr.commute_eval`), `Circuit.mapExprs Expr.commute` is sound
(`Circuit.mapExprs_sound`), and so is the choice between it and the identity
(`Circuit.commuteOpt_sound`). Both keep `checkLedger`.
-/
import Damp.Optimize.Commute
import Damp.Proofs.Optimize.Forward

namespace Damp.IR
open Damp.Zkir (Prims)

section
variable (p : Prims) (env : Env)

theorem add_swap_eval (a b : Expr) : (Expr.add b a).eval p env = (Expr.add a b).eval p env := by
  cases ha : a.eval p env <;> cases hb : b.eval p env <;>
    simp [Expr.eval, ha, hb, Algebra.fr_add_comm]

theorem mul_swap_eval (a b : Expr) : (Expr.mul b a).eval p env = (Expr.mul a b).eval p env := by
  cases ha : a.eval p env <;> cases hb : b.eval p env <;>
    simp [Expr.eval, ha, hb, Algebra.fr_mul_comm]

theorem eq_swap_eval (a b : Expr) : (Expr.eq b a).eval p env = (Expr.eq a b).eval p env := by
  cases ha : a.eval p env <;> cases hb : b.eval p env <;> simp [Expr.eval, ha, hb]
  rename_i x y
  by_cases h : x = y
  · subst h; rfl
  · simp [h, Ne.symm h]

theorem commuteNode_eval (tag : UInt64) (mk : Expr → Expr → Expr)
    (hmk : ∀ a b : Expr, (mk b a).eval p env = (mk a b).eval p env) (a b : Expr × UInt64) :
    (commuteNode tag mk a b).1.eval p env = (mk a.1 b.1).eval p env := by
  unfold commuteNode
  split
  · exact hmk a.1 b.1
  · rfl

mutual
theorem Expr.commuteK_eval : ∀ e : Expr, e.commuteK.1.eval p env = e.eval p env
  | .add a b => by
      simp only [Expr.commuteK]
      rw [commuteNode_eval p env 3 .add (add_swap_eval p env)]
      simp only [Expr.eval, Expr.commuteK_eval a, Expr.commuteK_eval b]
  | .mul a b => by
      simp only [Expr.commuteK]
      rw [commuteNode_eval p env 4 .mul (mul_swap_eval p env)]
      simp only [Expr.eval, Expr.commuteK_eval a, Expr.commuteK_eval b]
  | .eq a b => by
      simp only [Expr.commuteK]
      rw [commuteNode_eval p env 5 .eq (eq_swap_eval p env)]
      simp only [Expr.eval, Expr.commuteK_eval a, Expr.commuteK_eval b]
  | .neg a => by simp only [Expr.commuteK, Expr.eval, Expr.commuteK_eval a]
  | .lt bits a b => by simp only [Expr.commuteK, Expr.eval, Expr.commuteK_eval a, Expr.commuteK_eval b]
  | .select c a b => by
      simp only [Expr.commuteK, Expr.eval, Expr.commuteK_eval c, Expr.commuteK_eval a, Expr.commuteK_eval b]
  | .divmod quot bits a => by simp only [Expr.commuteK, Expr.eval, Expr.commuteK_eval a]
  | .hash xs => by simp only [Expr.commuteK, Expr.eval, Expr.commuteKList_eval xs]
  | .phash high align xs => by simp only [Expr.commuteK, Expr.eval, Expr.commuteKList_eval xs]
  | .disclose a => by simp only [Expr.commuteK, Expr.eval, Expr.commuteK_eval a]
  | .var _ => rfl
  | .const _ => rfl
  | .invalid _ => rfl
theorem Expr.commuteKList_eval : ∀ xs : List Expr,
    Expr.evalList p env (Expr.commuteKList xs).1 = Expr.evalList p env xs
  | [] => rfl
  | x :: xs => by
      simp only [Expr.commuteKList, Expr.evalList, Expr.commuteK_eval x, Expr.commuteKList_eval xs]
end

end

theorem Expr.commute_eval : EvalPreserving Expr.commute := fun p env e => Expr.commuteK_eval p env e

theorem Circuit.commuteOpt_sound : Pass.Sound Circuit.commuteOpt :=
  Pass.Sound.choose (Circuit.mapExprs_sound Expr.commute_eval) Pass.Sound.id _

theorem Circuit.commuteOpt_checkLedger (c : Circuit) (h : c.checkLedger = .ok ()) :
    (Circuit.commuteOpt c).checkLedger = .ok () := by
  simp only [Circuit.commuteOpt, Pass.choose]
  split
  · exact Circuit.mapExprs_checkLedger _ c h
  · exact h

end Damp.IR
