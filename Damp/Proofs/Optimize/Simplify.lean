/-
Correctness of the optimizer (`Damp/Optimize/Simplify.lean`) against the partial
semantics of `Damp/IR/Semantics.lean`.

* `Expr.simp_eval`: simplifying an expression does not change its value, and in
  particular does not change whether it has one.
* `Circuit.simplify_correct`: optimizing a circuit does not change what a run
  produces that anyone can observe: whether it succeeds, its outputs, and the
  public inputs of the on-chain instructions that ran.
-/
import Damp.Optimize.Simplify

set_option linter.unusedSimpArgs false

namespace Damp.Zkir

/-- What a run produces that anyone can observe: the outputs, and the public
    inputs of the on-chain instructions that actually ran. An instruction that
    did not run contributes an all-zero group that carries no information. -/
def Outcome.observable (o : Outcome) : List Fr × List Fr := (o.outputs, o.activeInputs)

end Damp.Zkir

namespace Damp.IR
open Damp.Zkir (Prims fitsBits)

/-! ## Small facts -/

/-- A boolean as a field element is 0 or 1. -/
theorem Fr.ofBool_zero_or_one (b : Bool) : Fr.ofBool b = 0 ∨ Fr.ofBool b = 1 := by
  cases b <;> simp [Fr.ofBool]

/-- `asBool` succeeds exactly on 0 and 1. -/
theorem asBool_of_zero_or_one {x : Fr} (h : x = 0 ∨ x = 1) : ∃ b, asBool x = some b ∧ Fr.ofBool b = x := by
  rcases h with h | h <;> subst h
  · exact ⟨false, by simp [asBool], rfl⟩
  · exact ⟨true, by simp [asBool, Fr.zero_ne_one.symm], rfl⟩

/-- The value of a canonical constant is the field element it was made from. -/
theorem canon_eval (p : Prims) (env : Env) (x : Fr) : (canon x).eval p env = some x := by
  show some (Fr.ofInt (Int.ofNat x.val)) = some x
  rw [Fr.ofInt_ofNat_val]

/-! ## What cannot fail -/

/-- The variables in `bools` hold 0 or 1. -/
def BoolsHold (env : Env) (bools : List Var) : Prop := ∀ v ∈ bools, env v = 0 ∨ env v = 1

section Total
set_option linter.unusedSectionVars false
variable (p : Prims) (env : Env) (bools : List Var) (hb : BoolsHold env bools)
include hb

/-- An expression that `isBool` says is 0 or 1 is 0 or 1 when it has a value. -/
theorem Expr.isBool_eval : ∀ (e : Expr) (x : Fr), e.isBool bools = true → e.eval p env = some x →
    x = 0 ∨ x = 1
  | .var v, x, h, he => by
      simp only [Expr.isBool, List.contains_iff_mem] at h
      simp only [Expr.eval, Option.some.injEq] at he
      subst he; exact hb v h
  | .const c, x, h, he => by
      simp only [Expr.isBool, Bool.or_eq_true, beq_iff_eq] at h
      simp only [Expr.eval, Option.some.injEq] at he
      subst he
      rcases h with h | h <;> subst h
      · exact Or.inl rfl
      · exact Or.inr rfl
  | .lt bits a b, x, _, he => by
      simp only [Expr.eval, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at he
      obtain ⟨_, _, _, _, he⟩ := he
      split at he
      · simp only [Option.some.injEq] at he; subst he; exact Fr.ofBool_zero_or_one _
      · cases he
  | .eq a b, x, _, he => by
      simp only [Expr.eval, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at he
      obtain ⟨_, _, _, _, he⟩ := he
      simp only [Option.some.injEq] at he; subst he; exact Fr.ofBool_zero_or_one _
  | .select c a b, x, h, he => by
      simp only [Expr.isBool, Bool.and_eq_true] at h
      simp only [Expr.eval, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at he
      obtain ⟨_, _, xa, ha, xb, hb', bc, _, he⟩ := he
      simp only [Option.some.injEq] at he
      subst he
      cases bc
      · exact Expr.isBool_eval b xb h.2 hb'
      · exact Expr.isBool_eval a xa h.1 ha
  | .disclose e, x, h, he => by
      simp only [Expr.isBool] at h
      simp only [Expr.eval] at he
      exact Expr.isBool_eval e x h he
  | .add .., _, h, _ | .mul .., _, h, _ | .neg _, _, h, _ | .hash _, _, h, _
  | .phash .., _, h, _ | .invalid _, _, h, _ | .divmod .., _, h, _ => by simp [Expr.isBool] at h

mutual
/-- An expression that `total` says cannot fail has a value. -/
theorem Expr.total_eval : ∀ e : Expr, e.total bools = true → ∃ x, e.eval p env = some x
  | .var v, _ => ⟨env v, rfl⟩
  | .const c, _ => ⟨_, rfl⟩
  | .add a b, h => by
      simp only [Expr.total, Bool.and_eq_true] at h
      obtain ⟨x, hx⟩ := Expr.total_eval a h.1
      obtain ⟨y, hy⟩ := Expr.total_eval b h.2
      exact ⟨x + y, by simp [Expr.eval, Option.bind_eq_bind, Option.pure_def, hx, hy]⟩
  | .mul a b, h => by
      simp only [Expr.total, Bool.and_eq_true] at h
      obtain ⟨x, hx⟩ := Expr.total_eval a h.1
      obtain ⟨y, hy⟩ := Expr.total_eval b h.2
      exact ⟨x * y, by simp [Expr.eval, Option.bind_eq_bind, Option.pure_def, hx, hy]⟩
  | .eq a b, h => by
      simp only [Expr.total, Bool.and_eq_true] at h
      obtain ⟨x, hx⟩ := Expr.total_eval a h.1
      obtain ⟨y, hy⟩ := Expr.total_eval b h.2
      exact ⟨Fr.ofBool (decide (x = y)), by simp [Expr.eval, Option.bind_eq_bind, Option.pure_def, hx, hy]⟩
  | .neg a, h => by
      simp only [Expr.total] at h
      obtain ⟨x, hx⟩ := Expr.total_eval a h
      exact ⟨-x, by simp [Expr.eval, Option.bind_eq_bind, Option.pure_def, hx]⟩
  | .divmod quot bits a, h => by
      simp only [Expr.total, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨x, hx⟩ := Expr.total_eval a h.2
      exact ⟨Fr.ofNat (if quot then x.val / 2 ^ bits else x.val % 2 ^ bits),
        by simp [Expr.eval, Option.bind_eq_bind, Option.pure_def, hx, h.1]⟩
  | .disclose a, h => by
      simp only [Expr.total] at h
      obtain ⟨x, hx⟩ := Expr.total_eval a h
      exact ⟨x, by simp [Expr.eval, hx]⟩
  | .select c a b, h => by
      simp only [Expr.total, Bool.and_eq_true] at h
      obtain ⟨⟨⟨hcb, hc⟩, ha⟩, hb'⟩ := h
      obtain ⟨xc, hxc⟩ := Expr.total_eval c hc
      obtain ⟨x, hx⟩ := Expr.total_eval a ha
      obtain ⟨y, hy⟩ := Expr.total_eval b hb'
      obtain ⟨bc, hbc, _⟩ := asBool_of_zero_or_one (Expr.isBool_eval p env bools hb c xc hcb hxc)
      exact ⟨if bc then x else y, by simp [Expr.eval, Option.bind_eq_bind, Option.pure_def, hxc, hx, hy, hbc]⟩
  | .hash xs, h => by
      simp only [Expr.total] at h
      obtain ⟨ys, hys⟩ := Expr.totalList_eval xs h
      exact ⟨p.transientHash ys, by simp [Expr.eval, Option.bind_eq_bind, Option.pure_def, hys]⟩
  | .lt .., h | .phash .., h | .invalid _, h => by simp [Expr.total] at h
/-- A list of expressions that `totalList` says cannot fail has values. -/
theorem Expr.totalList_eval : ∀ xs : List Expr, Expr.totalList bools xs = true →
    ∃ ys, Expr.evalList p env xs = some ys
  | [], _ => ⟨[], rfl⟩
  | x :: xs, h => by
      simp only [Expr.totalList, Bool.and_eq_true] at h
      obtain ⟨y, hy⟩ := Expr.total_eval x h.1
      obtain ⟨ys, hys⟩ := Expr.totalList_eval xs h.2
      exact ⟨y :: ys, by simp [Expr.evalList, Option.bind_eq_bind, Option.pure_def, hy, hys]⟩
end

end Total

/-- Every variable is 0 or 1 among none. -/
theorem boolsHold_nil (env : Env) : BoolsHold env [] := fun _ h => nomatch h

/-! ## Expression simplification -/

section Simp
variable (p : Prims) (env : Env)

/-- `mkAdd` computes the sum, failing exactly when the sum does. -/
theorem mkAdd_eval (a b : Expr) : (mkAdd a b).eval p env = (Expr.add a b).eval p env := by
  unfold mkAdd
  split <;> simp [Expr.eval, Option.bind_eq_bind, Option.pure_def, canon_eval, Fr.ofInt_zero,
    Fr.add_zero, Fr.zero_add]

/-- `mkMul` computes the product, failing exactly when the product does. -/
theorem mkMul_eval (a b : Expr) : (mkMul a b).eval p env = (Expr.mul a b).eval p env := by
  unfold mkMul
  split
  · simp [Expr.eval, Option.bind_eq_bind, Option.pure_def, canon_eval]
  · split
    · next h =>
      obtain ⟨x, hx⟩ := Expr.total_eval p env [] (boolsHold_nil env) _ h
      simp [Expr.eval, Option.bind_eq_bind, Option.pure_def, hx, Fr.ofInt_zero, Fr.zero_mul]
    · rfl
  · split
    · next h =>
      obtain ⟨x, hx⟩ := Expr.total_eval p env [] (boolsHold_nil env) _ h
      simp [Expr.eval, Option.bind_eq_bind, Option.pure_def, hx, Fr.ofInt_zero, Fr.mul_zero]
    · rfl
  all_goals simp [Expr.eval, Option.bind_eq_bind, Option.pure_def, Fr.ofInt_one, Fr.mul_one,
    Fr.one_mul]

/-- `mkNeg` computes the negation, failing exactly when it does. -/
theorem mkNeg_eval (a : Expr) : (mkNeg a).eval p env = (Expr.neg a).eval p env := by
  unfold mkNeg
  split
  · simp [Expr.eval, Option.bind_eq_bind, Option.pure_def, canon_eval]
  · rename_i e
    simp only [Expr.eval, Option.bind_eq_bind, Option.pure_def]
    cases e.eval p env <;> simp [Fr.neg_neg]
  · rfl

/-- `mkLt` folds a comparison of constants only when the comparison succeeds. -/
theorem mkLt_eval (bits : Nat) (a b : Expr) :
    (mkLt bits a b).eval p env = (Expr.lt bits a b).eval p env := by
  unfold mkLt
  split
  · split
    · rename_i h
      simp only [Bool.and_eq_true] at h
      simp [Expr.eval, Option.bind_eq_bind, Option.pure_def, canon_eval, h]
    · rfl
  · rfl

/-- `mkEq` replaces `e == e` by 1 only when `e` cannot fail. -/
theorem mkEq_eval (a b : Expr) : (mkEq a b).eval p env = (Expr.eq a b).eval p env := by
  unfold mkEq
  split
  · simp [Expr.eval, Option.bind_eq_bind, Option.pure_def, canon_eval]
  · split
    · rename_i h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, ht⟩ := h
      obtain ⟨x, hx⟩ := Expr.total_eval p env [] (boolsHold_nil env) a ht
      simp [Expr.eval, Option.bind_eq_bind, Option.pure_def, hx, Fr.ofInt_one, Fr.ofBool]
    · rfl

/-- `asBool` of 0 and 1. -/
theorem asBool_zero : asBool 0 = some false := by simp [asBool]
theorem asBool_one : asBool 1 = some true := by simp [asBool, Fr.zero_ne_one.symm]

/-- `mkSelectDistinct` picks a branch only when the other cannot fail. -/
theorem mkSelectDistinct_eval (c a b : Expr) :
    (mkSelectDistinct c a b).eval p env = (Expr.select c a b).eval p env := by
  unfold mkSelectDistinct
  split
  · rename_i k
    split
    · rename_i h
      obtain ⟨h1, hbt⟩ := h
      obtain ⟨y, hy⟩ := Expr.total_eval p env [] (boolsHold_nil env) b hbt
      simp only [Expr.eval, Option.bind_eq_bind, Option.pure_def, h1, hy]
      cases a.eval p env <;> rfl
    · split
      · rename_i h
        obtain ⟨h0, hat⟩ := h
        obtain ⟨x, hx⟩ := Expr.total_eval p env [] (boolsHold_nil env) a hat
        simp only [Expr.eval, Option.bind_eq_bind, Option.pure_def, h0, hx]
        cases b.eval p env <;> rfl
      · rfl
  · rename_i s
    simp only [Expr.eval, Option.bind_eq_bind, Option.pure_def, Fr.ofInt_zero, Fr.ofInt_one]
    cases s.eval p env with
    | none => rfl
    | some xs =>
      simp only [Option.bind_some]
      cases hs : asBool xs with
      | none => cases a.eval p env <;> cases b.eval p env <;> simp
      | some bs =>
        cases a.eval p env <;> cases b.eval p env <;> cases bs <;> simp [asBool_zero, asBool_one]
  · rfl

/-- `mkSelect` drops a conditional with equal branches only when its condition
    cannot fail and is 0 or 1. -/
theorem mkSelect_eval (c a b : Expr) :
    (mkSelect c a b).eval p env = (Expr.select c a b).eval p env := by
  unfold mkSelect
  split
  · rename_i h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, hct⟩, hcb⟩ := h
    obtain ⟨xc, hxc⟩ := Expr.total_eval p env [] (boolsHold_nil env) c hct
    obtain ⟨bc, hbc, _⟩ := asBool_of_zero_or_one
      (Expr.isBool_eval p env [] (boolsHold_nil env) c xc hcb hxc)
    simp only [Expr.eval, Option.bind_eq_bind, Option.pure_def, hxc, hbc, Option.bind_some]
    cases a.eval p env <;> cases bc <;> rfl
  · exact mkSelectDistinct_eval p env c a b

mutual
/-- Simplifying an expression does not change its value, nor whether it has one. -/
theorem Expr.simp_eval : ∀ e : Expr, e.simp.eval p env = e.eval p env
  | .add a b => by
      simp only [Expr.simp, mkAdd_eval, Expr.eval, Expr.simp_eval a, Expr.simp_eval b]
  | .mul a b => by
      simp only [Expr.simp, mkMul_eval, Expr.eval, Expr.simp_eval a, Expr.simp_eval b]
  | .neg a => by
      simp only [Expr.simp, mkNeg_eval, Expr.eval, Expr.simp_eval a]
  | .divmod _ _ a => by
      simp only [Expr.simp, Expr.eval, Expr.simp_eval a]
  | .lt bits a b => by
      simp only [Expr.simp, mkLt_eval, Expr.eval, Expr.simp_eval a, Expr.simp_eval b]
  | .eq a b => by
      simp only [Expr.simp, mkEq_eval, Expr.eval, Expr.simp_eval a, Expr.simp_eval b]
  | .select c a b => by
      simp only [Expr.simp, mkSelect_eval, Expr.eval, Expr.simp_eval c, Expr.simp_eval a,
        Expr.simp_eval b]
  | .hash xs => by
      simp only [Expr.simp, Expr.eval, Expr.simpList_eval xs]
  | .phash high align xs => by
      simp only [Expr.simp, Expr.eval, Expr.simpList_eval xs]
  | .var _ => rfl
  | .const _ => rfl
  | .invalid _ => rfl
  | .disclose e => by
      simp only [Expr.simp, Expr.eval, Expr.simp_eval e]
/-- Simplifying a list of expressions does not change their values. -/
theorem Expr.simpList_eval : ∀ xs : List Expr,
    Expr.evalList p env (Expr.simpList xs) = Expr.evalList p env xs
  | [] => rfl
  | x :: xs => by
      simp only [Expr.simpList, Expr.evalList, Expr.simp_eval x, Expr.simpList_eval xs]
end

end Simp

/-! ## Facts used inside a rewrite -/

section Rewrite
variable (p : Prims)

/-- `select c a a` is `a` when `c` cannot fail and is 0 or 1. -/
theorem select_same_eval (env : Env) (bools : List Var) (hb : BoolsHold env bools) (c a : Expr)
    (hct : c.total bools = true) (hcb : c.isBool bools = true) :
    (Expr.select c a a).eval p env = a.eval p env := by
  obtain ⟨xc, hxc⟩ := Expr.total_eval p env bools hb c hct
  obtain ⟨bc, hbc, _⟩ := asBool_of_zero_or_one (Expr.isBool_eval p env bools hb c xc hcb hxc)
  simp only [Expr.eval, Option.bind_eq_bind, Option.pure_def, hxc, hbc, Option.bind_some]
  cases a.eval p env <;> cases bc <;> rfl

/-- `select c 1 0` is `c` when `c` is 0 or 1 whenever it has a value. -/
theorem select_one_zero_eval (env : Env) (bools : List Var) (hb : BoolsHold env bools) (c : Expr)
    (hcb : c.isBool bools = true) :
    (Expr.select c (.const 1) (.const 0)).eval p env = c.eval p env := by
  cases hc : c.eval p env with
  | none => simp [Expr.eval, Option.bind_eq_bind, hc]
  | some x =>
      obtain ⟨bx, hbx, hx⟩ := asBool_of_zero_or_one (Expr.isBool_eval p env bools hb c x hcb hc)
      subst hx
      cases bx <;>
        simp [Expr.eval, Option.bind_eq_bind, Option.pure_def, hc, Fr.ofInt_zero,
          Fr.ofInt_one, Fr.ofBool, asBool_zero, asBool_one]

mutual
/-- The boolean rewrites do not change a value, given the variables in `bools` are 0 or 1. -/
theorem Expr.boolSimp_eval (env : Env) (bools : List Var) (hb : BoolsHold env bools) :
    ∀ e : Expr, (e.boolSimp bools).eval p env = e.eval p env
  | .select c a b => by
      have hs : (Expr.select (c.boolSimp bools) (a.boolSimp bools) (b.boolSimp bools)).eval p env
          = (Expr.select c a b).eval p env := by
        simp only [Expr.eval, Expr.boolSimp_eval env bools hb c, Expr.boolSimp_eval env bools hb a,
          Expr.boolSimp_eval env bools hb b]
      simp only [Expr.boolSimp]
      split
      · next h =>
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨hab, hct⟩, hcb⟩ := h
        rw [← hs, ← hab, select_same_eval p env bools hb _ _ hct hcb]
      · split
        · next h1 h2 =>
          split
          · next hcb =>
            rw [← hs, h1, h2, select_one_zero_eval p env bools hb _ hcb]
          · rw [← hs, h1, h2]
        · exact hs
  | .add a b => by
      simp only [Expr.boolSimp, Expr.eval, Expr.boolSimp_eval env bools hb a,
        Expr.boolSimp_eval env bools hb b]
  | .mul a b => by
      simp only [Expr.boolSimp, Expr.eval, Expr.boolSimp_eval env bools hb a,
        Expr.boolSimp_eval env bools hb b]
  | .eq a b => by
      simp only [Expr.boolSimp, Expr.eval, Expr.boolSimp_eval env bools hb a,
        Expr.boolSimp_eval env bools hb b]
  | .lt _ a b => by
      simp only [Expr.boolSimp, Expr.eval, Expr.boolSimp_eval env bools hb a,
        Expr.boolSimp_eval env bools hb b]
  | .neg a => by
      simp only [Expr.boolSimp, Expr.eval, Expr.boolSimp_eval env bools hb a]
  | .divmod _ _ a => by
      simp only [Expr.boolSimp, Expr.eval, Expr.boolSimp_eval env bools hb a]
  | .disclose a => by
      simp only [Expr.boolSimp, Expr.eval, Expr.boolSimp_eval env bools hb a]
  | .hash xs => by
      simp only [Expr.boolSimp, Expr.eval, Expr.boolSimpList_eval env bools hb xs]
  | .phash _ _ xs => by
      simp only [Expr.boolSimp, Expr.eval, Expr.boolSimpList_eval env bools hb xs]
  | .var _ => rfl
  | .const _ => rfl
  | .invalid _ => rfl
/-- The boolean rewrites do not change the values of a list. -/
theorem Expr.boolSimpList_eval (env : Env) (bools : List Var) (hb : BoolsHold env bools) :
    ∀ xs : List Expr, Expr.evalList p env (Expr.boolSimpList bools xs) = Expr.evalList p env xs
  | [] => rfl
  | x :: xs => by
      simp only [Expr.boolSimpList, Expr.evalList, Expr.boolSimp_eval env bools hb x,
        Expr.boolSimpList_eval env bools hb xs]
end

/-- Every variable, read through `known` in the optimized circuit's environment
    `env'`, has the value it has in the original circuit's environment `env`. -/
def KnownHolds (env env' : Env) (known : List (Var × Expr)) : Prop :=
  ∀ v, ((Expr.var v).subst known).eval p env' = some (env v)

mutual
/-- Substituting what is known gives, in the optimized environment, the value
    the expression has in the original one. -/
theorem Expr.subst_eval (env env' : Env) (known : List (Var × Expr)) (hk : KnownHolds p env env' known) :
    ∀ e : Expr, (e.subst known).eval p env' = e.eval p env
  | .var v => hk v
  | .const _ => rfl
  | .invalid _ => rfl
  | .add a b => by
      simp only [Expr.subst, Expr.eval, Expr.subst_eval env env' known hk a,
        Expr.subst_eval env env' known hk b]
  | .mul a b => by
      simp only [Expr.subst, Expr.eval, Expr.subst_eval env env' known hk a,
        Expr.subst_eval env env' known hk b]
  | .eq a b => by
      simp only [Expr.subst, Expr.eval, Expr.subst_eval env env' known hk a,
        Expr.subst_eval env env' known hk b]
  | .lt _ a b => by
      simp only [Expr.subst, Expr.eval, Expr.subst_eval env env' known hk a,
        Expr.subst_eval env env' known hk b]
  | .select c a b => by
      simp only [Expr.subst, Expr.eval, Expr.subst_eval env env' known hk c,
        Expr.subst_eval env env' known hk a, Expr.subst_eval env env' known hk b]
  | .neg a => by
      simp only [Expr.subst, Expr.eval, Expr.subst_eval env env' known hk a]
  | .divmod _ _ a => by
      simp only [Expr.subst, Expr.eval, Expr.subst_eval env env' known hk a]
  | .disclose a => by
      simp only [Expr.subst, Expr.eval, Expr.subst_eval env env' known hk a]
  | .hash xs => by
      simp only [Expr.subst, Expr.eval, Expr.substList_eval env env' known hk xs]
  | .phash _ _ xs => by
      simp only [Expr.subst, Expr.eval, Expr.substList_eval env env' known hk xs]
/-- `Expr.subst_eval` for lists. -/
theorem Expr.substList_eval (env env' : Env) (known : List (Var × Expr)) (hk : KnownHolds p env env' known) :
    ∀ xs : List Expr, Expr.evalList p env' (Expr.substList known xs) = Expr.evalList p env xs
  | [] => rfl
  | x :: xs => by
      simp only [Expr.substList, Expr.evalList, Expr.subst_eval env env' known hk x,
        Expr.substList_eval env env' known hk xs]
end

/-- Every checked expression has a value, in the optimized environment, that passes its check. -/
def CheckedHolds (env' : Env) (checked : List (Expr × Range)) : Prop :=
  ∀ e r, (e, r) ∈ checked → ∃ x, e.eval p env' = some x ∧ r.holds x = true

/-- The facts are true of the original environment `env` and the optimized one `env'`. -/
structure Facts.Holds (f : Facts) (env env' : Env) : Prop where
  known : KnownHolds p env env' f.known
  bools : BoolsHold env' f.bools
  checked : CheckedHolds p env' f.checked

/-- A rewritten expression has, in the optimized environment, the value the
    original has in the original environment. -/
theorem Facts.rw_eval {f : Facts} {env env' : Env} (h : f.Holds p env env') (e : Expr) :
    (f.rw e).eval p env' = e.eval p env := by
  unfold Facts.rw
  rw [Expr.boolSimp_eval p env' f.bools h.bools, Expr.simp_eval, Expr.subst_eval p env env' f.known h.known]

/-- `Facts.rw_eval` for lists. -/
theorem Facts.rw_evalList {f : Facts} {env env' : Env} (h : f.Holds p env env') :
    ∀ xs : List Expr, Expr.evalList p env' (xs.map f.rw) = Expr.evalList p env xs
  | [] => rfl
  | x :: xs => by
      simp only [List.map, Expr.evalList, Facts.rw_eval p h x, Facts.rw_evalList h xs]

end Rewrite

/-! ## Ranges -/

/-- A field element whose canonical value is 0 is 0. -/
theorem fr_eq_zero_of_val {x : Fr} (h : x.val = 0) : x = 0 := Fr.ext (by rw [h, Fr.val_zero])

/-- A field element whose canonical value is 1 is 1. -/
theorem fr_eq_one_of_val {x : Fr} (h : x.val = 1) : x = 1 := Fr.ext (by rw [h, Fr.val_one])

/-- A field element whose canonical value is below 2 is 0 or 1. -/
theorem fr_zero_or_one_of_val_lt_two {x : Fr} (h : x.val < 2) : x = 0 ∨ x = 1 := by
  rcases Nat.lt_or_ge x.val 1 with h1 | h1
  · exact Or.inl (fr_eq_zero_of_val (by omega))
  · exact Or.inr (fr_eq_one_of_val (by omega))

/-- Passing the boolean range check means being 0 or 1. -/
theorem Range.holds_bool {x : Fr} (h : Range.holds x .bool = true) : x = 0 ∨ x = 1 := by
  simpa [Range.holds] using h

/-- `Range.implies` is sound for `Range.holds`, widths and bounds included. -/
theorem Range.implies_holds (r r' : Range) (x : Fr) (h : r.implies r' = true)
    (hx : r.holds x = true) : r'.holds x = true := by
  cases r <;> cases r' <;>
    simp only [Range.implies, Range.holds, fitsBits, Zkir.frBits, Bool.and_eq_true,
      decide_eq_true_eq, Bool.or_eq_true, Bool.false_eq_true] at h hx ⊢
  case zero.zero | zero.bool | zero.bits | zero.below => subst hx; simp_all [Fr.val_zero]
  case bool.bool => exact hx
  case bool.bits | bool.below =>
    rcases hx with rfl | rfl <;> simp_all [Fr.val_zero, Fr.val_one]
  case bits.bool n =>
    have : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by decide) h
    exact fr_zero_or_one_of_val_lt_two (by omega)
  case bits.bits n m =>
    have : 2 ^ n ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) h.1
    exact ⟨h.2, by omega⟩
  case bits.below n b w =>
    have : 2 ^ n ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) h.1.1
    exact ⟨⟨⟨h.1.2.1, by omega⟩, h.1.2.1, h.1.2.2⟩, by omega⟩
  case below.bool => exact fr_zero_or_one_of_val_lt_two (by omega)
  case below.bits => exact ⟨h.2, by omega⟩
  case below.below => exact ⟨⟨⟨h.2.1, by omega⟩, h.2.1, h.2.2⟩, by omega⟩

/-! ## Environments -/

section Env
variable (p : Prims)

mutual
/-- An expression's value depends only on the variables in it. -/
theorem Expr.eval_congr_vars {e₁ e₂ : Env} :
    ∀ e : Expr, (∀ w ∈ e.vars, e₁ w = e₂ w) → e.eval p e₁ = e.eval p e₂
  | .var v, h => by simp only [Expr.eval]; rw [h v (by simp [Expr.vars])]
  | .const _, _ => rfl
  | .invalid _, _ => rfl
  | .disclose a, h => by
      simp only [Expr.eval]; exact Expr.eval_congr_vars a (by simpa [Expr.vars] using h)
  | .neg a, h => by
      simp only [Expr.eval]; rw [Expr.eval_congr_vars a (by simpa [Expr.vars] using h)]
  | .divmod _ _ a, h => by
      simp only [Expr.eval]; rw [Expr.eval_congr_vars a (by simpa [Expr.vars] using h)]
  | .add a b, h | .mul a b, h | .eq a b, h | .lt _ a b, h => by
      simp only [Expr.vars, List.mem_append] at h
      simp only [Expr.eval]
      rw [Expr.eval_congr_vars a (fun w hw => h w (Or.inl hw)),
        Expr.eval_congr_vars b (fun w hw => h w (Or.inr hw))]
  | .select c a b, h => by
      simp only [Expr.vars, List.mem_append] at h
      simp only [Expr.eval]
      rw [Expr.eval_congr_vars c (fun w hw => h w (Or.inl (Or.inl hw))),
        Expr.eval_congr_vars a (fun w hw => h w (Or.inl (Or.inr hw))),
        Expr.eval_congr_vars b (fun w hw => h w (Or.inr hw))]
  | .hash xs, h | .phash _ _ xs, h => by
      simp only [Expr.vars] at h
      simp only [Expr.eval]; rw [Expr.evalList_congr_vars xs h]
/-- `Expr.eval_congr_vars` for lists. -/
theorem Expr.evalList_congr_vars {e₁ e₂ : Env} :
    ∀ xs : List Expr, (∀ w ∈ Expr.varsList xs, e₁ w = e₂ w) →
      Expr.evalList p e₁ xs = Expr.evalList p e₂ xs
  | [], _ => rfl
  | x :: xs, h => by
      simp only [Expr.varsList, List.mem_append] at h
      simp only [Expr.evalList]
      rw [Expr.eval_congr_vars x (fun w hw => h w (Or.inl hw)),
        Expr.evalList_congr_vars xs (fun w hw => h w (Or.inr hw))]
end

/-- Looking up in a list with one more entry in front. -/
theorem lookup_cons (v u : Var) (e : Expr) (l : List (Var × Expr)) :
    ((v, e) :: l).lookup u = if u = v then some e else l.lookup u := by
  simp only [List.lookup]
  by_cases h : u = v
  · subst h; simp
  · have : (u == v) = false := by simp [h]
    rw [this]; simp [h]

/-- The entry `lookup` finds is in the list. -/
theorem lookup_mem : ∀ {l : List (Var × Expr)} {u : Var} {e : Expr}, l.lookup u = some e → (u, e) ∈ l
  | [], _, _, h => by simp [List.lookup] at h
  | (k, b) :: l, u, e, h => by
      rw [lookup_cons] at h
      split at h
      · next hk => subst hk; cases h; simp
      · exact List.mem_cons_of_mem _ (lookup_mem h)

/-- Looking up after dropping the entries of some variables. -/
theorem lookup_filter (vs : List Var) (u : Var) :
    ∀ l : List (Var × Expr),
      (l.filter fun (k, _) => !vs.contains k).lookup u = if u ∈ vs then none else l.lookup u
  | [] => by simp [List.lookup]
  | (k, b) :: l => by
      have ih := lookup_filter vs u l
      rw [List.filter_cons]
      by_cases hk : k ∈ vs
      · have hc : (!vs.contains k) = false := by simp [hk]
        simp only [hc, Bool.false_eq_true, ite_false]
        rw [ih, lookup_cons]
        by_cases hu : u = k
        · subst hu; simp [hk]
        · simp [hu]
      · have hc : (!vs.contains k) = true := by simp [hk]
        simp only [hc, ite_true]
        rw [lookup_cons, lookup_cons, ih]
        by_cases hu : u = k
        · subst hu; simp [hk]
        · simp [hu]

/-- Looking up with entries `v ↦ c` for a list of variables in front. -/
theorem lookup_append_const (vs : List Var) (c : Expr) (u : Var) (l : List (Var × Expr)) :
    ((vs.map fun v => (v, c)) ++ l).lookup u = if u ∈ vs then some c else l.lookup u := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
      simp only [List.map_cons, List.cons_append, lookup_cons, ih, List.mem_cons]
      by_cases hu : u = v <;> simp [hu]

/-- A variable not in the known list reads as itself. -/
theorem subst_var_of_lookup_none {known : List (Var × Expr)} {u : Var} (h : known.lookup u = none) :
    (Expr.var u).subst known = .var u := by
  simp [Expr.subst, h]

/-- A variable in the known list reads as its entry. -/
theorem subst_var_of_lookup_some {known : List (Var × Expr)} {u : Var} {e : Expr}
    (h : known.lookup u = some e) : (Expr.var u).subst known = e := by
  simp [Expr.subst, h]

/-- No known value of a variable not being bound mentions a variable being bound. -/
theorem Facts.not_clash {f : Facts} {vs : List Var} (hc : f.clash vs = false) :
    ∀ u e, (u, e) ∈ f.known → u ∉ vs → ∀ w ∈ e.vars, w ∉ vs := by
  intro u e hm hu w hw hwv
  have : f.clash vs = true := by
    simp only [Facts.clash, List.any_eq_true]
    exact ⟨(u, e), hm, by simp [hu, List.any_eq_true]; exact ⟨w, hw, hwv⟩⟩
  rw [hc] at this; cases this

/-- After binding the variables `vs` to the same values on both sides (and
    nothing else), the facts that do not mention them still hold, provided no
    known value clashes. -/
theorem Facts.forget_holds {f : Facts} {env env' r r' : Env} {vs : List Var}
    (h : f.Holds p env env') (hc : f.clash vs = false)
    (hin : ∀ w ∈ vs, r w = r' w) (hout : ∀ w, w ∉ vs → r w = env w ∧ r' w = env' w) :
    (f.forget vs).Holds p r r' where
  known := by
    intro u
    simp only [Facts.forget]
    rw [Expr.subst, lookup_filter]
    by_cases hu : u ∈ vs
    · simp [hu, Expr.eval, hin u hu]
    · simp only [hu, ite_false]
      have hk := h.known u
      cases hl : f.known.lookup u with
      | none =>
          rw [subst_var_of_lookup_none hl] at hk
          simp only [Expr.eval, Option.getD_none, Option.some.injEq] at hk ⊢
          rw [(hout u hu).1, (hout u hu).2, hk]
      | some e =>
          rw [subst_var_of_lookup_some hl] at hk
          simp only [Option.getD_some]
          rw [Expr.eval_congr_vars p e (e₂ := env'), hk, (hout u hu).1]
          intro w hw
          exact (hout w (f.not_clash hc u e (lookup_mem hl) hu w hw)).2
  bools := by
    intro v hv
    simp only [Facts.forget, List.mem_filter] at hv
    rw [(hout v (by simpa using hv.2)).2]
    exact h.bools v hv.1
  checked := by
    intro e rg hm
    simp only [Facts.forget, List.mem_filter, List.all_eq_true] at hm
    obtain ⟨x, hx, hr⟩ := h.checked e rg hm.1
    refine ⟨x, ?_, hr⟩
    rw [Expr.eval_congr_vars p e (e₂ := env'), hx]
    intro w hw
    have := hm.2 w hw
    exact (hout w (by simpa using this)).2

end Env

/-! ## Partial results -/

/-- Two partial results agree: both fail, or both succeed with related values. -/
def OptRel (R : α → β → Prop) : Option α → Option β → Prop
  | none, none => True
  | some a, some b => R a b
  | _, _ => False

/-- `OptRel` with a weaker relation. -/
theorem OptRel.mono {R S : α → β → Prop} {o₁ : Option α} {o₂ : Option β} (h : OptRel R o₁ o₂)
    (hs : ∀ a b, R a b → S a b) : OptRel S o₁ o₂ := by
  cases o₁ <;> cases o₂ <;> simp_all [OptRel]

/-! ## Reading transcripts -/

/-- One step of `readAll`: read a value, check its range, read the rest. -/
theorem readAll_cons (active : Bool) (env : Env) (v : Var) (rg : Option Range)
    (rest : List (Var × Option Range)) (st : List Fr) :
    readAll active env ((v, rg) :: rest) st =
      (Zkir.readOne active st).bind fun (x, st1) =>
        if rg.all (Range.holds x) then readAll active (env.set v x) rest st1 else none := by
  simp only [readAll]
  cases Zkir.readOne active st with
  | none => rfl
  | some xs =>
      obtain ⟨x, st1⟩ := xs
      cases rg with
      | none => simp [Option.bind_eq_bind]
      | some r =>
          by_cases hh : r.holds x <;> simp [Option.bind_eq_bind, hh]

/-- Reading into two environments reads the same values and stream: afterwards
    the environments agree on the variables read and are unchanged elsewhere. -/
theorem readAll_pair (active : Bool) : ∀ (outs : List (Var × Option Range)) (env env' : Env)
    (st : List Fr),
    OptRel (fun a b => a.2 = b.2 ∧ (∀ w ∈ outs.map (·.1), a.1 w = b.1 w) ∧
        (∀ w, w ∉ outs.map (·.1) → a.1 w = env w ∧ b.1 w = env' w))
      (readAll active env outs st) (readAll active env' outs st)
  | [], env, env', st => by simp [readAll, OptRel]
  | (v, rg) :: outs, env, env', st => by
      rw [readAll_cons, readAll_cons]
      cases Zkir.readOne active st with
      | none => simp [OptRel]
      | some xs =>
          obtain ⟨x, st1⟩ := xs
          simp only [Option.bind_some]
          split
          · refine (readAll_pair active outs (env.set v x) (env'.set v x) st1).mono ?_
            intro a b ⟨hs, hin, hout⟩
            refine ⟨hs, ?_, ?_⟩
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
          · simp [OptRel]

/-- A successful read leaves the variables it does not read unchanged. -/
theorem readAll_unchanged {active : Bool} {outs : List (Var × Option Range)} {env r : Env}
    {st st' : List Fr} (h : readAll active env outs st = some (r, st')) :
    ∀ w, w ∉ outs.map (·.1) → r w = env w := by
  have := readAll_pair active outs env env st
  rw [h] at this
  simp only [OptRel] at this
  exact fun w hw => (this.2.2 w hw).1

/-- After a successful read of distinct variables, each passes its range check. -/
theorem readAll_checks {active : Bool} : ∀ {outs : List (Var × Option Range)} {env r : Env}
    {st st' : List Fr}, readAll active env outs st = some (r, st') → (outs.map (·.1)).Nodup →
    ∀ v rg, (v, some rg) ∈ outs → rg.holds (r v) = true
  | [], _, _, _, _, _, _, _, _, hm => by simp at hm
  | (v0, rg0) :: outs, env, r, st, st', h, hnd, v, rg, hm => by
      rw [readAll_cons] at h
      cases hr : Zkir.readOne active st with
      | none => simp [hr] at h
      | some xs =>
          obtain ⟨x, st1⟩ := xs
          simp only [hr, Option.bind_some] at h
          split at h
          · next hok =>
            simp only [List.map_cons, List.nodup_cons] at hnd
            simp only [List.mem_cons, Prod.mk.injEq] at hm
            rcases hm with ⟨rfl, rfl⟩ | hm
            · rw [readAll_unchanged h v hnd.1]
              simpa [Env.set] using hok
            · exact readAll_checks h hnd.2 v rg hm
          · cases h

/-- With the guard false, a read succeeds when zero passes every range check:
    it reads nothing and sets the variables to zero. -/
theorem readAll_inactive : ∀ (outs : List (Var × Option Range)) (env : Env) (st : List Fr),
    (outs.all fun (_, r) => r.all (Range.holds 0)) = true →
    ∃ r, readAll false env outs st = some (r, st) ∧ (∀ w ∈ outs.map (·.1), r w = 0) ∧
      (∀ w, w ∉ outs.map (·.1) → r w = env w)
  | [], env, st, _ => ⟨env, rfl, by simp, fun _ _ => rfl⟩
  | (v, rg) :: outs, env, st, h => by
      simp only [List.all_cons, Bool.and_eq_true] at h
      obtain ⟨r, hr, hin, hout⟩ := readAll_inactive outs (env.set v 0) st h.2
      refine ⟨r, ?_, ?_, ?_⟩
      · rw [readAll_cons]
        simp [Zkir.readOne, h.1, hr]
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

/-! ## On-chain instructions -/

section Ops
set_option linter.unusedSectionVars false
variable (g : Expr → Expr) (hg : ∀ k, g (Expr.const k) = Expr.const k)
include hg

/-- Rewriting the values of an aligned value rewrites its encoding. -/
theorem Aligned.encode_map (v : Impact.Aligned Expr) :
    (Id.run (v.mapM (m := Id) fun a => pure (g a))).encode Expr.const =
      (v.encode Expr.const).map g := by
  simp [Impact.Aligned.mapM, Impact.Aligned.encode, List.mapM_pure, hg, Function.comp_def]

omit hg in
/-- Rewriting the values in a list of state values keeps its length. -/
theorem StateLit.mapMList_length : ∀ es : List (Impact.StateLit Expr),
    (Id.run (Impact.StateLit.mapMList (m := Id) (fun a => pure (g a)) es)).length = es.length
  | [] => rfl
  | e :: es => by
      have := StateLit.mapMList_length es
      simp [Impact.StateLit.mapMList] at this ⊢
      exact this

mutual
/-- Rewriting the values in a state value rewrites its encoding. -/
theorem StateLit.encode_map : ∀ v : Impact.StateLit Expr,
    (Id.run (v.mapM (m := Id) fun a => pure (g a))).encode Expr.const =
      (v.encode Expr.const).map g
  | .null => by simp [Impact.StateLit.mapM, Impact.StateLit.encode, hg]
  | .cell v => by
      simp [Impact.StateLit.mapM, Impact.StateLit.encode, hg, Impact.Aligned.mapM,
        Impact.Aligned.encode, List.mapM_pure]
  | .emptyMap => by simp [Impact.StateLit.mapM, Impact.StateLit.encode, hg]
  | .array es => by
      have h1 := StateLit.encodeList_map es
      have h2 := StateLit.mapMList_length g es
      simp [Impact.StateLit.mapM, Impact.StateLit.encode, hg] at h1 h2 ⊢
      exact ⟨by rw [h2], h1⟩
  | .emptyMerkleTree d => by simp [Impact.StateLit.mapM, Impact.StateLit.encode, hg]
/-- `StateLit.encode_map` for lists. -/
theorem StateLit.encodeList_map : ∀ es : List (Impact.StateLit Expr),
    Impact.StateLit.encodeList Expr.const
        (Id.run (Impact.StateLit.mapMList (m := Id) (fun a => pure (g a)) es)) =
      (Impact.StateLit.encodeList Expr.const es).map g
  | [] => by simp [Impact.StateLit.mapMList, Impact.StateLit.encodeList]
  | e :: es => by
      have h1 := StateLit.encode_map e
      have h2 := StateLit.encodeList_map es
      simp [Impact.StateLit.mapMList, Impact.StateLit.encodeList] at h1 h2 ⊢
      rw [h1, h2]
end

/-- Rewriting the operands of an instruction rewrites its encoding, provided the
    rewrite leaves constants alone. -/
theorem Op.encode_map (op : Impact.Op Expr) :
    (op.map g).encode Expr.const = (op.encode Expr.const).map g := by
  cases op <;> simp [Impact.Op.map, Impact.Op.mapM, Impact.Op.encode, hg, List.mapM_pure,
    Impact.Aligned.mapM, Impact.Aligned.encode]
  case idx path =>
    induction path with
    | nil => rfl
    | cons a path ih => simp [hg, ih]
  case idxStack pre =>
    induction pre with
    | nil => rfl
    | cons a pre ih => simp [hg, ih]
  case pushState v =>
    have := StateLit.encode_map g hg v
    simpa using this

end Ops

/-- A rewrite leaves constants alone. -/
theorem Facts.rw_const (f : Facts) (k : Int) : f.rw (.const k) = .const k := rfl

/-- Rewriting the operands of the ledger instructions does not change the
    public inputs they produce. -/
theorem ledgerGroups_rw (p : Prims) {f : Facts} {env env' : Env} (h : f.Holds p env env')
    (active : Bool) : ∀ ops : List (Impact.Op Expr),
    ledgerGroups p env' active (ops.map (·.map f.rw)) = ledgerGroups p env active ops
  | [] => rfl
  | op :: ops => by
      simp only [List.map_cons, ledgerGroups]
      rw [Op.encode_map f.rw (Facts.rw_const f), Facts.rw_evalList p h, ledgerGroups_rw p h active ops]

/-- With the guard false, ledger instructions whose operands all have values
    produce only inactive groups. -/
theorem ledgerGroups_inactive (p : Prims) (env : Env) : ∀ ops : List (Impact.Op Expr),
    (∀ op ∈ ops, ∃ ys, Expr.evalList p env (op.encode Expr.const) = some ys) →
    ∃ gs, ledgerGroups p env false ops = some gs ∧ gs.filter (·.active) = []
  | [], _ => ⟨[], rfl, rfl⟩
  | op :: ops, h => by
      obtain ⟨ys, hys⟩ := h op (by simp)
      obtain ⟨gs, hgs, hf⟩ := ledgerGroups_inactive p env ops (fun o ho => h o (by simp [ho]))
      refine ⟨{ active := false, vals := ys.map fun _ => 0 } :: gs, ?_, ?_⟩
      · simp only [ledgerGroups, hys, hgs, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
        rfl
      · simp [hf]

/-! ## Statement lists -/

/-- Running two lists of statements is running one after the other. -/
theorem execAll_append (p : Prims) : ∀ (a b : List Stmt) (s : RunState),
    execAll p (a ++ b) s = (execAll p a s).bind (execAll p b)
  | [], _, _ => rfl
  | st :: a, b, s => by
      simp only [List.cons_append, execAll, Option.bind_eq_bind]
      cases st.exec p s with
      | none => rfl
      | some s' => simp only [Option.bind_some]; exact execAll_append p a b s'

/-! ## Statements -/

section Stmts
variable (p : Prims)

/-- The original run state `s` and the optimized one `s'` correspond under the
    facts `f`: the facts hold, the unread transcripts are the same, and so are
    the public inputs of the instructions that ran. -/
structure StateRel (f : Facts) (s s' : RunState) : Prop where
  facts : f.Holds p s.env s'.env
  priv : s'.priv = s.priv
  pub : s'.pub = s.pub
  groups : s'.groups.filter (·.active) = s.groups.filter (·.active)

/-- Running one statement as a list. -/
theorem execAll_single (st : Stmt) (s : RunState) : execAll p [st] s = st.exec p s := by
  simp only [execAll, Option.bind_eq_bind]
  cases st.exec p s <;> rfl

/-- Knowing that `v` now reads as `e`, where `e` has `v`'s new value in the
    optimized environment, which did not change. -/
theorem KnownHolds.cons {env env' : Env} {known : List (Var × Expr)} (hk : KnownHolds p env env' known)
    (v : Var) (e : Expr) (x : Fr) (he : e.eval p env' = some x) :
    KnownHolds p (env.set v x) env' ((v, e) :: known) := by
  intro u
  rw [Expr.subst, lookup_cons]
  by_cases hu : u = v
  · subst hu; simp [Env.set, he]
  · have := hk u
    simp only [Expr.subst] at this
    simp [hu, Env.set, this]

/-- Knowing that the variables `vs` now read as 0, where they were set to 0 in
    the original environment only. -/
theorem KnownHolds.zeros {env env' r : Env} {known : List (Var × Expr)} (hk : KnownHolds p env env' known)
    (vs : List Var) (hin : ∀ w ∈ vs, r w = 0) (hout : ∀ w, w ∉ vs → r w = env w) :
    KnownHolds p r env' (vs.map (fun v => (v, Expr.const 0)) ++ known) := by
  intro u
  rw [Expr.subst, lookup_append_const]
  by_cases hu : u ∈ vs
  · simp [hu, hin u hu, Expr.eval, Fr.ofInt_zero]
  · have := hk u
    simp only [Expr.subst] at this
    simp [hu, hout u hu, this]

/-- `bind` is optimized soundly. -/
theorem optimize_bind_sound {f f' : Facts} {v : Var} {hint : String} {e : Expr} {out : List Stmt}
    (ho : (Stmt.bind v hint e).optimize f = some (out, f')) {s s' : RunState}
    (hr : StateRel p f s s') :
    OptRel (StateRel p f') ((Stmt.bind v hint e).exec p s) (execAll p out s') := by
  have hrw := Facts.rw_eval p hr.facts e
  simp only [Stmt.optimize] at ho
  split at ho
  · next c hc =>
    simp only [Option.some.injEq, Prod.mk.injEq] at ho
    obtain ⟨rfl, rfl⟩ := ho
    rw [hc] at hrw
    simp only [Stmt.exec, ← hrw, Expr.eval, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      execAll, OptRel]
    exact ⟨⟨hr.facts.known.cons p v _ _ rfl, hr.facts.bools, hr.facts.checked⟩, hr.priv, hr.pub,
      hr.groups⟩
  · next w hw =>
    simp only [Option.some.injEq, Prod.mk.injEq] at ho
    obtain ⟨rfl, rfl⟩ := ho
    rw [hw] at hrw
    simp only [Stmt.exec, ← hrw, Expr.eval, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      execAll, OptRel]
    exact ⟨⟨hr.facts.known.cons p v _ _ rfl, hr.facts.bools, hr.facts.checked⟩, hr.priv, hr.pub,
      hr.groups⟩
  · split at ho
    · cases ho
    · next hc =>
      simp only [Option.some.injEq, Prod.mk.injEq] at ho
      obtain ⟨rfl, rfl⟩ := ho
      rw [execAll_single]
      simp only [Stmt.exec, Option.bind_eq_bind, Option.pure_def, hrw]
      cases he : e.eval p s.env with
      | none => simp [OptRel]
      | some x =>
        simp only [Option.bind_some, OptRel]
        have hf := Facts.forget_holds p hr.facts (Bool.eq_false_iff.mpr hc)
          (r := s.env.set v x) (r' := s'.env.set v x)
          (by intro w hw; simp at hw; subst hw; simp [Env.set])
          (by intro w hw; simp at hw; simp [Env.set, hw])
        refine ⟨?_, hr.priv, hr.pub, hr.groups⟩
        split
        · next hb =>
          refine ⟨hf.known, ?_, hf.checked⟩
          intro u hu
          simp only [List.mem_cons] at hu
          rcases hu with rfl | hu
          · simp only [Env.set, ↓reduceIte]
            exact Expr.isBool_eval p s'.env f.bools hr.facts.bools _ x hb (hrw.trans he)
          · exact hf.bools u hu
        · exact hf

/-- `assert` is optimized soundly. -/
theorem optimize_assert_sound {f f' : Facts} {cond : Expr} {msg : String} {out : List Stmt}
    (ho : (Stmt.assert cond msg).optimize f = some (out, f')) {s s' : RunState}
    (hr : StateRel p f s s') :
    OptRel (StateRel p f') ((Stmt.assert cond msg).exec p s) (execAll p out s') := by
  have hrw := Facts.rw_eval p hr.facts cond
  simp only [Stmt.optimize] at ho
  split at ho
  · next h1 =>
    simp only [Option.some.injEq, Prod.mk.injEq] at ho
    obtain ⟨rfl, rfl⟩ := ho
    rw [h1] at hrw
    simp only [Stmt.exec, ← hrw, Expr.eval, Option.bind_eq_bind, Option.bind_some, Fr.ofInt_one,
      asBool_one, ite_true, execAll, OptRel]
    exact hr
  · simp only [Option.some.injEq, Prod.mk.injEq] at ho
    obtain ⟨rfl, rfl⟩ := ho
    rw [execAll_single]
    simp only [Stmt.exec, Option.bind_eq_bind, hrw]
    cases cond.eval p s.env with
    | none => simp [OptRel]
    | some x =>
      simp only [Option.bind_some]
      cases asBool x with
      | none => simp [OptRel]
      | some b => cases b <;> simp [OptRel, hr]

/-- `constrain` is optimized soundly. -/
theorem optimize_constrain_sound {f f' : Facts} {e : Expr} {r : Range} {out : List Stmt}
    (ho : (Stmt.constrain e r).optimize f = some (out, f')) {s s' : RunState}
    (hr : StateRel p f s s') :
    OptRel (StateRel p f') ((Stmt.constrain e r).exec p s) (execAll p out s') := by
  have hrw := Facts.rw_eval p hr.facts e
  simp only [Stmt.optimize] at ho
  split at ho
  · next hdrop =>
    simp only [Option.some.injEq, Prod.mk.injEq] at ho
    obtain ⟨rfl, rfl⟩ := ho
    -- The check is known to pass.
    have : ∃ x, e.eval p s.env = some x ∧ r.holds x = true := by
      simp only [Facts.passes, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hdrop
      rcases hdrop with htriv | ⟨⟨e0, r0⟩, hm, heq, himp⟩
      · split at htriv
        · next c hc =>
          rw [hc] at hrw
          exact ⟨_, hrw.symm, htriv⟩
        · cases htriv
      · simp only at heq himp
        subst heq
        obtain ⟨x, hx, hh⟩ := hr.facts.checked _ _ hm
        exact ⟨x, hrw ▸ hx, Range.implies_holds r0 r x himp hh⟩
    obtain ⟨x, hx, hh⟩ := this
    simp only [Stmt.exec, hx, Option.bind_eq_bind, Option.bind_some, hh, ite_true, execAll, OptRel]
    exact hr
  · simp only [Option.some.injEq, Prod.mk.injEq] at ho
    obtain ⟨rfl, rfl⟩ := ho
    rw [execAll_single]
    simp only [Stmt.exec, Option.bind_eq_bind, hrw]
    cases hx : e.eval p s.env with
    | none => simp [OptRel]
    | some x =>
      simp only [Option.bind_some]
      by_cases hh : r.holds x
      · simp only [hh, ite_true, Option.pure_def, OptRel]
        refine ⟨⟨hr.facts.known, ?_, ?_⟩, hr.priv, hr.pub, hr.groups⟩
        · unfold Facts.boolsAfter
          split
          · next v hv himp =>
            intro u hu
            simp only [List.mem_cons] at hu
            rcases hu with rfl | hu
            · rw [hv] at hrw
              simp only [Expr.eval, hx, Option.some.injEq] at hrw
              rw [hrw]
              exact Range.holds_bool (Range.implies_holds r .bool x himp hh)
            · exact hr.facts.bools u hu
          · exact hr.facts.bools
        · intro e0 r0 hm
          simp only [List.mem_cons, Prod.mk.injEq] at hm
          rcases hm with ⟨rfl, rfl⟩ | hm
          · exact ⟨x, hrw.trans hx, hh⟩
          · exact hr.facts.checked e0 r0 hm
      · simp [hh, OptRel]

/-- After a witness call, its results pass the checks recorded for them. -/
theorem witnessChecks_holds {act : Bool} {outs : List (Var × Option Range)} {env r r' : Env}
    {st st' : List Fr} (h : readAll act env outs st = some (r, st'))
    (hin : ∀ w ∈ outs.map (·.1), r w = r' w) : CheckedHolds p r' (witnessChecks outs) := by
  intro e rg hm
  unfold witnessChecks at hm
  split at hm
  · next hnd =>
    simp only [List.mem_filterMap] at hm
    obtain ⟨⟨v, ro⟩, hmo, hsome⟩ := hm
    cases ro with
    | none => simp at hsome
    | some r0 =>
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsome
      obtain ⟨rfl, rfl⟩ := hsome
      have hv : v ∈ outs.map (·.1) := List.mem_map.mpr ⟨_, hmo, rfl⟩
      exact ⟨r v, by simp [Expr.eval, hin v hv], readAll_checks h hnd v r0 hmo⟩
  · simp at hm

/-- After a witness call, its results recorded as 0 or 1 are. -/
theorem witnessBools_holds {act : Bool} {outs : List (Var × Option Range)} {env r r' : Env}
    {st st' : List Fr} (h : readAll act env outs st = some (r, st'))
    (hin : ∀ w ∈ outs.map (·.1), r w = r' w) : BoolsHold r' (witnessBools outs) := by
  intro v hm
  unfold witnessBools at hm
  split at hm
  · next hnd =>
    simp only [List.mem_filterMap] at hm
    obtain ⟨⟨v', ro⟩, hmo, hsome⟩ := hm
    cases ro with
    | none => simp at hsome
    | some r0 =>
      simp only at hsome
      split at hsome
      · next himp =>
        simp only [Option.some.injEq] at hsome
        subst hsome
        have hv : v' ∈ outs.map (·.1) := List.mem_map.mpr ⟨_, hmo, rfl⟩
        rw [← hin v' hv]
        exact Range.holds_bool (Range.implies_holds r0 .bool _ himp (readAll_checks h hnd v' r0 hmo))
      · cases hsome
  · simp at hm

/-- Facts that hold, with more checks and booleans that hold. -/
theorem Facts.Holds.extend {f : Facts} {env env' : Env} (h : f.Holds p env env')
    {cs : List (Expr × Range)} {bs : List Var} (hc : CheckedHolds p env' cs) (hb : BoolsHold env' bs) :
    ({ f with checked := cs ++ f.checked, bools := bs ++ f.bools } : Facts).Holds p env env' where
  known := h.known
  bools := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hb v hv
    · exact h.bools v hv
  checked := by
    intro e r hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hc e r hm
    · exact h.checked e r hm

/-- `witness` is optimized soundly. -/
theorem optimize_witness_sound {f f' : Facts} {guard : Expr} {name : String} {args : List Expr}
    {outs : List (Var × Option Range)} {shape : Shape} {out : List Stmt}
    (ho : (Stmt.witness guard name args outs shape).optimize f = some (out, f')) {s s' : RunState}
    (hr : StateRel p f s s') :
    OptRel (StateRel p f') ((Stmt.witness guard name args outs shape).exec p s) (execAll p out s') := by
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
      simp only [Stmt.exec, ← hrw, Expr.eval, Option.bind_eq_bind, Option.bind_some, execAll]
      by_cases he : outs.isEmpty
      · have : outs = [] := List.isEmpty_iff.mp he
        subst this
        simp only [List.isEmpty_nil, ite_true, OptRel, List.map_nil, List.nil_append]
        exact hr
      · simp only [he, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hskip
        obtain ⟨h0, hall⟩ := hskip
        obtain ⟨r, hrd, hin, hout⟩ := readAll_inactive outs s.env s.priv hall
        simp only [he, Bool.false_eq_true, ite_false, h0, asBool_zero, Option.bind_some, hrd,
          Option.pure_def, OptRel]
        exact ⟨⟨hr.facts.known.zeros p _ hin hout, hr.facts.bools, hr.facts.checked⟩, hr.priv,
          hr.pub, hr.groups⟩
    · cases hskip
  · split at ho
    · cases ho
    · next hc =>
      simp only [Option.some.injEq, Prod.mk.injEq] at ho
      obtain ⟨rfl, rfl⟩ := ho
      rw [execAll_single]
      simp only [Stmt.exec, Option.bind_eq_bind, hrw]
      cases guard.eval p s.env with
      | none => simp [OptRel]
      | some gx =>
        simp only [Option.bind_some]
        split
        · next he =>
          have : outs = [] := List.isEmpty_iff.mp he
          subst this
          simp only [OptRel]
          refine ⟨?_, hr.priv, hr.pub, hr.groups⟩
          have := Facts.forget_holds p hr.facts (Bool.eq_false_iff.mpr hc) (r := s.env) (r' := s'.env)
            (by simp) (fun w _ => ⟨rfl, rfl⟩)
          simpa [witnessChecks, witnessBools] using this
        · cases asBool gx with
          | none => simp [OptRel]
          | some act =>
            simp only [Option.bind_some]
            have hp := readAll_pair act outs s.env s'.env s.priv
            rw [hr.priv]
            cases h1 : readAll act s.env outs s.priv with
            | none =>
              rw [h1] at hp
              cases h2 : readAll act s'.env outs s.priv with
              | none => simp [OptRel]
              | some b => rw [h2] at hp; simp [OptRel] at hp
            | some a =>
              rw [h1] at hp
              cases h2 : readAll act s'.env outs s.priv with
              | none => rw [h2] at hp; simp [OptRel] at hp
              | some b =>
                rw [h2] at hp
                obtain ⟨r, st⟩ := a
                obtain ⟨r', st'⟩ := b
                simp only [OptRel] at hp
                obtain ⟨hst, hin, hout⟩ := hp
                simp only [Option.bind_some, Option.pure_def, OptRel]
                refine ⟨?_, hst.symm, hr.pub, hr.groups⟩
                exact (Facts.forget_holds p hr.facts (Bool.eq_false_iff.mpr hc) hin hout).extend p
                  (witnessChecks_holds p h1 hin) (witnessBools_holds h1 hin)

/-- The variables a ledger statement reads. -/
theorem reads_vars (reads : List Var) :
    (reads.map fun v => ((v, (none : Option Range)))).map (·.1) = reads := by
  induction reads <;> simp_all

/-- `ledger` is optimized soundly. A ledger statement dropped because its guard
    is 0 contributes only inactive groups, which nobody observes. -/
theorem optimize_ledger_sound {f f' : Facts} {guard : Expr} {reads : List Var}
    {ops : List (Impact.Op Expr)} {out : List Stmt}
    (ho : (Stmt.ledger guard reads ops).optimize f = some (out, f')) {s s' : RunState}
    (hr : StateRel p f s s') :
    OptRel (StateRel p f') ((Stmt.ledger guard reads ops).exec p s) (execAll p out s') := by
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
      simp only [Stmt.exec, ← hrw, Expr.eval, Option.bind_eq_bind, Option.bind_some, execAll]
      by_cases he : (reads.isEmpty && ops.isEmpty) = true
      · simp only [Bool.and_eq_true] at he
        have : reads = [] := List.isEmpty_iff.mp he.1
        subst this
        simp only [List.isEmpty_nil, he.2, Bool.and_self, ite_true, OptRel, List.map_nil,
          List.nil_append]
        exact hr
      · have he' : (reads.isEmpty && ops.isEmpty) = false := by simpa using he
        simp only [List.isEmpty_map, he', Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hskip
        obtain ⟨h0, htot⟩ := hskip
        obtain ⟨r, hrd, hin, hout⟩ :=
          readAll_inactive (reads.map fun v => (v, none)) s.env s.pub (by simp)
        rw [reads_vars] at hin hout
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
        refine ⟨hf0, hr.priv, hr.pub, ?_⟩
        simp [List.filter_append, hgf, hr.groups]
    · cases hskip
  · split at ho
    · cases ho
    · next hc =>
      split at ho
      · cases ho
      simp only [Option.some.injEq, Prod.mk.injEq] at ho
      obtain ⟨rfl, rfl⟩ := ho
      rw [execAll_single]
      simp only [Stmt.exec, Option.bind_eq_bind, hrw, List.isEmpty_map]
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
          refine ⟨?_, hr.priv, hr.pub, hr.groups⟩
          exact Facts.forget_holds p hr.facts (Bool.eq_false_iff.mpr hc) (r := s.env) (r' := s'.env)
            (by simp) (fun w _ => ⟨rfl, rfl⟩)
        · cases asBool gx with
          | none => simp [OptRel]
          | some act =>
            simp only [Option.bind_some]
            have hp := readAll_pair act (reads.map fun v => (v, none)) s.env s'.env s.pub
            rw [hr.pub]
            cases h1 : readAll act s.env (reads.map fun v => (v, none)) s.pub with
            | none =>
              rw [h1] at hp
              cases h2 : readAll act s'.env (reads.map fun v => (v, none)) s.pub with
              | none => simp [OptRel]
              | some b => rw [h2] at hp; simp [OptRel] at hp
            | some a =>
              rw [h1] at hp
              cases h2 : readAll act s'.env (reads.map fun v => (v, none)) s.pub with
              | none => rw [h2] at hp; simp [OptRel] at hp
              | some b =>
                rw [h2] at hp
                obtain ⟨r, st⟩ := a
                obtain ⟨r', st'⟩ := b
                simp only [OptRel] at hp
                obtain ⟨hst, hin, hout⟩ := hp
                rw [reads_vars] at hin hout
                have hf := Facts.forget_holds p hr.facts (Bool.eq_false_iff.mpr hc) hin hout
                simp only [Option.bind_some, ledgerGroups_rw p hf]
                cases ledgerGroups p r act ops with
                | none => simp [OptRel]
                | some gs =>
                  simp only [Option.bind_some, Option.pure_def, OptRel]
                  refine ⟨hf, hr.priv, hst.symm, ?_⟩
                  simp [List.filter_append, hr.groups]

/-- Every statement is optimized soundly. -/
theorem Stmt.optimize_sound {f f' : Facts} {stmt : Stmt} {out : List Stmt}
    (ho : stmt.optimize f = some (out, f')) {s s' : RunState} (hr : StateRel p f s s') :
    OptRel (StateRel p f') (stmt.exec p s) (execAll p out s') := by
  cases stmt with
  | bind => exact optimize_bind_sound p ho hr
  | assert => exact optimize_assert_sound p ho hr
  | constrain => exact optimize_constrain_sound p ho hr
  | witness => exact optimize_witness_sound p ho hr
  | ledger => exact optimize_ledger_sound p ho hr

/-- A list of statements is optimized soundly. -/
theorem Stmt.optimizeAll_sound : ∀ {f f' : Facts} {stmts out : List Stmt},
    Stmt.optimizeAll f stmts = some (out, f') → ∀ {s s' : RunState}, StateRel p f s s' →
    OptRel (StateRel p f') (execAll p stmts s) (execAll p out s')
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
      have hs := Stmt.optimize_sound p h1 hr
      simp only [execAll, execAll_append, Option.bind_eq_bind]
      revert hs
      cases st.exec p s <;> cases execAll p a s' <;> simp only [OptRel, Option.bind_none,
        Option.bind_some, imp_self, false_implies]
      intro hs
      exact Stmt.optimizeAll_sound h2 hs

end Stmts

/-! ## Circuits -/

open Damp.Zkir (Outcome) in
/-- Optimizing a circuit does not change what a run of it produces that anyone
    can observe: it fails exactly when the original does, and otherwise has the
    same outputs and the same public inputs of the instructions that ran. No
    hypothesis on the circuit is needed: where the pass would rely on a value
    that a later binding changes, it leaves the circuit unchanged. -/
theorem Circuit.simplify_correct (p : Prims) (c : Circuit) (inputs priv pub : List Fr) :
    (c.simplify.run p inputs priv pub).map Outcome.observable =
      (c.run p inputs priv pub).map Outcome.observable := by
  unfold Circuit.simplify
  split
  · next body f ho =>
    simp only [Circuit.run, Option.bind_eq_bind]
    cases bindInputs (fun _ => 0) c.inputs inputs with
    | none => rfl
    | some env0 =>
      simp only [Option.bind_some]
      have hr0 : StateRel p {} { env := env0, priv, pub } { env := env0, priv, pub } :=
        ⟨⟨fun v => by simp [Expr.subst, List.lookup, Expr.eval], (fun _ h => nomatch h),
          (fun _ _ h => nomatch h)⟩, rfl, rfl, rfl⟩
      have hs := Stmt.optimizeAll_sound p ho hr0
      rw [List.toList_toArray]
      revert hs
      cases execAll p c.body.toList { env := env0, priv, pub } <;>
        cases execAll p body { env := env0, priv, pub } <;> simp only [OptRel, false_implies]
      · intro _; rfl
      · next t t' =>
        intro hrel
        simp only [Option.bind_some]
        rw [Facts.rw_evalList p hrel.facts, hrel.priv, hrel.pub]
        cases Expr.evalList p t.env c.outputs with
        | none => rfl
        | some outs =>
          simp only [Option.bind_some]
          split
          · simp [Outcome.observable, Outcome.activeInputs, hrel.groups]
          · rfl
  · rfl

end Damp.IR
