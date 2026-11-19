/-
Soundness of the value-range pass (`Damp/Optimize/Bounds.lean`).

* `Bounds.ub_spec`: the bound of an expression bounds its value, whenever it
  has one; `Bounds.totalB_eval`: an expression `totalB` says cannot fail has a
  value; `Bounds.tighten_eval`: the rewrites of rule 2 and 3 do not change an
  expression's value, nor whether it has one.
* `Bounds.stmts_exec`, `Bounds.stmts_steps`: the rewritten statements run, in
  the semantics and in the executor, to exactly the same states as the
  original ones (the pass only drops checks that pass and rewrites
  expressions in place).
* `Circuit.bounds_sound : Pass.Sound Circuit.bounds`, and
  `Circuit.bounds_checkLedger`.
-/
import Damp.Optimize.Bounds
import Damp.Proofs.Optimize.Sound
import Damp.Proofs.Field
import Damp.IR.LedgerCheck

set_option linter.unusedSimpArgs false

namespace Damp.IR
namespace Bounds
open Damp.Zkir (Prims fitsBits)

/-! ## Field values -/

theorem val_add_of_lt {a b : Fr} (h : a.val + b.val < Fr.modulus) : (a + b).val = a.val + b.val :=
  Fr.val_ofNat_of_lt h

theorem val_mul_of_lt {a b : Fr} (h : a.val * b.val < Fr.modulus) : (a * b).val = a.val * b.val :=
  Fr.val_ofNat_of_lt h

theorem val_ofBool_le (b : Bool) : (Fr.ofBool b).val ≤ 1 := by
  rw [Fr.val_ofBool]; split <;> omega

theorem val_ofNat_le (n : Nat) : (Fr.ofNat n).val ≤ n := by
  rw [Fr.val_ofNat]; exact Nat.mod_le _ _

/-- `asBool` succeeds only on 0 and 1, giving back the value. -/
theorem asBool_some {x : Fr} {b : Bool} (h : asBool x = some b) : x = Fr.ofBool b := by
  unfold asBool at h
  split at h
  · next h0 => cases h; rw [h0]; rfl
  · split at h
    · next h1 => cases h; rw [h1]; rfl
    · cases h

/-! ## Facts -/

/-- Every recorded bound is true of the environment. -/
def Holds (env : Env) (f : UB) : Prop := ∀ v x, (v, x) ∈ f → (env v).val ≤ x

theorem holds_nil (env : Env) : Holds env [] := fun _ _ h => nomatch h

theorem lookup_mem : ∀ {l : List (Var × Nat)} {u : Var} {x : Nat}, l.lookup u = some x → (u, x) ∈ l
  | [], _, _, h => by simp [List.lookup] at h
  | (k, b) :: l, u, x, h => by
      simp only [List.lookup] at h
      split at h
      · next hk =>
        cases h
        have : u = k := by simpa using hk
        subst this; simp
      · exact List.mem_cons_of_mem _ (lookup_mem h)

/-- After binding the variables `vs`, the bounds of the others still hold. -/
theorem forget_holds {env r : Env} {f : UB} {vs : List Var} (h : Holds env f)
    (hout : ∀ w, w ∉ vs → r w = env w) : Holds r (forget f vs) := by
  intro v x hm
  simp only [forget, List.mem_filter, Bool.not_eq_true'] at hm
  have hv : v ∉ vs := by simpa using hm.2
  rw [hout v hv]
  exact h v x hm.1

/-! ## Expressions -/

section Expr
set_option linter.unusedSectionVars false
variable (p : Prims) {env : Env} {f : UB} (hf : Holds env f)
include hf

/-- The bound of an expression bounds its value, whenever it has one. -/
theorem ub_spec : ∀ (e : Expr) {x : Fr} {B : Nat}, e.eval p env = some x → ub f e = some B → x.val ≤ B
  | .var v, x, B, he, hb => by
      simp only [Expr.eval, Option.some.injEq] at he
      subst he
      exact hf v B (lookup_mem hb)
  | .const c, x, B, he, hb => by
      simp only [Expr.eval, Option.some.injEq] at he
      simp only [ub, Option.some.injEq] at hb
      subst he hb; exact Nat.le_refl _
  | .add a b, x, B, he, hb => by
      simp only [Expr.eval, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        Option.some.injEq] at he
      obtain ⟨xa, ha, xb, hb', rfl⟩ := he
      simp only [ub] at hb
      cases hA : ub f a <;> cases hB : ub f b <;> simp only [hA, hB, reduceCtorEq] at hb
      next A B' =>
        split at hb
        · next hlt =>
          cases hb
          have h1 := ub_spec a ha hA
          have h2 := ub_spec b hb' hB
          rw [val_add_of_lt (by omega)]
          omega
        · cases hb
  | .mul a b, x, B, he, hb => by
      simp only [Expr.eval, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        Option.some.injEq] at he
      obtain ⟨xa, ha, xb, hb', rfl⟩ := he
      simp only [ub] at hb
      cases hA : ub f a <;> cases hB : ub f b <;> simp only [hA, hB, reduceCtorEq] at hb
      next A B' =>
        split at hb
        · next hlt =>
          cases hb
          have h1 := ub_spec a ha hA
          have h2 := ub_spec b hb' hB
          have hm : xa.val * xb.val ≤ A * B' := Nat.mul_le_mul h1 h2
          rw [val_mul_of_lt (by omega)]
          exact hm
        · cases hb
  | .select c a b, x, B, he, hb => by
      simp only [Expr.eval, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        Option.some.injEq] at he
      obtain ⟨_, _, xa, ha, xb, hb', bc, _, rfl⟩ := he
      simp only [ub] at hb
      cases hA : ub f a <;> cases hB : ub f b <;> simp only [hA, hB, reduceCtorEq, Option.some.injEq] at hb
      subst hb
      have h1 := ub_spec a ha hA
      have h2 := ub_spec b hb' hB
      cases bc <;> simp <;> omega
  | .lt bits a b, x, B, he, hb => by
      simp only [Expr.eval, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at he
      obtain ⟨_, _, _, _, he⟩ := he
      simp only [ub, Option.some.injEq] at hb
      subst hb
      split at he
      · cases he; exact val_ofBool_le _
      · cases he
  | .eq a b, x, B, he, hb => by
      simp only [Expr.eval, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        Option.some.injEq] at he
      obtain ⟨_, _, _, _, rfl⟩ := he
      simp only [ub, Option.some.injEq] at hb
      subst hb
      exact val_ofBool_le _
  | .divmod quot bits a, x, B, he, hb => by
      simp only [Expr.eval, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at he
      obtain ⟨xa, ha, he⟩ := he
      split at he
      · cases he
        cases quot
        · simp only [ub] at hb
          simp only [Bool.false_eq_true, ite_false]
          have hm := Nat.mod_le xa.val (2 ^ bits)
          have hl := Nat.mod_lt xa.val (Nat.two_pow_pos bits)
          have hv := val_ofNat_le (xa.val % 2 ^ bits)
          cases hA : ub f a <;> simp only [hA, Option.some.injEq] at hb <;> subst hb
          · omega
          · have := ub_spec a ha hA
            omega
        · simp only [ub, Option.map_eq_some_iff] at hb
          obtain ⟨A, hA, rfl⟩ := hb
          simp only [ite_true]
          have := ub_spec a ha hA
          exact Nat.le_trans (val_ofNat_le _) (Nat.div_le_div_right this)
      · cases he
  | .disclose e, x, B, he, hb => by
      simp only [Expr.eval] at he
      simp only [ub] at hb
      exact ub_spec e he hb
  | .neg _, _, _, _, hb | .hash _, _, _, _, hb | .phash .., _, _, _, hb | .invalid _, _, _, _, hb => by
      simp [ub] at hb

omit hf in
/-- The lower bound of an expression bounds its value from below. -/
theorem lower_spec : ∀ (e : Expr) {x : Fr}, e.eval p env = some x → lower e ≤ x.val
  | .const c, x, he => by
      simp only [Expr.eval, Option.some.injEq] at he
      subst he; exact Nat.le_refl _
  | .disclose e, x, he => by
      simp only [Expr.eval] at he
      exact lower_spec e he
  | .var _, _, _ | .add .., _, _ | .mul .., _, _ | .neg _, _, _ | .lt .., _, _ | .eq .., _, _
  | .select .., _, _ | .hash _, _, _ | .phash .., _, _ | .divmod .., _, _ | .invalid _, _, _ => by
      simp [lower]

omit hf in
/-- A value bounded by 1 is 0 or 1. -/
theorem zero_or_one_of_le_one {x : Fr} (h : x.val ≤ 1) : x = 0 ∨ x = 1 :=
  fr_zero_or_one_of_val_lt_two (by omega)

theorem fits_spec {bits : Nat} {e : Expr} {x : Fr} (h : fits f bits e = true)
    (he : e.eval p env = some x) : x.val < 2 ^ bits := by
  unfold fits at h
  split at h
  · next A hA =>
    have := ub_spec p hf e he hA
    simp only [decide_eq_true_eq] at h
    omega
  · cases h

theorem isBit_spec {e : Expr} {x : Fr} (h : isBit f e = true)
    (he : e.eval p env = some x) : x = 0 ∨ x = 1 := by
  unfold isBit at h
  split at h
  · next A hA =>
    have := ub_spec p hf e he hA
    simp only [decide_eq_true_eq] at h
    exact zero_or_one_of_le_one (by omega)
  · cases h

mutual
/-- An expression that `totalB` says cannot fail has a value. -/
theorem totalB_eval : ∀ e : Expr, totalB f e = true → ∃ x, e.eval p env = some x
  | .var v, _ => ⟨env v, rfl⟩
  | .const c, _ => ⟨_, rfl⟩
  | .add a b, h => by
      simp only [totalB, Bool.and_eq_true] at h
      obtain ⟨x, hx⟩ := totalB_eval a h.1
      obtain ⟨y, hy⟩ := totalB_eval b h.2
      exact ⟨x + y, by simp [Expr.eval, Option.bind_eq_bind, Option.pure_def, hx, hy]⟩
  | .mul a b, h => by
      simp only [totalB, Bool.and_eq_true] at h
      obtain ⟨x, hx⟩ := totalB_eval a h.1
      obtain ⟨y, hy⟩ := totalB_eval b h.2
      exact ⟨x * y, by simp [Expr.eval, Option.bind_eq_bind, Option.pure_def, hx, hy]⟩
  | .eq a b, h => by
      simp only [totalB, Bool.and_eq_true] at h
      obtain ⟨x, hx⟩ := totalB_eval a h.1
      obtain ⟨y, hy⟩ := totalB_eval b h.2
      exact ⟨Fr.ofBool (decide (x = y)), by simp [Expr.eval, Option.bind_eq_bind, Option.pure_def, hx, hy]⟩
  | .neg a, h => by
      simp only [totalB] at h
      obtain ⟨x, hx⟩ := totalB_eval a h
      exact ⟨-x, by simp [Expr.eval, Option.bind_eq_bind, Option.pure_def, hx]⟩
  | .disclose a, h => by
      simp only [totalB] at h
      obtain ⟨x, hx⟩ := totalB_eval a h
      exact ⟨x, by simp [Expr.eval, hx]⟩
  | .divmod quot bits a, h => by
      simp only [totalB, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨x, hx⟩ := totalB_eval a h.2
      exact ⟨Fr.ofNat (if quot then x.val / 2 ^ bits else x.val % 2 ^ bits),
        by simp [Expr.eval, Option.bind_eq_bind, Option.pure_def, hx, h.1]⟩
  | .select c a b, h => by
      simp only [totalB, Bool.and_eq_true] at h
      obtain ⟨⟨⟨hcb, hc⟩, ha⟩, hb'⟩ := h
      obtain ⟨xc, hxc⟩ := totalB_eval c hc
      obtain ⟨x, hx⟩ := totalB_eval a ha
      obtain ⟨y, hy⟩ := totalB_eval b hb'
      obtain ⟨bc, hbc, _⟩ := asBool_of_zero_or_one (isBit_spec p hf hcb hxc)
      exact ⟨if bc then x else y, by simp [Expr.eval, Option.bind_eq_bind, Option.pure_def, hxc, hx, hy, hbc]⟩
  | .lt bits a b, h => by
      simp only [totalB, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨hbits, hfa⟩, hfb⟩, ha⟩, hb'⟩ := h
      obtain ⟨x, hx⟩ := totalB_eval a ha
      obtain ⟨y, hy⟩ := totalB_eval b hb'
      have h1 := fits_spec p hf hfa hx
      have h2 := fits_spec p hf hfb hy
      refine ⟨Fr.ofBool (decide (x.val < y.val)), ?_⟩
      simp [Expr.eval, Option.bind_eq_bind, Option.pure_def, hx, hy, fitsBits, Zkir.frBits, hbits, h1, h2]
  | .hash xs, h => by
      simp only [totalB] at h
      obtain ⟨ys, hys⟩ := totalBList_eval xs h
      exact ⟨p.transientHash ys, by simp [Expr.eval, Option.bind_eq_bind, Option.pure_def, hys]⟩
  | .phash .., h | .invalid _, h => by simp [totalB] at h
/-- A list of expressions that `totalBList` says cannot fail has values. -/
theorem totalBList_eval : ∀ xs : List Expr, totalBList f xs = true →
    ∃ ys, Expr.evalList p env xs = some ys
  | [], _ => ⟨[], rfl⟩
  | x :: xs, h => by
      simp only [totalBList, Bool.and_eq_true] at h
      obtain ⟨y, hy⟩ := totalB_eval x h.1
      obtain ⟨ys, hys⟩ := totalBList_eval xs h.2
      exact ⟨y :: ys, by simp [Expr.evalList, Option.bind_eq_bind, Option.pure_def, hy, hys]⟩
end

/-- A comparison the bounds decide has that value. -/
theorem decideLt_spec {bits : Nat} {a b : Expr} {r : Bool} (h : decideLt f bits a b = some r) :
    (Expr.lt bits a b).eval p env = some (Fr.ofBool r) := by
  unfold decideLt at h
  split at h
  · next hc =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨hbits, hfa⟩, hfb⟩, hta⟩, htb⟩ := hc
    obtain ⟨xa, ha⟩ := totalB_eval p hf a hta
    obtain ⟨xb, hb⟩ := totalB_eval p hf b htb
    have h1 := fits_spec p hf hfa ha
    have h2 := fits_spec p hf hfb hb
    have la := lower_spec p a ha
    have lb := lower_spec p b hb
    simp only [Expr.eval, Option.bind_eq_bind, Option.pure_def, ha, hb, Option.bind_some, fitsBits,
      Zkir.frBits, hbits, h1, h2, decide_true, Bool.and_self, ite_true, Option.some.injEq]
    split at h
    · next A B hA hB =>
      have hxa := ub_spec p hf a ha hA
      have hxb := ub_spec p hf b hb hB
      split at h
      · cases h; congr 1; simp only [decide_eq_true_eq]; omega
      · split at h
        · cases h; congr 1; simp only [decide_eq_false_iff_not]; omega
        · cases h
    · cases h
  · cases h

/-- The rewrites of rules 2 and 3 do not change an expression's value, nor
    whether it has one. -/
theorem tighten_eval : ∀ e : Expr, (tighten f e).eval p env = e.eval p env
  | .add a b => by simp only [tighten, Expr.eval, tighten_eval a, tighten_eval b]
  | .mul a b => by simp only [tighten, Expr.eval, tighten_eval a, tighten_eval b]
  | .eq a b => by simp only [tighten, Expr.eval, tighten_eval a, tighten_eval b]
  | .neg a => by simp only [tighten, Expr.eval, tighten_eval a]
  | .disclose a => by simp only [tighten, Expr.eval, tighten_eval a]
  | .select c a b => by simp only [tighten, Expr.eval, tighten_eval c, tighten_eval a, tighten_eval b]
  | .lt bits a b => by
      simp only [tighten]
      split
      · next h => rw [decideLt_spec p hf h]; rfl
      · next h => rw [decideLt_spec p hf h]; rfl
      · simp only [Expr.eval, tighten_eval a, tighten_eval b]
  | .divmod quot bits a => by
      simp only [tighten]
      split
      · next hc =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        cases quot
        · simp only [Bool.false_eq_true, ite_false]
          rw [tighten_eval a]
          simp only [Expr.eval, Option.bind_eq_bind, Option.pure_def]
          cases ha : a.eval p env with
          | none => rfl
          | some xa =>
            have := fits_spec p hf hc.2 ha
            simp [hc.1, Nat.mod_eq_of_lt this, Fr.ofNat_val]
        · simp only [ite_true]
          split
          · next ht =>
            obtain ⟨xa, ha⟩ := totalB_eval p hf a ht
            have := fits_spec p hf hc.2 ha
            simp [Expr.eval, ha, hc.1, Nat.div_eq_of_lt this]
            rfl
          · simp only [Expr.eval, tighten_eval a]
      · simp only [Expr.eval, tighten_eval a]
  | .var _ | .const _ | .hash _ | .phash .. | .invalid _ => by simp only [tighten]

theorem tighten_evalList : ∀ xs : List Expr, Expr.evalList p env (xs.map (tighten f)) = Expr.evalList p env xs
  | [] => rfl
  | x :: xs => by simp only [List.map, Expr.evalList, tighten_eval p hf x, tighten_evalList xs]

end Expr

/-! ## Ranges -/

/-- A value passing a range check is at most the check's bound. -/
theorem Range.ub_holds {r : Range} {x : Fr} (h : r.holds x = true) : x.val ≤ Range.ub r := by
  cases r <;> simp only [Range.holds, fitsBits, Zkir.frBits, Bool.and_eq_true, decide_eq_true_eq,
    Bool.or_eq_true, Range.ub] at h ⊢
  case zero => subst h; simp [Fr.val_zero]
  case bool => rcases h with rfl | rfl <;> simp [Fr.val_zero, Fr.val_one]
  case bits n => omega
  case below b w => omega

/-- A value within a bound that `within` accepts passes the check. -/
theorem within_spec {r : Range} {x : Fr} {B : Nat} (hx : x.val ≤ B) (h : within B r = true) :
    r.holds x = true := by
  have hfr : Zkir.frBits = 255 := rfl
  cases r <;> simp only [within, Range.holds, fitsBits, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true] at h ⊢
  case zero => exact fr_eq_zero_of_val (by omega)
  case bool => exact zero_or_one_of_le_one (by omega)
  case bits n => omega
  case below b w => omega

/-! ## Facts after a statement -/

theorem holds_append {env : Env} {f g : UB} (hf : Holds env f) (hg : Holds env g) : Holds env (f ++ g) := by
  intro v x hm
  rcases List.mem_append.mp hm with hm | hm
  · exact hf v x hm
  · exact hg v x hm

/-- Recording a bound that holds. -/
theorem learn_holds {env : Env} {f : UB} {v : Var} {o : Option Nat} (hf : Holds env f)
    (ho : ∀ B, o = some B → (env v).val ≤ B) : Holds env (learn f v o) := by
  unfold learn
  split
  · next B =>
    intro u y hm
    simp only [List.mem_cons, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | hm
    · exact ho _ rfl
    · exact hf u y hm
  · exact hf

section Post
set_option linter.unusedSectionVars false
variable (p : Prims) {env : Env} {f : UB} (hf : Holds env f)
include hf

/-- After a binding, its variable is bounded by the bound of its expression. -/
theorem bind_holds {v : Var} {e : Expr} {x : Fr} (hx : e.eval p env = some x) :
    Holds (env.set v x) (learn (forget f [v]) v (ub f e)) := by
  refine learn_holds (forget_holds hf ?_) ?_
  · intro w hw; simp at hw; simp [Env.set, hw]
  · intro B hB
    simp only [Env.set, ite_true]
    exact ub_spec p hf e hx hB

/-- After a range check of a variable passes, the variable is bounded by it. -/
theorem constrain_holds {e : Expr} {r : Range} {x : Fr} (hx : e.eval p env = some x)
    (hh : r.holds x = true) : Holds env (constrainFacts f e r) := by
  unfold constrainFacts
  split
  · next v =>
    simp only [Expr.eval, Option.some.injEq] at hx
    subst hx
    intro u y hm
    simp only [List.mem_cons, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | hm
    · exact Range.ub_holds hh
    · exact hf u y hm
  · exact hf

/-- After an assertion passes, what it says about a variable's bound holds. -/
theorem assert_holds {c : Expr} {x : Fr} (hx : c.eval p env = some x) (ht : asBool x = some true) :
    Holds env (assertFacts f c) := by
  have hx1 : x = 1 := asBool_some ht
  subst hx1
  unfold assertFacts
  split
  · next bits v b =>
    refine learn_holds hf ?_
    intro B hB
    simp only [Option.map_eq_some_iff] at hB
    obtain ⟨B', hB', rfl⟩ := hB
    simp only [Expr.eval, Option.bind_eq_bind, Option.pure_def, Option.bind_some,
      Option.bind_eq_some_iff] at hx
    obtain ⟨y, hy, hx⟩ := hx
    split at hx
    · simp only [Option.some.injEq] at hx
      have hyb := ub_spec p hf b hy hB'
      have : (decide ((env v).val < y.val)) = true := by
        cases hd : decide ((env v).val < y.val)
        · rw [hd] at hx; exact absurd hx (by decide)
        · rfl
      simp only [decide_eq_true_eq] at this
      omega
    · cases hx
  · next bits a v =>
    refine learn_holds hf ?_
    intro B hB
    simp only [Expr.eval, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      Option.some.injEq] at hx
    obtain ⟨xc, hxc, _, rfl, _, rfl, bc, hbc, hsel⟩ := hx
    obtain ⟨xa, ha, _, rfl, hxc⟩ := hxc
    have hbc' := asBool_some hbc
    cases bc
    · -- the comparison is 0: `v ≤ a`
      split at hxc
      · simp only [Option.some.injEq] at hxc
        subst hxc
        have := ub_spec p hf a ha hB
        have hd : decide (xa.val < (env v).val) = false := by
          cases hd : decide (xa.val < (env v).val)
          · rfl
          · rw [hd] at hbc'; exact absurd hbc' (by decide)
        simp only [decide_eq_false_iff_not] at hd
        omega
      · cases hxc
    · simp only [ite_true] at hsel
      exact absurd hsel (by decide)
  · exact hf

/-- After a witness call, its results with a range check are bounded by it,
    and every other variable keeps its bound. -/
theorem witness_holds {outs : List (Var × Option Range)} {r : Env}
    (hout : ∀ w, w ∉ outs.map (·.1) → r w = env w)
    (hck : (outs.map (·.1)).Nodup → ∀ v rg, (v, some rg) ∈ outs → rg.holds (r v) = true) :
    Holds r (witnessBounds outs ++ forget f (outs.map (·.1))) := by
  refine holds_append ?_ (forget_holds hf hout)
  intro v B hm
  unfold witnessBounds at hm
  split at hm
  · next hnd =>
    simp only [List.mem_filterMap] at hm
    obtain ⟨⟨v', ro⟩, hmo, hsome⟩ := hm
    cases ro with
    | none => simp at hsome
    | some rg =>
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsome
      obtain ⟨rfl, rfl⟩ := hsome
      exact Range.ub_holds (hck hnd v' rg hmo)
  · simp at hm

end Post

/-- A successful read leaves the other variables alone and checks the ones it reads. -/
theorem readAll_post {act : Bool} {outs : List (Var × Option Range)} {env r : Env} {st st' : List Fr}
    (h : readAll act env outs st = some (r, st')) :
    (∀ w, w ∉ outs.map (·.1) → r w = env w) ∧
      ((outs.map (·.1)).Nodup → ∀ v rg, (v, some rg) ∈ outs → rg.holds (r v) = true) :=
  ⟨readAll_unchanged h, fun hnd => readAll_checks h hnd⟩

/-- `readAll_post` for the executor's assignment. -/
theorem assign_post {outs : List (Var × Option Range)} {env r : Env} {vals : List Fr}
    (h : Exec.assign env outs vals = some r) :
    (∀ w, w ∉ outs.map (·.1) → r w = env w) ∧
      ((outs.map (·.1)).Nodup → ∀ v rg, (v, some rg) ∈ outs → rg.holds (r v) = true) :=
  readAll_post (Exec.assign_readAll' outs env vals r h)

/-! ## Statements, in the semantics -/

section Run
variable (p : Prims)

/-- A rewritten statement runs exactly as the original, and the bounds after
    it hold of the state it leaves. -/
theorem stmt_exec {f : UB} {s : RunState} (hf : Holds s.env f) (st : Stmt) :
    execAll p (stmt f st).1 s = st.exec p s ∧
      ∀ s', st.exec p s = some s' → Holds s'.env (stmt f st).2 := by
  cases st with
  | bind v hint e =>
      simp only [stmt, execAll_single]
      refine ⟨by simp only [Stmt.exec, tighten_eval p hf], ?_⟩
      intro s' h
      simp only [Stmt.exec, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨x, hx, rfl⟩ := h
      exact bind_holds p hf hx
  | assert c msg =>
      simp only [stmt, execAll_single]
      refine ⟨by simp only [Stmt.exec, tighten_eval p hf], ?_⟩
      intro s' h
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨x, hx, b, hb, h⟩ := h
      cases b
      · simp at h
      · simp only [ite_true, Option.pure_def, Option.some.injEq] at h
        subst h
        exact assert_holds p hf hx hb
  | constrain e r =>
      simp only [stmt]
      split
      · next hc =>
        simp only [implied, Bool.and_eq_true] at hc
        obtain ⟨ht, hw⟩ := hc
        obtain ⟨x, hx⟩ := totalB_eval p hf e ht
        have hh : r.holds x = true := by
          split at hw
          · next B hB => exact within_spec (ub_spec p hf e hx hB) hw
          · cases hw
        have hexec : (Stmt.constrain e r).exec p s = some s := by
          simp [Stmt.exec, Option.bind_eq_bind, hx, hh]
        refine ⟨by rw [hexec]; rfl, ?_⟩
        intro s' h
        rw [hexec] at h; cases h
        exact constrain_holds p hf hx hh
      · simp only [execAll_single]
        refine ⟨by simp only [Stmt.exec, tighten_eval p hf], ?_⟩
        intro s' h
        simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨x, hx, h⟩ := h
        split at h
        · next hh =>
          simp only [Option.pure_def, Option.some.injEq] at h; subst h
          exact constrain_holds p hf hx hh
        · cases h
  | witness g name args outs shape =>
      simp only [stmt, execAll_single]
      refine ⟨trivial, ?_⟩
      intro s' h
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨gx, _, h⟩ := h
      split at h
      · next he =>
        simp only [Option.pure_def, Option.some.injEq] at h; subst h
        have : outs = [] := List.isEmpty_iff.mp he
        subst this
        exact witness_holds hf (fun _ _ => rfl) (by simp)
      · simp only [Option.bind_eq_some_iff] at h
        obtain ⟨act, _, ⟨r, pv⟩, hrd, h⟩ := h
        simp only [Option.pure_def, Option.some.injEq] at h; subst h
        obtain ⟨hout, hck⟩ := readAll_post hrd
        exact witness_holds hf hout hck
  | ledger g reads ops =>
      simp only [stmt, execAll_single]
      refine ⟨trivial, ?_⟩
      intro s' h
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨gx, _, h⟩ := h
      split at h
      · simp only [Option.pure_def, Option.some.injEq] at h; subst h
        exact forget_holds hf (fun _ _ => rfl)
      · simp only [Option.bind_eq_some_iff] at h
        obtain ⟨act, _, ⟨r, pv⟩, hrd, gs, _, h⟩ := h
        simp only [Option.pure_def, Option.some.injEq] at h; subst h
        have hout := (readAll_post hrd).1
        rw [reads_vars] at hout
        exact forget_holds hf hout

/-- The rewritten statements run exactly as the original ones. -/
theorem stmts_exec : ∀ (f : UB) (l : List Stmt) (s : RunState), Holds s.env f →
    execAll p (stmts f l) s = execAll p l s
  | _, [], _, _ => rfl
  | f, st :: rest, s, hf => by
      obtain ⟨h1, h2⟩ := stmt_exec p hf st
      simp only [stmts, execAll_append, h1, execAll, Option.bind_eq_bind]
      cases h : st.exec p s with
      | none => rfl
      | some s' => exact stmts_exec _ rest s' (h2 s' h)

/-- The bounds known at the end hold of the state the statements leave. -/
theorem final_exec : ∀ (f : UB) (l : List Stmt) (s s' : RunState), Holds s.env f →
    execAll p l s = some s' → Holds s'.env (final f l)
  | _, [], s, s', hf, h => by cases h; exact hf
  | f, st :: rest, s, s', hf, h => by
      simp only [execAll, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨s1, h1, h⟩ := h
      exact final_exec _ rest s1 s' ((stmt_exec p hf st).2 s1 h1) h

end Run

/-! ## Statements, in the executor -/

section Executor
variable {ω σ : Type} (p : Prims) (O : Exec.Oracles ω σ)

/-- A statement that asks no oracle is rewritten into such statements. -/
theorem stmt_local {f : UB} {st : Stmt} (hl : Exec.Stmt.isLocal st = true) :
    ∀ x ∈ (stmt f st).1, Exec.Stmt.isLocal x = true := by
  cases st with
  | bind | assert => simp [stmt, Exec.Stmt.isLocal]
  | constrain e r =>
      simp only [stmt]
      split <;> simp [Exec.Stmt.isLocal]
  | witness | ledger => simp [Exec.Stmt.isLocal] at hl

/-- A rewritten statement runs in the executor exactly as the original, and
    the bounds after it hold of the state it leaves. -/
theorem stmt_step {f : UB} {s : Exec.State ω σ} (hf : Holds s.env f) (st : Stmt) :
    Exec.steps p O (stmt f st).1 s = Exec.step p O s st ∧
      ∀ s', Exec.step p O s st = some s' → Holds s'.env (stmt f st).2 := by
  by_cases hl : Exec.Stmt.isLocal st = true
  · have hr := stmt_exec p (s := s.toRun) hf st
    rw [Exec.steps_local p O _ (stmt_local hl), Exec.step_local p O hl, hr.1]
    refine ⟨rfl, ?_⟩
    intro s' h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨r, hr', rfl⟩ := h
    exact hr.2 r hr'
  · cases st with
    | bind | assert | constrain => simp [Exec.Stmt.isLocal] at hl
    | witness g name args outs shape =>
        simp only [stmt, Exec.steps_single]
        refine ⟨trivial, ?_⟩
        intro s' h
        simp only [Exec.step, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨gx, _, h⟩ := h
        split at h
        · next he =>
          have : outs = [] := List.isEmpty_iff.mp he
          subst this
          have hs : s'.env = s.env := by
            split at h
            · simp only [Option.bind_eq_some_iff] at h
              obtain ⟨_, _, ⟨vals, pv⟩, _, h⟩ := h
              split at h
              · simp only [Option.pure_def, Option.some.injEq] at h; subst h; rfl
              · cases h
            · simp only [Option.pure_def, Option.some.injEq] at h; subst h; rfl
          rw [hs]
          exact witness_holds hf (fun _ _ => rfl) (by simp)
        · simp only [Option.bind_eq_some_iff] at h
          obtain ⟨act, _, h⟩ := h
          split at h
          · simp only [Option.bind_eq_some_iff] at h
            obtain ⟨_, _, ⟨vals, pv⟩, _, r, hasg, h⟩ := h
            simp only [Option.pure_def, Option.some.injEq] at h; subst h
            obtain ⟨hout, hck⟩ := assign_post hasg
            exact witness_holds hf hout hck
          · simp only [Option.bind_eq_some_iff] at h
            obtain ⟨r, hasg, h⟩ := h
            simp only [Option.pure_def, Option.some.injEq] at h; subst h
            obtain ⟨hout, hck⟩ := assign_post hasg
            exact witness_holds hf hout hck
    | ledger g reads ops =>
        simp only [stmt, Exec.steps_single]
        refine ⟨trivial, ?_⟩
        intro s' h
        simp only [Exec.step, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨gx, _, h⟩ := h
        split at h
        · simp only [Option.pure_def, Option.some.injEq] at h; subst h
          exact forget_holds hf (fun _ _ => rfl)
        · simp only [Option.bind_eq_some_iff] at h
          obtain ⟨act, _, h⟩ := h
          split at h
          · simp only [Option.bind_eq_some_iff] at h
            obtain ⟨_, _, ⟨vals, lg⟩, _, r, hasg, gs, _, h⟩ := h
            simp only [Option.pure_def, Option.some.injEq] at h; subst h
            have hout := (assign_post hasg).1
            rw [reads_vars] at hout
            exact forget_holds hf hout
          · simp only [Option.bind_eq_some_iff] at h
            obtain ⟨r, hasg, gs, _, h⟩ := h
            simp only [Option.pure_def, Option.some.injEq] at h; subst h
            have hout := (assign_post hasg).1
            rw [reads_vars] at hout
            exact forget_holds hf hout

/-- The rewritten statements run in the executor exactly as the original ones. -/
theorem stmts_steps : ∀ (f : UB) (l : List Stmt) (s : Exec.State ω σ), Holds s.env f →
    Exec.steps p O (stmts f l) s = Exec.steps p O l s
  | _, [], _, _ => rfl
  | f, st :: rest, s, hf => by
      obtain ⟨h1, h2⟩ := stmt_step p O hf st
      simp only [stmts, Exec.steps_append, h1, Exec.steps, Option.bind_eq_bind]
      cases h : Exec.step p O s st with
      | none => rfl
      | some s' => exact stmts_steps _ rest s' (h2 s' h)

/-- The bounds known at the end hold of the state the executor leaves. -/
theorem final_steps : ∀ (f : UB) (l : List Stmt) (s s' : Exec.State ω σ), Holds s.env f →
    Exec.steps p O l s = some s' → Holds s'.env (final f l)
  | _, [], s, s', hf, h => by cases h; exact hf
  | f, st :: rest, s, s', hf, h => by
      simp only [Exec.steps, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨s1, h1, h⟩ := h
      exact final_steps _ rest s1 s' ((stmt_step p O hf st).2 s1 h1) h

end Executor

/-! ## Ledger well-formedness -/

/-- The statements a statement is rewritten into have its ledger problems:
    none, unless it is a ledger statement, which is kept as it is. -/
theorem stmt_ledgerProblem {f : UB} (st : Stmt) :
    ∀ x ∈ (stmt f st).1, x.ledgerProblem = st.ledgerProblem := by
  cases st with
  | bind | assert | witness | ledger => simp [stmt, Stmt.ledgerProblem]
  | constrain e r =>
      simp only [stmt]
      split <;> simp [Stmt.ledgerProblem]

theorem stmts_ledgerProblem : ∀ (f : UB) (l : List Stmt), (∀ s ∈ l, s.ledgerProblem = none) →
    ∀ x ∈ stmts f l, x.ledgerProblem = none
  | _, [], _ => by simp [stmts]
  | f, st :: rest, h => by
      intro x hx
      simp only [stmts, List.mem_append] at hx
      rcases hx with hx | hx
      · rw [stmt_ledgerProblem st x hx]; exact h st (by simp)
      · exact stmts_ledgerProblem _ rest (fun s hs => h s (by simp [hs])) x hx

theorem checkLedgerFrom_ok (name : String) : ∀ (i : Nat) (l : List Stmt),
    checkLedgerFrom name i l = .ok () ↔ ∀ s ∈ l, s.ledgerProblem = none
  | _, [] => by simp [checkLedgerFrom]
  | i, st :: rest => by
      simp only [checkLedgerFrom, List.mem_cons, forall_eq_or_imp]
      split
      · next why h => simp [h]
      · next h => rw [checkLedgerFrom_ok name (i + 1) rest]; simp [h]

end Bounds

open Damp.Zkir (Prims)

/-- The rewritten circuit runs exactly as the original. -/
theorem Circuit.bounds_run (p : Prims) (c : Circuit) (inputs priv pub : List Fr) :
    c.bounds.run p inputs priv pub = c.run p inputs priv pub := by
  simp only [Circuit.run, Circuit.bounds, List.toList_toArray, Option.bind_eq_bind]
  cases bindInputs (fun _ => 0) c.inputs inputs with
  | none => rfl
  | some env0 =>
      simp only [Option.bind_some]
      rw [Bounds.stmts_exec p [] _ _ (Bounds.holds_nil _)]
      cases h : execAll p c.body.toList { env := env0, priv, pub } with
      | none => rfl
      | some s' =>
          simp only [Option.bind_some]
          rw [Bounds.tighten_evalList p (Bounds.final_exec p [] _ _ _ (Bounds.holds_nil _) h)]

/-- The executor runs the rewritten circuit exactly as the original. -/
theorem Circuit.bounds_runExec {ω σ : Type} (p : Prims) (O : Exec.Oracles ω σ) (c : Circuit)
    (inputs : List Fr) (private_ : ω) (ledger : σ) :
    Exec.run p O c.bounds inputs private_ ledger = Exec.run p O c inputs private_ ledger := by
  simp only [Exec.run, Circuit.bounds, List.toList_toArray, Option.bind_eq_bind]
  cases bindInputs (fun _ => 0) c.inputs inputs with
  | none => rfl
  | some env0 =>
      simp only [Option.bind_some]
      rw [Bounds.stmts_steps p O [] _ _ (Bounds.holds_nil _)]
      cases h : Exec.steps p O c.body.toList { env := env0, private_, ledger } with
      | none => rfl
      | some s' =>
          simp only [Option.bind_some]
          rw [Bounds.tighten_evalList p (Bounds.final_steps p O [] _ _ _ (Bounds.holds_nil _) h)]

/-- The value-range pass is sound: it changes neither what a run of any
    circuit produces, nor what the executor does with it, for any inputs,
    transcripts and oracles. -/
theorem Circuit.bounds_sound : Pass.Sound Circuit.bounds :=
  ⟨fun p c i pr pu => by rw [Circuit.bounds_run],
   fun p O c i w l => by rw [Circuit.bounds_runExec]⟩

/-- The pass keeps every ledger statement as it is, so a circuit that passes
    `checkLedger` still does. -/
theorem Circuit.bounds_checkLedger (c : Circuit) (h : c.checkLedger = .ok ()) :
    c.bounds.checkLedger = .ok () := by
  simp only [Circuit.checkLedger, Circuit.bounds, List.toList_toArray] at h ⊢
  rw [Bounds.checkLedgerFrom_ok] at h ⊢
  exact Bounds.stmts_ledgerProblem [] _ h

end Damp.IR
