/-
`Circuit.asserts` is sound.

The pass rewrites expressions in place and drops `assert`s known to pass; it
never touches a binding. So the rewritten circuit runs through exactly the
same environments as the original, and the proof is an equality of runs
(`Circuit.asserts_run`, `Exec.asserts_run`), under the invariant that every
fact the pass carries (`Known.Holds`) is true of the current environment.

A rewritten expression has exactly the value of the original, failures
included (`Asserts.Known.rw_eval`): a fact `(e, r)` says `e` has a value and `r` has the
same one; a rule that drops a subexpression requires it to be known to have a
value (`Asserts.Known.evals_eval`), because it occurs in an expression evaluated
earlier (`hasSub_eval`: every subexpression of an expression with a
value has one) or is built from such by operations that cannot fail.
-/
import Damp.Optimize.Asserts
import Damp.Proofs.Optimize.Sound
import Damp.IR.LedgerCheck

namespace Damp.IR.Asserts
open Damp.Zkir (Prims fitsBits)

/-! ## Expressions -/

section Exprs
variable (p : Prims) (env : Env)

mutual
/-- Dropping the `disclose` markers does not change a value. -/
theorem strip_eval : ∀ e : Expr, (strip e).eval p env = e.eval p env
  | .disclose a => by simp only [strip, Expr.eval, strip_eval a]
  | .add a b => by simp only [strip, Expr.eval, strip_eval a, strip_eval b]
  | .mul a b => by simp only [strip, Expr.eval, strip_eval a, strip_eval b]
  | .eq a b => by simp only [strip, Expr.eval, strip_eval a, strip_eval b]
  | .lt _ a b => by simp only [strip, Expr.eval, strip_eval a, strip_eval b]
  | .select c a b => by
      simp only [strip, Expr.eval, strip_eval c, strip_eval a, strip_eval b]
  | .neg a => by simp only [strip, Expr.eval, strip_eval a]
  | .divmod _ _ a => by simp only [strip, Expr.eval, strip_eval a]
  | .hash xs => by simp only [strip, Expr.eval, stripList_eval xs]
  | .phash _ _ xs => by simp only [strip, Expr.eval, stripList_eval xs]
  | .var _ => rfl
  | .const _ => rfl
  | .invalid _ => rfl
/-- `strip_eval` for lists. -/
theorem stripList_eval : ∀ xs : List Expr,
    Expr.evalList p env (stripList xs) = Expr.evalList p env xs
  | [] => rfl
  | x :: xs => by simp only [stripList, Expr.evalList, strip_eval x, stripList_eval xs]
end

mutual
/-- Every subexpression of an expression that has a value has one: evaluation
    evaluates every operand, both branches of a conditional included. -/
theorem hasSub_eval : ∀ (e s : Expr) (x : Fr), e.eval p env = some x → hasSub e s = true →
    ∃ y, s.eval p env = some y
  | .var _, s, x, h, hs | .const _, s, x, h, hs | .invalid _, s, x, h, hs => by
      simp only [hasSub, beq_iff_eq] at hs; subst hs; exact ⟨x, h⟩
  | .disclose a, s, x, h, hs => by
      have h0 := h
      simp only [Expr.eval] at h
      simp only [hasSub, Bool.or_eq_true, beq_iff_eq] at hs
      rcases hs with rfl | hs
      · exact ⟨x, h0⟩
      · exact hasSub_eval a s x h hs
  | .neg a, s, x, h, hs => by
      have h0 := h
      simp only [Expr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨xa, ha, _⟩ := h
      simp only [hasSub, Bool.or_eq_true, beq_iff_eq] at hs
      rcases hs with rfl | hs
      · exact ⟨x, h0⟩
      · exact hasSub_eval a s xa ha hs
  | .divmod _ _ a, s, x, h, hs => by
      have h0 := h
      simp only [Expr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨xa, ha, _⟩ := h
      simp only [hasSub, Bool.or_eq_true, beq_iff_eq] at hs
      rcases hs with rfl | hs
      · exact ⟨x, h0⟩
      · exact hasSub_eval a s xa ha hs
  | .add a b, s, x, h, hs | .mul a b, s, x, h, hs | .eq a b, s, x, h, hs
  | .lt _ a b, s, x, h, hs => by
      have h0 := h
      simp only [Expr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨xa, ha, xb, hb, _⟩ := h
      simp only [hasSub, Bool.or_eq_true, beq_iff_eq] at hs
      rcases hs with (rfl | hs) | hs
      · exact ⟨x, h0⟩
      · exact hasSub_eval a s xa ha hs
      · exact hasSub_eval b s xb hb hs
  | .select c a b, s, x, h, hs => by
      have h0 := h
      simp only [Expr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨xc, hc, xa, ha, xb, hb, _⟩ := h
      simp only [hasSub, Bool.or_eq_true, beq_iff_eq] at hs
      rcases hs with ((rfl | hs) | hs) | hs
      · exact ⟨x, h0⟩
      · exact hasSub_eval c s xc hc hs
      · exact hasSub_eval a s xa ha hs
      · exact hasSub_eval b s xb hb hs
  | .hash xs, s, x, h, hs | .phash _ _ xs, s, x, h, hs => by
      have h0 := h
      simp only [Expr.eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨ys, hys, _⟩ := h
      simp only [hasSub, Bool.or_eq_true, beq_iff_eq] at hs
      rcases hs with rfl | hs
      · exact ⟨x, h0⟩
      · exact hasSubList_eval xs s ys hys hs
/-- `hasSub_eval` for lists. -/
theorem hasSubList_eval : ∀ (xs : List Expr) (s : Expr) (ys : List Fr),
    Expr.evalList p env xs = some ys → hasSubList xs s = true → ∃ y, s.eval p env = some y
  | [], _, _, _, hs => by simp [hasSubList] at hs
  | x :: xs, s, ys, h, hs => by
      simp only [Expr.evalList, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨y, hy, zs, hzs, _⟩ := h
      simp only [hasSubList, Bool.or_eq_true] at hs
      rcases hs with hs | hs
      · exact hasSub_eval x s y hy hs
      · exact hasSubList_eval xs s zs hzs hs
end

end Exprs

/-! ## Facts -/

section Facts
variable (p : Prims)

/-- Every fact is true of the environment. -/
structure Known.Holds (K : Known) (env : Env) : Prop where
  eqs : ∀ q ∈ K.eqs, ∃ x, q.1.eval p env = some x ∧ q.2.eval p env = some x
  evald : ∀ e ∈ K.evald, ∃ x, e.eval p env = some x
  ranged : CheckedHolds p env K.ranged

theorem Known.holds_empty (env : Env) : ({} : Known).Holds p env :=
  ⟨fun _ h => (nomatch h), fun _ h => (nomatch h), fun _ _ h => (nomatch h)⟩

variable {p}

/-- Something that occurs in an expression known to have a value has one. -/
theorem Known.seen_eval {K : Known} {env : Env} (h : K.Holds p env) {e : Expr}
    (hs : K.seen e = true) : ∃ x, e.eval p env = some x := by
  simp only [Known.seen, Bool.or_eq_true, List.any_eq_true] at hs
  rcases hs with ⟨e0, hm, hsub⟩ | ⟨q, hm, hsub⟩
  · obtain ⟨x, hx⟩ := h.evald e0 hm
    exact hasSub_eval p env e0 e x hx hsub
  · obtain ⟨x, hx, _⟩ := h.eqs q hm
    exact hasSub_eval p env q.1 e x hx hsub

/-- What `fits` says fits does. -/
theorem Known.fits_eval {K : Known} {env : Env} (h : K.Holds p env) {n : Nat} {e : Expr} {x : Fr}
    (hf : K.fits n e = true) (he : e.eval p env = some x) : fitsBits x n = true := by
  have ranged : (K.ranged.any fun q => q.1 == e && q.2.implies (.bits n)) = true →
      fitsBits x n = true := by
    intro ha
    simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at ha
    obtain ⟨⟨e0, r⟩, hm, he0, himp⟩ := ha
    simp only at he0 himp
    subst he0
    obtain ⟨y, hy, hr⟩ := h.ranged e0 r hm
    rw [he, Option.some.injEq] at hy
    subst hy
    exact Range.implies_holds r (.bits n) _ himp hr
  cases e with
  | const k =>
      simp only [Known.fits] at hf
      simp only [Expr.eval, Option.some.injEq] at he
      subst he; exact hf
  | _ => exact ranged hf

/-- What `evals` says has a value has one. -/
theorem Known.evals_eval {K : Known} {env : Env} (h : K.Holds p env) :
    ∀ e : Expr, K.evals e = true → ∃ x, e.eval p env = some x
  | .var v, _ => ⟨env v, rfl⟩
  | .const _, _ => ⟨_, rfl⟩
  | .add a b, he => by
      simp only [Known.evals, Bool.or_eq_true, Bool.and_eq_true] at he
      rcases he with hs | ⟨ha, hb⟩
      · exact Known.seen_eval h hs
      · obtain ⟨x, hx⟩ := Known.evals_eval h a ha
        obtain ⟨y, hy⟩ := Known.evals_eval h b hb
        exact ⟨x + y, by simp [Expr.eval, Option.bind_eq_bind, Option.pure_def, hx, hy]⟩
  | .mul a b, he => by
      simp only [Known.evals, Bool.or_eq_true, Bool.and_eq_true] at he
      rcases he with hs | ⟨ha, hb⟩
      · exact Known.seen_eval h hs
      · obtain ⟨x, hx⟩ := Known.evals_eval h a ha
        obtain ⟨y, hy⟩ := Known.evals_eval h b hb
        exact ⟨x * y, by simp [Expr.eval, Option.bind_eq_bind, Option.pure_def, hx, hy]⟩
  | .eq a b, he => by
      simp only [Known.evals, Bool.or_eq_true, Bool.and_eq_true] at he
      rcases he with hs | ⟨ha, hb⟩
      · exact Known.seen_eval h hs
      · obtain ⟨x, hx⟩ := Known.evals_eval h a ha
        obtain ⟨y, hy⟩ := Known.evals_eval h b hb
        exact ⟨Fr.ofBool (decide (x = y)), by simp [Expr.eval, Option.bind_eq_bind, Option.pure_def, hx, hy]⟩
  | .lt n a b, he => by
      simp only [Known.evals, Bool.or_eq_true, Bool.and_eq_true] at he
      rcases he with hs | ⟨⟨⟨ha, hb⟩, hfa⟩, hfb⟩
      · exact Known.seen_eval h hs
      · obtain ⟨x, hx⟩ := Known.evals_eval h a ha
        obtain ⟨y, hy⟩ := Known.evals_eval h b hb
        exact ⟨Fr.ofBool (decide (x.val < y.val)), by simp [Expr.eval, Option.bind_eq_bind, Option.pure_def, hx, hy,
          Known.fits_eval h hfa hx, Known.fits_eval h hfb hy]⟩
  | .neg a, he => by
      simp only [Known.evals, Bool.or_eq_true] at he
      rcases he with hs | ha
      · exact Known.seen_eval h hs
      · obtain ⟨x, hx⟩ := Known.evals_eval h a ha
        exact ⟨-x, by simp [Expr.eval, Option.bind_eq_bind, Option.pure_def, hx]⟩
  | .disclose a, he => by
      simp only [Known.evals, Bool.or_eq_true] at he
      rcases he with hs | ha
      · exact Known.seen_eval h hs
      · obtain ⟨x, hx⟩ := Known.evals_eval h a ha
        exact ⟨x, by simp [Expr.eval, hx]⟩
  | .divmod q n a, he => by
      simp only [Known.evals, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at he
      rcases he with hs | ⟨hn, ha⟩
      · exact Known.seen_eval h hs
      · obtain ⟨x, hx⟩ := Known.evals_eval h a ha
        exact ⟨Fr.ofNat (if q then x.val / 2 ^ n else x.val % 2 ^ n),
          by simp [Expr.eval, Option.bind_eq_bind, Option.pure_def, hx, hn]⟩
  | .select c a b, he => by
      simp only [Known.evals, Bool.or_eq_true, Bool.and_eq_true] at he
      rcases he with hs | ⟨⟨⟨hcb, hc⟩, ha⟩, hb⟩
      · exact Known.seen_eval h hs
      · obtain ⟨xc, hxc⟩ := Known.evals_eval h c hc
        obtain ⟨x, hx⟩ := Known.evals_eval h a ha
        obtain ⟨y, hy⟩ := Known.evals_eval h b hb
        obtain ⟨bc, hbc, _⟩ := asBool_of_zero_or_one
          (Expr.isBool_eval p env [] (boolsHold_nil env) c xc hcb hxc)
        exact ⟨if bc then x else y,
          by simp [Expr.eval, Option.bind_eq_bind, Option.pure_def, hxc, hx, hy, hbc]⟩
  | .hash xs, he => by
      simp only [Known.evals, Bool.or_eq_true] at he
      rcases he with hs | ht
      · exact Known.seen_eval h hs
      · obtain ⟨ys, hys⟩ := Expr.totalList_eval p env [] (boolsHold_nil env) xs ht
        exact ⟨p.transientHash ys, by simp [Expr.eval, Option.bind_eq_bind, Option.pure_def, hys]⟩
  | .phash hi al xs, he => Known.seen_eval h (e := .phash hi al xs) he
  | .invalid m, he => Known.seen_eval h (e := .invalid m) he

/-- Known to have a value, before or after rewriting. -/
theorem Known.evals_or {K : Known} {env : Env} (h : K.Holds p env) {e e' : Expr}
    (he : e'.eval p env = e.eval p env) (hb : (K.evals e || K.evals e') = true) :
    ∃ x, e'.eval p env = some x := by
  simp only [Bool.or_eq_true] at hb
  rcases hb with hb | hb
  · rw [he]; exact Known.evals_eval h e hb
  · exact Known.evals_eval h e' hb

theorem Known.isZero_eq {e : Expr} (h : Known.isZero e = true) : ∃ k, e = .const k ∧ Fr.ofInt k = 0 := by
  cases e <;> simp_all [Known.isZero]

theorem Known.isOne_eq {e : Expr} (h : Known.isOne e = true) : ∃ k, e = .const k ∧ Fr.ofInt k = 1 := by
  cases e <;> simp_all [Known.isOne]

theorem asBool_true {x : Fr} (h : asBool x = some true) : x = 1 := by
  unfold asBool at h
  split at h
  · cases h
  · split at h
    · assumption
    · cases h

theorem asBool_false {x : Fr} (h : asBool x = some false) : x = 0 := by
  unfold asBool at h
  split at h
  · assumption
  · split at h <;> cases h

section Rules
variable (env : Env)

/-- `mkMul` drops a factor only when it is known to have a value. -/
theorem Known.mkMul_eval {a b : Expr} {ea eb : Bool}
    (ha : ea = true → ∃ x, a.eval p env = some x) (hb : eb = true → ∃ x, b.eval p env = some x) :
    (Known.mkMul a b ea eb).eval p env = (Expr.mul a b).eval p env := by
  unfold Known.mkMul
  split
  · next hc =>
    simp only [Bool.and_eq_true] at hc
    obtain ⟨k, rfl, hk⟩ := Known.isZero_eq hc.1
    obtain ⟨y, hy⟩ := hb hc.2
    simp [Expr.eval, Option.bind_eq_bind, Option.pure_def, hy, hk, Fr.ofInt_zero, Fr.zero_mul]
  · split
    · next hc =>
      simp only [Bool.and_eq_true] at hc
      obtain ⟨k, rfl, hk⟩ := Known.isZero_eq hc.1
      obtain ⟨x, hx⟩ := ha hc.2
      simp [Expr.eval, Option.bind_eq_bind, Option.pure_def, hx, hk, Fr.ofInt_zero, Fr.mul_zero]
    · rfl

/-- `mkEq` folds `e == e` only when `e` is known to have a value. -/
theorem Known.mkEq_eval {a b : Expr} {ea : Bool} (ha : ea = true → ∃ x, a.eval p env = some x) :
    (Known.mkEq a b ea).eval p env = (Expr.eq a b).eval p env := by
  unfold Known.mkEq
  split
  · next hc =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨rfl, he⟩ := hc
    obtain ⟨x, hx⟩ := ha he
    simp [Expr.eval, Option.bind_eq_bind, Option.pure_def, hx, Fr.ofBool, Fr.ofInt_one]
  · rfl

/-- `mkSel` drops a branch or the condition only when it is known to have a value. -/
theorem Known.mkSel_eval {c a b : Expr} {ec ea eb : Bool}
    (hc : ec = true → ∃ x, c.eval p env = some x)
    (ha : ea = true → ∃ x, a.eval p env = some x) (hb : eb = true → ∃ x, b.eval p env = some x) :
    (Known.mkSel c a b ec ea eb).eval p env = (Expr.select c a b).eval p env := by
  unfold Known.mkSel
  split
  · next h1 =>
    simp only [Bool.and_eq_true] at h1
    obtain ⟨k, rfl, hk⟩ := Known.isOne_eq h1.1
    obtain ⟨y, hy⟩ := hb h1.2
    simp only [Expr.eval, Option.bind_eq_bind, Option.pure_def, hk, hy]
    cases a.eval p env <;> simp [asBool_one]
  · split
    · next h1 =>
      simp only [Bool.and_eq_true] at h1
      obtain ⟨k, rfl, hk⟩ := Known.isZero_eq h1.1
      obtain ⟨x, hx⟩ := ha h1.2
      simp only [Expr.eval, Option.bind_eq_bind, Option.pure_def, hk, hx]
      cases b.eval p env <;> simp [asBool_zero]
    · split
      · next h1 =>
        simp only [Bool.and_eq_true, beq_iff_eq] at h1
        obtain ⟨⟨rfl, hec⟩, hcb⟩ := h1
        obtain ⟨xc, hxc⟩ := hc hec
        obtain ⟨bc, hbc, _⟩ := asBool_of_zero_or_one
          (Expr.isBool_eval p env [] (boolsHold_nil env) c xc hcb hxc)
        simp only [Expr.eval, Option.bind_eq_bind, Option.pure_def, hxc, hbc, Option.bind_some]
        cases a.eval p env <;> cases bc <;> rfl
      · rfl

end Rules

/-- A replacement found for an expression has its value. -/
theorem Known.lookup_eval {K : Known} {env : Env} (h : K.Holds p env) {e r : Expr}
    (hl : K.lookup e = some r) : r.eval p env = e.eval p env := by
  simp only [Known.lookup, Option.map_eq_some_iff] at hl
  obtain ⟨q, hq, rfl⟩ := hl
  have hm := List.mem_of_find?_eq_some hq
  have hp := List.find?_some hq
  simp only [beq_iff_eq] at hp
  obtain ⟨x, h1, h2⟩ := h.eqs q hm
  rw [h2, ← hp, h1]

mutual
/-- Rewriting with facts that hold does not change a value, nor whether there is one. -/
theorem Known.rwS_eval {K : Known} {env : Env} (h : K.Holds p env) :
    ∀ e : Expr, (K.rwS e).eval p env = e.eval p env
  | .add a b => by
      rw [Known.rwS]; split
      · next r hr => exact Known.lookup_eval h hr
      · simp only [Expr.eval, Known.rwS_eval h a, Known.rwS_eval h b]
  | .mul a b => by
      rw [Known.rwS]; split
      · next r hr => exact Known.lookup_eval h hr
      · dsimp only
        rw [Known.mkMul_eval env (Known.evals_or h (Known.rwS_eval h a))
          (Known.evals_or h (Known.rwS_eval h b))]
        simp only [Expr.eval, Known.rwS_eval h a, Known.rwS_eval h b]
  | .eq a b => by
      rw [Known.rwS]; split
      · next r hr => exact Known.lookup_eval h hr
      · dsimp only
        rw [Known.mkEq_eval env (Known.evals_or h (Known.rwS_eval h a))]
        simp only [Expr.eval, Known.rwS_eval h a, Known.rwS_eval h b]
  | .select c a b => by
      rw [Known.rwS]; split
      · next r hr => exact Known.lookup_eval h hr
      · dsimp only
        rw [Known.mkSel_eval env (Known.evals_or h (Known.rwS_eval h c))
          (Known.evals_or h (Known.rwS_eval h a)) (Known.evals_or h (Known.rwS_eval h b))]
        simp only [Expr.eval, Known.rwS_eval h c, Known.rwS_eval h a, Known.rwS_eval h b]
  | .lt _ a b => by
      rw [Known.rwS]; split
      · next r hr => exact Known.lookup_eval h hr
      · simp only [Expr.eval, Known.rwS_eval h a, Known.rwS_eval h b]
  | .neg a => by
      rw [Known.rwS]; split
      · next r hr => exact Known.lookup_eval h hr
      · simp only [Expr.eval, Known.rwS_eval h a]
  | .divmod _ _ a => by
      rw [Known.rwS]; split
      · next r hr => exact Known.lookup_eval h hr
      · simp only [Expr.eval, Known.rwS_eval h a]
  | .disclose a => by
      rw [Known.rwS]; split
      · next r hr => exact Known.lookup_eval h hr
      · simp only [Expr.eval, Known.rwS_eval h a]
  | .hash xs => by
      rw [Known.rwS]; split
      · next r hr => exact Known.lookup_eval h hr
      · simp only [Expr.eval, Known.rwSList_eval h xs]
  | .phash _ _ xs => by
      rw [Known.rwS]; split
      · next r hr => exact Known.lookup_eval h hr
      · simp only [Expr.eval, Known.rwSList_eval h xs]
  | .var _ => by
      rw [Known.rwS]; split
      · next r hr => exact Known.lookup_eval h hr
      · rfl
  | .const _ => by
      rw [Known.rwS]; split
      · next r hr => exact Known.lookup_eval h hr
      · rfl
  | .invalid _ => by
      rw [Known.rwS]; split
      · next r hr => exact Known.lookup_eval h hr
      · rfl
/-- `Known.rwS_eval` for lists. -/
theorem Known.rwSList_eval {K : Known} {env : Env} (h : K.Holds p env) :
    ∀ xs : List Expr, Expr.evalList p env (K.rwSList xs) = Expr.evalList p env xs
  | [] => rfl
  | x :: xs => by
      simp only [Known.rwSList, Expr.evalList, Known.rwS_eval h x, Known.rwSList_eval h xs]
end

/-- Rewriting with facts that hold does not change a value, nor whether there is one. -/
theorem Known.rw_eval {K : Known} {env : Env} (h : K.Holds p env) (e : Expr) :
    (K.rw e).eval p env = e.eval p env := by
  unfold Known.rw
  rw [Known.rwS_eval h, strip_eval]

theorem Known.rw_evalList {K : Known} {env : Env} (h : K.Holds p env) :
    ∀ xs : List Expr, Expr.evalList p env (xs.map K.rw) = Expr.evalList p env xs
  | [] => rfl
  | x :: xs => by simp only [List.map, Expr.evalList, Known.rw_eval h x, Known.rw_evalList h xs]

end Facts

/-! ## Keeping the facts true -/

section Keep
variable {p : Prims}

/-- One more fact `e ↦ r`, where both have the value `x`. -/
theorem Known.cons_holds {K : Known} {env : Env} (h : K.Holds p env) {e r : Expr} {x : Fr}
    (he : e.eval p env = some x) (hr : r.eval p env = some x) :
    ({ K with eqs := (e, r) :: K.eqs } : Known).Holds p env where
  eqs := by
    intro q hq
    simp only [List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact ⟨x, he, hr⟩
    · exact h.eqs q hq
  evald := h.evald
  ranged := h.ranged

theorem constOther_eval {e : Expr} {k : Int} (env : Env) (h : Known.constOther e k = true) :
    ∃ j, e.eval p env = some (Fr.ofInt j) ∧ Fr.ofInt j ≠ Fr.ofInt k := by
  cases e with
  | const j => exact ⟨j, rfl, by simpa [Known.constOther] using h⟩
  | _ => simp [Known.constOther] at h

theorem constVal_eq {e : Expr} {k : Int} (h : Known.constVal? e = some k) : e = .const k := by
  cases e <;> simp_all [Known.constVal?]

/-- Taking an established value apart keeps the facts true. -/
theorem Known.assumeConst_holds {env : Env} :
    ∀ (e : Expr) (K : Known) (k : Int), K.Holds p env → e.eval p env = some (Fr.ofInt k) →
      (K.assumeConst e k).Holds p env
  | .select c a b, K, k, hK, he => by
      have hK1 := Known.cons_holds hK he (rfl : (Expr.const k).eval p env = some (Fr.ofInt k))
      have he' := he
      simp only [Expr.eval, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        Option.some.injEq] at he'
      obtain ⟨xc, hc, xa, ha, xb, hb, bc, hbc, hres⟩ := he'
      unfold Known.assumeConst
      dsimp only
      split
      · next ho =>
        obtain ⟨j, hj, hne⟩ := constOther_eval env ho
        rw [hb, Option.some.injEq] at hj
        cases bc with
        | false => simp only [Bool.false_eq_true, ite_false] at hres; exact absurd (hj ▸ hres) hne
        | true =>
          simp only [ite_true] at hres
          have hc1 : xc = 1 := asBool_true hbc
          refine Known.assumeConst_holds a _ k (Known.assumeConst_holds c _ 1 hK1 ?_) (by rw [ha, hres])
          rw [hc, hc1, Fr.ofInt_one]
      · split
        · next _ ho =>
          obtain ⟨j, hj, hne⟩ := constOther_eval env ho
          rw [ha, Option.some.injEq] at hj
          cases bc with
          | true => simp only [ite_true] at hres; exact absurd (hj ▸ hres) hne
          | false =>
            simp only [Bool.false_eq_true, ite_false] at hres
            have hc0 : xc = 0 := asBool_false hbc
            refine Known.assumeConst_holds b _ k (Known.assumeConst_holds c _ 0 hK1 ?_) (by rw [hb, hres])
            rw [hc, hc0, Fr.ofInt_zero]
        · exact hK1
  | .eq a b, K, k, hK, he => by
      have hK1 := Known.cons_holds hK he (rfl : (Expr.const k).eval p env = some (Fr.ofInt k))
      have he' := he
      simp only [Expr.eval, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        Option.some.injEq] at he'
      obtain ⟨xa, ha, xb, hb, hres⟩ := he'
      unfold Known.assumeConst
      dsimp only
      split
      · next hk1 =>
        have hab : xa = xb := by
          rw [hk1] at hres
          by_cases hne : xa = xb
          · exact hne
          · rw [decide_eq_false hne] at hres
            exact absurd hres Fr.zero_ne_one
        cases hvb : Known.constVal? b with
        | some kb =>
            simp only
            have := constVal_eq hvb; subst this
            simp only [Expr.eval, Option.some.injEq] at hb
            exact Known.assumeConst_holds a _ kb hK1 (by rw [ha, hab, hb])
        | none =>
          cases hva : Known.constVal? a with
          | some ka =>
              simp only
              have := constVal_eq hva; subst this
              simp only [Expr.eval, Option.some.injEq] at ha
              exact Known.assumeConst_holds b _ ka hK1 (by rw [hb, ← hab, ha])
          | none => exact hK1
      · exact hK1
  | .var _, K, k, hK, he | .const _, K, k, hK, he | .add .., K, k, hK, he
  | .mul .., K, k, hK, he | .neg _, K, k, hK, he | .lt .., K, k, hK, he
  | .hash _, K, k, hK, he | .phash .., K, k, hK, he | .divmod .., K, k, hK, he
  | .invalid _, K, k, hK, he | .disclose _, K, k, hK, he => by
      unfold Known.assumeConst
      exact Known.cons_holds hK he rfl

theorem notin_of_all {l vs : List Var} (h : l.all (!vs.contains ·) = true) : ∀ w ∈ l, w ∉ vs := by
  intro w hw hv
  have := List.all_eq_true.mp h w hw
  simp [hv] at this

/-- After binding the variables `vs`, the facts that do not mention them still hold. -/
theorem Known.forget_holds {K : Known} {env env' : Env} {vs : List Var} (h : K.Holds p env)
    (hun : ∀ w, w ∉ vs → env' w = env w) : (K.forget vs).Holds p env' where
  eqs := by
    intro q hq
    simp only [Known.forget, List.mem_filter] at hq
    have hn := notin_of_all hq.2
    obtain ⟨x, h1, h2⟩ := h.eqs q hq.1
    refine ⟨x, ?_, ?_⟩
    · rw [Expr.eval_congr_vars p q.1 (e₂ := env) (fun w hw => hun w (hn w (List.mem_append_left _ hw))), h1]
    · rw [Expr.eval_congr_vars p q.2 (e₂ := env) (fun w hw => hun w (hn w (List.mem_append_right _ hw))), h2]
  evald := by
    intro e he
    simp only [Known.forget, List.mem_filter] at he
    obtain ⟨x, h1⟩ := h.evald e he.1
    exact ⟨x, by rw [Expr.eval_congr_vars p e (e₂ := env) (fun w hw => hun w (notin_of_all he.2 w hw)), h1]⟩
  ranged := by
    intro e r he
    simp only [Known.forget, List.mem_filter] at he
    obtain ⟨x, h1, h2⟩ := h.ranged e r he.1
    exact ⟨x, by rw [Expr.eval_congr_vars p e (e₂ := env) (fun w hw => hun w (notin_of_all he.2 w hw)), h1], h2⟩

/-- After a statement that evaluated `es` and bound `vs`. -/
theorem Known.after_holds {K : Known} {env env' : Env} {es : List Expr} {vs : List Var}
    (h : K.Holds p env) (hes : ∀ e ∈ es, ∃ x, e.eval p env = some x)
    (hun : ∀ w, w ∉ vs → env' w = env w) : (K.after es vs).Holds p env' := by
  unfold Known.after
  refine Known.forget_holds ⟨h.eqs, ?_, h.ranged⟩ hun
  intro e he
  simp only [List.mem_append] at he
  rcases he with he | he
  · exact hes e he
  · exact h.evald e he

/-- More range facts that hold. -/
theorem Known.ranged_holds {K : Known} {env : Env} (h : K.Holds p env) {rs : List (Expr × Range)}
    (hr : CheckedHolds p env rs) : ({ K with ranged := rs ++ K.ranged } : Known).Holds p env where
  eqs := h.eqs
  evald := h.evald
  ranged := by
    intro e r hm
    simp only [List.mem_append] at hm
    rcases hm with hm | hm
    · exact hr e r hm
    · exact h.ranged e r hm

/-- An expression and its rewrite both have the value the original had. -/
theorem Known.pair_evals {K : Known} {env : Env} (h : K.Holds p env) {e : Expr} {x : Fr}
    (he : e.eval p env = some x) : ∀ e0 ∈ [strip e, K.rw e], ∃ y, e0.eval p env = some y := by
  intro e0 hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · exact ⟨x, by rw [strip_eval, he]⟩
  · exact ⟨x, by rw [Known.rw_eval h, he]⟩

/-- After a witness call that read `outs`. -/
theorem Known.witness_post {K : Known} {env env' : Env} {g : Expr} {xg : Fr}
    {outs : List (Var × Option Range)} {act : Bool} {st st' : List Fr}
    (h : K.Holds p env) (hg : g.eval p env = some xg) (hr : readAll act env outs st = some (env', st')) :
    ({ K.after [strip g, K.rw g] (outs.map (·.1)) with
        ranged := witnessChecks outs ++ (K.after [strip g, K.rw g] (outs.map (·.1))).ranged } : Known).Holds
      p env' :=
  Known.ranged_holds (Known.after_holds h (Known.pair_evals h hg) (readAll_unchanged hr))
    (witnessChecks_holds p hr (fun _ _ => rfl))

end Keep

/-! ## Statements -/

section Stmts
variable (p : Prims)

/-- One statement, in the semantics: the rewritten statements run exactly as
    the original, and the facts after it hold of the environment it leaves. -/
theorem Known.stmt_exec (K : Known) (st : Stmt) (s : RunState) (h : K.Holds p s.env) :
    execAll p (K.stmt st).1 s = st.exec p s ∧
      ∀ s', st.exec p s = some s' → (K.stmt st).2.Holds p s'.env := by
  cases st with
  | bind v hint e =>
      simp only [Known.stmt]
      refine ⟨by rw [execAll_single]; simp only [Stmt.exec, Known.rw_eval h], ?_⟩
      intro s' hs
      simp only [Stmt.exec, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        Option.some.injEq] at hs
      obtain ⟨x, hx, rfl⟩ := hs
      refine Known.after_holds h (Known.pair_evals h hx) ?_
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      simp [Env.set, hw]
  | assert c msg =>
      simp only [Known.stmt]
      split
      · next h1 =>
        obtain ⟨k, hk, hk1⟩ := Known.isOne_eq h1
        have hc : c.eval p s.env = some 1 := by
          rw [← Known.rw_eval h, hk]; simp [Expr.eval, hk1]
        refine ⟨?_, ?_⟩
        · simp [execAll, Stmt.exec, hc, asBool_one]
        · intro s' hs
          simp [Stmt.exec, hc, asBool_one] at hs
          subst hs; exact h
      · refine ⟨by rw [execAll_single]; simp only [Stmt.exec, Known.rw_eval h], ?_⟩
        intro s' hs
        simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at hs
        obtain ⟨x, hx, b, hb, hs⟩ := hs
        cases b with
        | false => simp at hs
        | true =>
          simp only [ite_true, Option.pure_def, Option.some.injEq] at hs
          subst hs
          have hx1 := asBool_true hb
          subst hx1
          refine Known.assumeConst_holds _ _ _ (Known.assumeConst_holds _ _ _ h ?_) ?_
          · rw [strip_eval, hx, Fr.ofInt_one]
          · rw [Known.rw_eval h, hx, Fr.ofInt_one]
  | constrain e r =>
      simp only [Known.stmt]
      refine ⟨by rw [execAll_single]; simp only [Stmt.exec, Known.rw_eval h], ?_⟩
      intro s' hs
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at hs
      obtain ⟨x, hx, hs⟩ := hs
      split at hs
      · next hr =>
        simp only [Option.pure_def, Option.some.injEq] at hs
        subst hs
        refine Known.ranged_holds (rs := [(strip e, r), (K.rw e, r)])
          (Known.after_holds h (Known.pair_evals h hx) (fun _ _ => rfl)) ?_
        intro e0 r0 hm
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨x, by rw [strip_eval, hx], hr⟩
        · exact ⟨x, by rw [Known.rw_eval h, hx], hr⟩
      · cases hs
  | witness g name args outs shape =>
      simp only [Known.stmt]
      refine ⟨by rw [execAll_single]; simp only [Stmt.exec, Known.rw_eval h], ?_⟩
      intro s' hs
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at hs
      obtain ⟨xg, hg, hs⟩ := hs
      split at hs
      · next hemp =>
        simp only [Option.pure_def, Option.some.injEq] at hs
        subst hs
        have : outs = [] := List.isEmpty_iff.mp hemp
        subst this
        exact Known.witness_post h hg (act := true) (st := s.priv) rfl
      · simp only [Option.bind_eq_some_iff] at hs
        obtain ⟨act, _, ⟨env1, priv1⟩, hr, hs⟩ := hs
        simp only [Option.pure_def, Option.some.injEq] at hs
        subst hs
        exact Known.witness_post h hg hr
  | ledger g reads ops =>
      simp only [Known.stmt]
      refine ⟨by rw [execAll_single]; simp only [Stmt.exec, Known.rw_eval h], ?_⟩
      intro s' hs
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at hs
      obtain ⟨xg, hg, hs⟩ := hs
      split at hs
      · simp only [Option.pure_def, Option.some.injEq] at hs
        subst hs
        exact Known.after_holds h (Known.pair_evals h hg) (fun _ _ => rfl)
      · simp only [Option.bind_eq_some_iff] at hs
        obtain ⟨act, _, ⟨env1, pub1⟩, hr, groups, _, hs⟩ := hs
        simp only [Option.pure_def, Option.some.injEq] at hs
        subst hs
        refine Known.after_holds h (Known.pair_evals h hg) ?_
        intro w hw
        exact readAll_unchanged hr w (by rw [reads_vars]; exact hw)

/-- A list of statements, in the semantics. -/
theorem Known.stmts_exec : ∀ (stmts : List Stmt) (K : Known) (s : RunState), K.Holds p s.env →
    execAll p (K.stmts stmts).1 s = execAll p stmts s ∧
      ∀ s', execAll p stmts s = some s' → (K.stmts stmts).2.Holds p s'.env
  | [], K, s, h => ⟨rfl, fun s' hs => by cases hs; exact h⟩
  | st :: rest, K, s, h => by
      obtain ⟨h1, h2⟩ := Known.stmt_exec p K st s h
      simp only [Known.stmts]
      rw [execAll_append, h1]
      simp only [execAll, Option.bind_eq_bind]
      cases hs : st.exec p s with
      | none => exact ⟨rfl, fun _ h => by cases h⟩
      | some s1 =>
          simp only [Option.bind_some]
          exact Known.stmts_exec rest _ s1 (h2 s1 hs)

end Stmts

end Damp.IR.Asserts

namespace Damp.IR.Asserts
open Damp.Exec
open Damp.Zkir (Prims)

variable {ω σ : Type}

section Exec
variable (p : Prims) (O : Oracles ω σ)

/-- Assigned values are read from a stream, so the facts after a witness call hold. -/
theorem assign_post {K : Known} {env env' : Env} {g : Expr} {xg : Fr}
    {outs : List (Var × Option Range)} {vals : List Fr}
    (h : K.Holds p env) (hg : g.eval p env = some xg) (ha : assign env outs vals = some env') :
    ({ K.after [strip g, K.rw g] (outs.map (·.1)) with
        ranged := witnessChecks outs ++ (K.after [strip g, K.rw g] (outs.map (·.1))).ranged } : Known).Holds
      p env' :=
  Known.witness_post h hg (assign_readAll' outs env vals env' ha)

/-- One statement, in the executor: the rewritten statements run exactly as the
    original, and the facts after it hold of the environment it leaves. -/
theorem Known.stmt_step (K : Known) (st : Stmt) (s : State ω σ) (h : K.Holds p s.env) :
    steps p O (K.stmt st).1 s = step p O s st ∧
      ∀ s', step p O s st = some s' → (K.stmt st).2.Holds p s'.env := by
  cases st with
  | bind v hint e =>
      simp only [Known.stmt]
      refine ⟨by rw [steps_single]; simp only [step, Known.rw_eval h], ?_⟩
      intro s' hs
      simp only [step, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        Option.some.injEq] at hs
      obtain ⟨x, hx, rfl⟩ := hs
      refine Known.after_holds h (Known.pair_evals h hx) ?_
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      simp [Env.set, hw]
  | assert c msg =>
      simp only [Known.stmt]
      split
      · next h1 =>
        obtain ⟨k, hk, hk1⟩ := Known.isOne_eq h1
        have hc : c.eval p s.env = some 1 := by
          rw [← Known.rw_eval h, hk]; simp [Expr.eval, hk1]
        refine ⟨?_, ?_⟩
        · simp [steps, step, hc, asBool_one]
        · intro s' hs
          simp [step, hc, asBool_one] at hs
          subst hs; exact h
      · refine ⟨by rw [steps_single]; simp only [step, Known.rw_eval h], ?_⟩
        intro s' hs
        simp only [step, Option.bind_eq_bind, Option.bind_eq_some_iff] at hs
        obtain ⟨x, hx, b, hb, hs⟩ := hs
        cases b with
        | false => simp at hs
        | true =>
          simp only [ite_true, Option.pure_def, Option.some.injEq] at hs
          subst hs
          have hx1 := asBool_true hb
          subst hx1
          refine Known.assumeConst_holds _ _ _ (Known.assumeConst_holds _ _ _ h ?_) ?_
          · rw [strip_eval, hx, Fr.ofInt_one]
          · rw [Known.rw_eval h, hx, Fr.ofInt_one]
  | constrain e r =>
      simp only [Known.stmt]
      refine ⟨by rw [steps_single]; simp only [step, Known.rw_eval h], ?_⟩
      intro s' hs
      simp only [step, Option.bind_eq_bind, Option.bind_eq_some_iff] at hs
      obtain ⟨x, hx, hs⟩ := hs
      split at hs
      · next hr =>
        simp only [Option.pure_def, Option.some.injEq] at hs
        subst hs
        refine Known.ranged_holds (rs := [(strip e, r), (K.rw e, r)])
          (Known.after_holds h (Known.pair_evals h hx) (fun _ _ => rfl)) ?_
        intro e0 r0 hm
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨x, by rw [strip_eval, hx], hr⟩
        · exact ⟨x, by rw [Known.rw_eval h, hx], hr⟩
      · cases hs
  | witness g name args outs shape =>
      simp only [Known.stmt]
      refine ⟨by rw [steps_single]; simp only [step, Known.rw_eval h, Known.rw_evalList h], ?_⟩
      intro s' hs
      simp only [step, Option.bind_eq_bind, Option.bind_eq_some_iff] at hs
      obtain ⟨xg, hg, hs⟩ := hs
      split at hs
      · next hemp =>
        have : outs = [] := List.isEmpty_iff.mp hemp
        subst this
        have henv : s'.env = s.env := by
          split at hs
          · simp only [Option.bind_eq_some_iff] at hs
            obtain ⟨_, _, ⟨vals, w⟩, _, hs⟩ := hs
            split at hs
            · simp only [Option.pure_def, Option.some.injEq] at hs; subst hs; rfl
            · cases hs
          · simp only [Option.pure_def, Option.some.injEq] at hs; subst hs; rfl
        rw [henv]
        exact Known.witness_post h hg (act := true) (st := []) rfl
      · simp only [Option.bind_eq_some_iff] at hs
        obtain ⟨act, _, hs⟩ := hs
        split at hs
        · simp only [Option.bind_eq_some_iff] at hs
          obtain ⟨_, _, ⟨vals, w⟩, _, env1, ha, hs⟩ := hs
          simp only [Option.pure_def, Option.some.injEq] at hs
          subst hs
          exact assign_post p h hg ha
        · simp only [Option.bind_eq_some_iff] at hs
          obtain ⟨env1, ha, hs⟩ := hs
          simp only [Option.pure_def, Option.some.injEq] at hs
          subst hs
          exact assign_post p h hg ha
  | ledger g reads ops =>
      simp only [Known.stmt]
      refine ⟨by rw [steps_single]; simp only [step, Known.rw_eval h], ?_⟩
      intro s' hs
      simp only [step, Option.bind_eq_bind, Option.bind_eq_some_iff] at hs
      obtain ⟨xg, hg, hs⟩ := hs
      have post : ∀ env1 vals, assign s.env (reads.map fun v => (v, none)) vals = some env1 →
          (K.after [strip g, K.rw g] reads).Holds p env1 := by
        intro env1 vals ha
        refine Known.after_holds h (Known.pair_evals h hg) ?_
        intro w hw
        exact readAll_unchanged (assign_readAll' _ _ _ _ ha) w (by rw [reads_vars]; exact hw)
      split at hs
      · simp only [Option.pure_def, Option.some.injEq] at hs
        subst hs
        exact Known.after_holds h (Known.pair_evals h hg) (fun _ _ => rfl)
      · simp only [Option.bind_eq_some_iff] at hs
        obtain ⟨act, _, hs⟩ := hs
        split at hs
        · simp only [Option.bind_eq_some_iff] at hs
          obtain ⟨_, _, ⟨vals, l⟩, _, env1, ha, _, _, hs⟩ := hs
          simp only [Option.pure_def, Option.some.injEq] at hs
          subst hs
          exact post env1 vals ha
        · simp only [Option.bind_eq_some_iff] at hs
          obtain ⟨env1, ha, _, _, hs⟩ := hs
          simp only [Option.pure_def, Option.some.injEq] at hs
          subst hs
          exact post env1 _ ha

/-- A list of statements, in the executor. -/
theorem Known.stmts_step : ∀ (stmts : List Stmt) (K : Known) (s : State ω σ), K.Holds p s.env →
    steps p O (K.stmts stmts).1 s = steps p O stmts s ∧
      ∀ s', steps p O stmts s = some s' → (K.stmts stmts).2.Holds p s'.env
  | [], K, s, h => ⟨rfl, fun s' hs => by cases hs; exact h⟩
  | st :: rest, K, s, h => by
      obtain ⟨h1, h2⟩ := Known.stmt_step p O K st s h
      simp only [Known.stmts]
      rw [steps_append, h1]
      simp only [steps, Option.bind_eq_bind]
      cases hs : step p O s st with
      | none => exact ⟨rfl, fun _ h => by cases h⟩
      | some s1 =>
          simp only [Option.bind_some]
          exact Known.stmts_step rest _ s1 (h2 s1 hs)

end Exec

end Damp.IR.Asserts

/-! ## Circuits -/

namespace Damp.IR
open Damp.Zkir (Prims)
open Damp.IR.Asserts

/-- A run of the rewritten circuit is exactly a run of the original. -/
theorem Circuit.asserts_run (p : Prims) (c : Circuit) (inputs priv pub : List Fr) :
    (Circuit.asserts c).run p inputs priv pub = c.run p inputs priv pub := by
  simp only [Circuit.asserts, Circuit.run, Option.bind_eq_bind]
  cases bindInputs (fun _ => 0) c.inputs inputs with
  | none => rfl
  | some env =>
    simp only [Option.bind_some]
    obtain ⟨h1, h2⟩ := Known.stmts_exec p c.body.toList {} { env, priv, pub } (Known.holds_empty p _)
    rw [h1]
    cases hs : execAll p c.body.toList { env, priv, pub } with
    | none => rfl
    | some s => simp only [Option.bind_some, Known.rw_evalList (h2 s hs)]

end Damp.IR

namespace Damp.Exec
open Damp.IR Damp.IR.Asserts
open Damp.Zkir (Prims)

/-- The executor runs the rewritten circuit exactly as the original. -/
theorem asserts_run {ω σ : Type} (p : Prims) (O : Oracles ω σ) (c : Circuit) (inputs : List Fr)
    (private_ : ω) (ledger : σ) :
    run p O (Circuit.asserts c) inputs private_ ledger = run p O c inputs private_ ledger := by
  simp only [Circuit.asserts, run, Option.bind_eq_bind]
  cases bindInputs (fun _ => 0) c.inputs inputs with
  | none => rfl
  | some env =>
    simp only [Option.bind_some]
    obtain ⟨h1, h2⟩ := Known.stmts_step p O c.body.toList {} { env, private_, ledger }
      (Known.holds_empty p _)
    rw [h1]
    cases hs : steps p O c.body.toList { env, private_, ledger } with
    | none => rfl
    | some s => simp only [Option.bind_some, Known.rw_evalList (h2 s hs)]

end Damp.Exec

namespace Damp.IR
open Damp.IR.Asserts

/-- `Circuit.asserts` is a sound pass. -/
theorem Circuit.asserts_sound : Pass.Sound Circuit.asserts :=
  ⟨fun p c i pr pu => by rw [Circuit.asserts_run],
   fun p O c i w l => by rw [Exec.asserts_run]⟩

/-! ## Ledger statements are untouched -/

namespace Asserts

theorem checkLedgerFrom_iff (name : String) : ∀ (i : Nat) (l : List Stmt),
    checkLedgerFrom name i l = .ok () ↔ ∀ s ∈ l, s.ledgerProblem = none
  | _, [] => by simp [checkLedgerFrom]
  | i, s :: l => by
      simp only [checkLedgerFrom, List.mem_cons, forall_eq_or_imp]
      cases s.ledgerProblem with
      | some why => simp
      | none => simp only [true_and]; exact checkLedgerFrom_iff name (i + 1) l

theorem Known.stmt_ledgerProblem (K : Known) (st : Stmt) :
    ∀ s ∈ (K.stmt st).1, s.ledgerProblem = st.ledgerProblem ∨ s.ledgerProblem = none := by
  intro s hs
  cases st with
  | assert c msg =>
      simp only [Known.stmt] at hs
      split at hs
      · cases hs
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs; subst hs
        right; rfl
  | _ =>
      simp only [Known.stmt, List.mem_cons, List.not_mem_nil, or_false] at hs
      subst hs; first | (left; rfl) | (right; rfl)

theorem Known.stmts_ledgerProblem : ∀ (l : List Stmt) (K : Known), (∀ s ∈ l, s.ledgerProblem = none) →
    ∀ s ∈ (K.stmts l).1, s.ledgerProblem = none
  | [], _, _ => by simp [Known.stmts]
  | st :: l, K, h => by
      intro s hs
      simp only [Known.stmts, List.mem_append] at hs
      rcases hs with hs | hs
      · rcases Known.stmt_ledgerProblem K st s hs with e | e
        · rw [e]; exact h st (by simp)
        · exact e
      · exact Known.stmts_ledgerProblem l _ (fun s hs => h s (by simp [hs])) s hs

end Asserts

/-- The pass keeps a circuit's ledger statements well formed: it changes only
    their guards. -/
theorem Circuit.asserts_checkLedger (c : Circuit) (h : c.checkLedger = .ok ()) :
    (Circuit.asserts c).checkLedger = .ok () := by
  simp only [Circuit.checkLedger, Circuit.asserts, List.toList_toArray] at h ⊢
  rw [Asserts.checkLedgerFrom_iff] at h ⊢
  exact Known.stmts_ledgerProblem _ _ h

end Damp.IR
