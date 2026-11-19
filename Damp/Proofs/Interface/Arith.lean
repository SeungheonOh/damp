/-
`Uint` arithmetic and conversions, under the invariant `Uint.Means`.

* `+` and `*` mean the sum and product of the numbers, with the widened bound
  and no wrap-around in the field. The cap: the result type `Uint (m + k)`
  (resp. `Uint (m * k)`) goes through `Uint.capped`; if the new bound exceeds
  `Uint.maxBound = 2 ^ 248 - 1` the result is an `invalid` expression, which
  has no value (`Uint.add_past_cap`) and which the emitter rejects. At the cap
  itself (`m + k = 2 ^ 248 - 1`) the result is fine (`Uint.add_means`), and the
  largest number it can hold, `2 ^ 248 - 1`, is far below the field modulus, so
  the field element read back is the sum (`Uint.Means.val`).
* `castTo` and `Field.toUint` succeed exactly when the value fits (or the guard
  is off), as `Runs` statements.
* `widen`, literals, `toField`, `select` keep the meaning.
-/
import Damp.Proofs.Interface.Logic

namespace Damp
open IR

variable {p : Zkir.Prims} {env : Env}

/-! ## Making `Uint`s -/

theorem Uint.lit_means {n : Nat} (hn : n ≤ Uint.maxBound) : Uint.Means p env (Uint.lit n) n :=
  ⟨hn, Uint.lit_is hn⟩

theorem Uint.ofNat_means {m n : Nat} (h : n ≤ m) (hm : m ≤ Uint.maxBound) :
    Uint.Means p env (Uint.ofNat n h : Uint m) n := ⟨hm, Uint.ofNat_is h hm⟩

theorem Uint.numeral_means {m n : Nat} (h : n ≤ m) (hm : m ≤ Uint.maxBound) :
    Uint.Means p env (OfNat.ofNat n : Uint m) n := ⟨hm, Uint.numeral_is h hm⟩

theorem Uint.widen_means {m k n : Nat} {a : Uint m} (h : m ≤ k) (hk : k ≤ Uint.maxBound)
    (ha : Uint.Means p env a n) : Uint.Means p env (a.widen h) n := ⟨hk, Uint.widen_is h hk ha.2⟩

theorem Uint.toField_means {m n : Nat} {a : Uint m} (ha : Uint.Means p env a n) :
    Field.Is p env a.toField (Fr.ofNat n) := ha.2.2

/-! ## `+` and `*` -/

/-- `a + b` means `x + y`, within the bound `m + k`, as long as that bound is within the cap. -/
theorem Uint.add_means {m k x y : Nat} {a : Uint m} {b : Uint k} (hcap : m + k ≤ Uint.maxBound)
    (ha : Uint.Means p env a x) (hb : Uint.Means p env b y) : Uint.Means p env (a + b) (x + y) :=
  ⟨hcap, Uint.add_is hcap ha.2 hb.2⟩

/-- `a * b` means `x * y`, within the bound `m * k`, as long as that bound is within the cap. -/
theorem Uint.mul_means {m k x y : Nat} {a : Uint m} {b : Uint k} (hcap : m * k ≤ Uint.maxBound)
    (ha : Uint.Means p env a x) (hb : Uint.Means p env b y) : Uint.Means p env (a * b) (x * y) :=
  ⟨hcap, Uint.mul_is hcap ha.2 hb.2⟩

/-- No wrap-around: the field element of `a + b` reads back as the natural sum. -/
theorem Uint.add_no_wrap {m k x y : Nat} {a : Uint m} {b : Uint k} (hcap : m + k ≤ Uint.maxBound)
    (ha : Uint.Means p env a x) (hb : Uint.Means p env b y) :
    (a + b).expr.eval p env = some (Fr.ofNat (x + y)) ∧ (Fr.ofNat (x + y)).val = x + y :=
  ⟨(Uint.add_means hcap ha hb).eval, (Uint.add_means hcap ha hb).val⟩

/-- No wrap-around: the field element of `a * b` reads back as the natural product. -/
theorem Uint.mul_no_wrap {m k x y : Nat} {a : Uint m} {b : Uint k} (hcap : m * k ≤ Uint.maxBound)
    (ha : Uint.Means p env a x) (hb : Uint.Means p env b y) :
    (a * b).expr.eval p env = some (Fr.ofNat (x * y)) ∧ (Fr.ofNat (x * y)).val = x * y :=
  ⟨(Uint.mul_means hcap ha hb).eval, (Uint.mul_means hcap ha hb).val⟩

/-- Past the cap `a + b` has no value, whatever the operands hold: the cap is on the type. -/
theorem Uint.add_past_cap {m k : Nat} (a : Uint m) (b : Uint k) (h : Uint.maxBound < m + k) :
    (a + b).expr.eval p env = none := Uint.add_too_large a b (by omega)

/-- Past the cap `a * b` has no value. -/
theorem Uint.mul_past_cap {m k : Nat} (a : Uint m) (b : Uint k) (h : Uint.maxBound < m * k) :
    (a * b).expr.eval p env = none := Uint.mul_too_large a b (by omega)

/-- Exactly at the cap: `Uint (2^248 - 1)` values add to the largest legal bound only with 0. -/
example : (Uint.lit Uint.maxBound + Uint.lit 0).expr = .add (Uint.lit Uint.maxBound).expr (Uint.lit 0).expr := by
  rw [Uint.add_expr, Uint.capped_of_le (by decide)]

/-! ## `select` on `Uint` -/

theorem select_uint_means {m x y : Nat} {c : Boolean} {a b : Uint m} {u : Bool}
    (hc : Boolean.Is p env c u) (ha : Uint.Means p env a x) (hb : Uint.Means p env b y) :
    Uint.Means p env (select c a b) (if u then x else y) := ⟨ha.1, select_uint_is ha.1 hc ha.2 hb.2⟩

/-! ## Checked operations, as builder computations -/

section Checked
variable {s : Build} {st : RunState} {gb : Bool}

/-- The guard of the builder state means `gb`, stably. -/
abbrev GuardIs (p : Zkir.Prims) (s : Build) (st : RunState) (gb : Bool) : Prop :=
  Stable s.next st.env (fun e => Boolean.Is p e ⟨s.guard⟩ gb)

/-- A run state with this environment. -/
abbrev withEnv (e : Env) : RunState := { env := e, priv := [], pub := [] }

/-- A computation that appends one check and returns a value, described by its exec lemma. -/
theorem Runs.ofCheck {α : Type} {m : CircuitM α} {chk : Stmt} {r : α} {ok : Bool} {Q : α → Env → Prop}
    (hrun : m.run s = (r, { s with stmts := s.stmts.push chk }))
    (hexec : execAll p [chk] st = if ok then some st else none)
    (hQ : ok = true → Stable s.next st.env (Q r)) :
    Runs p m s st (ok = true) Q := by
  refine ⟨by rw [hrun]; exact Nat.le_refl _, by rw [hrun], [chk], by rw [hrun]; exact Array.toList_push, ?_, ?_⟩
  · rw [hexec]; cases ok <;> simp
  · intro st' h'
    rw [hexec] at h'
    cases ok
    · cases h'
    · simp only [↓reduceIte, Option.some.injEq] at h'
      subst h'
      exact ⟨Agree.refl _ _, rfl, rfl, rfl, by rw [hrun]; exact hQ rfl⟩

/-- `a.sub b` succeeds exactly when the guard is off or `y ≤ x`; then it means `x - y` where
    the guard holds and 0 where it does not. -/
theorem Runs.sub {m k x y : Nat} {a : Uint m} {b : Uint k}
    (hg : GuardIs p s st gb) (ha : Stable s.next st.env (fun e => Uint.Means p e a x))
    (hb : Stable s.next st.env (fun e => Uint.Means p e b y)) :
    Runs p (a.sub b) s st (gb = true → y ≤ x) (fun r e => Uint.Means p e r (if gb then x - y else 0)) := by
  have h := Uint.sub_correct (st := st) ha.holds.lt254 hb.holds.lt254 ha.holds.2 hb.holds.2 hg.holds
  refine (Runs.ofCheck (Uint.sub_run a b s) h.1 fun hok e he => ?_).conseq
    (by cases gb <;> simp) (fun _ _ h => h)
  have h' := Uint.sub_correct (st := withEnv e) (ha e he).lt254 (hb e he).lt254 (ha e he).2 (hb e he).2 (hg e he)
  exact ⟨(ha e he).1, h'.2 hok⟩

/-- `Uint.sub` at the top level of a circuit: succeeds exactly when `y ≤ x`, and means `x - y`. -/
theorem Runs.sub_top {m k x y : Nat} {a : Uint m} {b : Uint k} (hs : s.guard = .const 1)
    (ha : Stable s.next st.env (fun e => Uint.Means p e a x))
    (hb : Stable s.next st.env (fun e => Uint.Means p e b y)) :
    Runs p (a.sub b) s st (y ≤ x) (fun r e => Uint.Means p e r (x - y)) :=
  (Runs.sub (gb := true) (fun e _ => by rw [hs]; exact guard_one_is) ha hb).conseq (by simp)
    (fun _ _ h => by simpa using h)

/-- Widening `castTo` builds nothing and keeps the number. -/
theorem Runs.castTo_le {m k x : Nat} {a : Uint m} (h : m ≤ k) (hk : k ≤ Uint.maxBound)
    (ha : Stable s.next st.env (fun e => Uint.Means p e a x)) :
    Runs p (a.castTo k) s st True (fun r e => Uint.Means p e r x) := by
  have hrun := Uint.castTo_run_le a h hk s
  refine ⟨by rw [hrun]; exact Nat.le_refl _, by rw [hrun], [], by rw [hrun]; simp, by simp [execAll], fun st' h' => ?_⟩
  simp only [execAll, Option.some.injEq] at h'; subst h'
  refine ⟨Agree.refl _ _, rfl, rfl, rfl, ?_⟩
  rw [hrun]; exact fun e he => ⟨hk, Uint.castTo_le_correct h (ha e he).2⟩

/-- Narrowing `castTo` succeeds exactly when the guard is off or `x ≤ k`; then it means `x`
    where the guard holds and 0 where it does not. -/
theorem Runs.castTo_gt {m k x : Nat} {a : Uint m} (h : ¬ m ≤ k) (hk : k ≤ Uint.maxBound)
    (hg : GuardIs p s st gb) (ha : Stable s.next st.env (fun e => Uint.Means p e a x)) :
    Runs p (a.castTo k) s st (gb = true → x ≤ k) (fun r e => Uint.Means p e r (if gb then x else 0)) := by
  have h1 := Uint.castTo_correct (st := st) ha.holds.ltMod (Uint.lt_of_le_maxBound hk) ha.holds.2 hg.holds
  refine (Runs.ofCheck (Uint.castTo_run_gt a h hk s) h1.1 fun hok e he => ?_).conseq
    (by cases gb <;> simp) (fun _ _ h => h)
  have h' := Uint.castTo_correct (st := withEnv e) (ha e he).ltMod (Uint.lt_of_le_maxBound hk) (ha e he).2 (hg e he)
  exact ⟨hk, h'.2 hok⟩

/-- `castTo` in general: succeeds exactly when the guard is off or the number fits. -/
theorem Runs.castTo {m k x : Nat} {a : Uint m} (hk : k ≤ Uint.maxBound)
    (hg : GuardIs p s st gb) (ha : Stable s.next st.env (fun e => Uint.Means p e a x)) :
    Runs p (a.castTo k) s st (gb = true → x ≤ k)
      (fun r e => Uint.Means p e r (if gb || decide (m ≤ k) then x else 0)) := by
  by_cases h : m ≤ k
  · have hx : x ≤ k := Nat.le_trans ha.holds.le h
    exact (Runs.castTo_le h hk ha).conseq (by simp [hx]) (fun _ _ hm => by simpa [h] using hm)
  · exact (Runs.castTo_gt h hk hg ha).conseq Iff.rfl (fun _ _ hm => by simpa [h] using hm)

/-- `Field.toUint` succeeds exactly when the guard is off or the value is at most `k`; then it
    means the value where the guard holds and 0 where it does not. -/
theorem Runs.toUint {k : Nat} {a : Field} {v : Fr} (hk : k ≤ Uint.maxBound)
    (hg : GuardIs p s st gb) (ha : Stable s.next st.env (fun e => Field.Is p e a v)) :
    Runs p (a.toUint k) s st (gb = true → v.val ≤ k) (fun r e => Uint.Means p e r (if gb then v.val else 0)) := by
  have h1 := Field.toUint_correct (st := st) (Uint.lt_of_le_maxBound hk) ha.holds hg.holds
  refine (Runs.ofCheck (Field.toUint_run a hk s) h1.1 fun hok e he => ?_).conseq
    (by cases gb <;> simp) (fun _ _ h => h)
  exact ⟨hk, (Field.toUint_correct (st := withEnv e) (Uint.lt_of_le_maxBound hk) (ha e he) (hg e he)).2 hok⟩

end Checked

end Damp
