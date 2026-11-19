/-
Comparisons and Boolean connectives on values that satisfy their types' invariants.

`Uint.Means a n` is the invariant of a `Uint m` made by the interface: its bound
is within Compact's limit (`m ≤ 2 ^ 248 - 1`; every way of making a `Uint`,
`Field.unsafeToUint` included, goes through `Uint.capped`, which has no value past it, see
`Uint.capped_eval_of_gt`) and it means the number `n ≤ m`. Under these
invariants every comparison form evaluates, to the comparison of the numbers:
the only partiality of `<`, an operand not fitting the stated width, cannot
arise, because the interface compares at `max (bitLen m) (bitLen k) ≤ 248`
bits (`Uint.lt_width_le`) and a number at most `m` fits `bitLen m` bits
(`Uint.Means.fits`). A `Nat` literal on one side must itself be within the
limit: past it, `Uint.lit n` is an `invalid` expression and the comparison has
no value (`cmpLt_uint_nat_past_cap`); the emitter rejects such a circuit.
-/
import Damp.Proofs.Interface.Args

namespace Damp
open IR

/-- `a` satisfies the invariant of its type: the bound is within Compact's limit and `a`
    means the number `n` (so `n ≤ m`). -/
def Uint.Means (p : Zkir.Prims) (env : Env) {m : Nat} (a : Uint m) (n : Nat) : Prop :=
  m ≤ Uint.maxBound ∧ Uint.Is p env a n

variable {p : Zkir.Prims} {env : Env}

theorem Uint.Means.is {m n : Nat} {a : Uint m} (h : Uint.Means p env a n) : Uint.Is p env a n := h.2
theorem Uint.Means.le {m n : Nat} {a : Uint m} (h : Uint.Means p env a n) : n ≤ m := h.2.1
theorem Uint.Means.bound {m n : Nat} {a : Uint m} (h : Uint.Means p env a n) : m ≤ Uint.maxBound := h.1
theorem Uint.Means.lt254 {m n : Nat} {a : Uint m} (h : Uint.Means p env a n) : m < 2 ^ 254 :=
  Uint.lt_of_le_maxBound h.1
theorem Uint.Means.ltMod {m n : Nat} {a : Uint m} (h : Uint.Means p env a n) : m < Fr.modulus :=
  Uint.lt_modulus_of_le_maxBound h.1

/-- The number is read back from the field element unchanged. -/
theorem Uint.Means.val {m n : Nat} {a : Uint m} (h : Uint.Means p env a n) : (Fr.ofNat n).val = n :=
  h.2.val_eq h.ltMod

/-- A `Uint` means at most one number. -/
theorem Uint.Means.unique {m x y : Nat} {a : Uint m} (hx : Uint.Means p env a x) (hy : Uint.Means p env a y) :
    x = y := Uint.Is.unique hx.ltMod hx.2 hy.2

/-- A `Uint` has a value: it cannot fail. -/
theorem Uint.Means.eval {m n : Nat} {a : Uint m} (h : Uint.Means p env a n) :
    a.expr.eval p env = some (Fr.ofNat n) := h.2.2

/-- A `Boolean` that means a truth value has a value: it cannot fail. -/
theorem Boolean.Is.ne_none {b : Boolean} {u : Bool} (h : Boolean.Is p env b u) : b.expr.eval p env ≠ none := by
  rw [h]; exact Option.some_ne_none _

/-! ## The comparison width -/

/-- A bound within Compact's limit has bit length at most 248. -/
theorem bitLen_le_248 {m : Nat} (h : m ≤ Uint.maxBound) : bitLen m ≤ 248 :=
  bitLen_le_of_lt (by unfold Uint.maxBound at h; have : 0 < 2 ^ 248 := Nat.two_pow_pos _; omega)

/-- The width `Uint.lt` uses is at most 248 bits, below ZKIR's limit of 255. -/
theorem Uint.lt_width_le {m k : Nat} (hm : m ≤ Uint.maxBound) (hk : k ≤ Uint.maxBound) :
    max (bitLen m) (bitLen k) ≤ 248 := Nat.max_le.2 ⟨bitLen_le_248 hm, bitLen_le_248 hk⟩

/-- An operand that satisfies its invariant fits the width `Uint.lt` compares at. -/
theorem Uint.Means.fits {m k n : Nat} {a : Uint m} (h : Uint.Means p env a n) (hk : k ≤ Uint.maxBound) :
    Zkir.fitsBits (Fr.ofNat n) (max (bitLen m) (bitLen k)) = true :=
  fitsBits_of_le h.le h.lt254 (Nat.le_max_left _ _) (by have := Uint.lt_width_le h.bound hk; omega)

/-- The same for the right operand. -/
theorem Uint.Means.fits_right {m k n : Nat} {a : Uint k} (h : Uint.Means p env a n) (hm : m ≤ Uint.maxBound) :
    Zkir.fitsBits (Fr.ofNat n) (max (bitLen m) (bitLen k)) = true :=
  fitsBits_of_le h.le h.lt254 (Nat.le_max_right _ _) (by have := Uint.lt_width_le hm h.bound; omega)

/-! ## Comparison forms on `Uint`, total under the invariants -/

section Cmp
variable {m k x y n : Nat} {a : Uint m} {b : Uint k}

theorem Uint.lt_means (ha : Uint.Means p env a x) (hb : Uint.Means p env b y) :
    Boolean.Is p env (a.lt b) (decide (x < y)) := Uint.lt_is ha.lt254 hb.lt254 ha.2 hb.2

theorem Uint.eq_means (ha : Uint.Means p env a x) (hb : Uint.Means p env b y) :
    Boolean.Is p env (a.eq b) (decide (x = y)) := Uint.eq_is ha.ltMod hb.ltMod ha.2 hb.2

/-- `a <. b`. -/
theorem cmpLt_means (ha : Uint.Means p env a x) (hb : Uint.Means p env b y) :
    Boolean.Is p env (cmpLt a b) (decide (x < y)) := cmpLt_uint ha.lt254 hb.lt254 ha.2 hb.2
/-- `a >. b`. -/
theorem cmpGt_means (ha : Uint.Means p env a x) (hb : Uint.Means p env b y) :
    Boolean.Is p env (cmpGt a b) (decide (y < x)) := cmpGt_uint ha.lt254 hb.lt254 ha.2 hb.2
/-- `a <=. b`. -/
theorem cmpLe_means (ha : Uint.Means p env a x) (hb : Uint.Means p env b y) :
    Boolean.Is p env (cmpLe a b) (decide (x ≤ y)) := cmpLe_uint ha.lt254 hb.lt254 ha.2 hb.2
/-- `a >=. b`. -/
theorem cmpGe_means (ha : Uint.Means p env a x) (hb : Uint.Means p env b y) :
    Boolean.Is p env (cmpGe a b) (decide (y ≤ x)) := cmpGe_uint ha.lt254 hb.lt254 ha.2 hb.2
/-- `a ==. b`. -/
theorem cmpEq_means (ha : Uint.Means p env a x) (hb : Uint.Means p env b y) :
    Boolean.Is p env (cmpEq a b) (decide (x = y)) := cmpEq_uint ha.ltMod hb.ltMod ha.2 hb.2
/-- `a !=. b`. -/
theorem cmpNe_means (ha : Uint.Means p env a x) (hb : Uint.Means p env b y) :
    Boolean.Is p env (cmpNe a b) (decide (x ≠ y)) := cmpNe_uint ha.ltMod hb.ltMod ha.2 hb.2

/-- `a <. n` with a literal within the limit. -/
theorem cmpLt_means_nat (ha : Uint.Means p env a x) (hn : n ≤ Uint.maxBound) :
    Boolean.Is p env (cmpLt a n) (decide (x < n)) := cmpLt_uint_nat ha.lt254 hn ha.2
theorem cmpGt_means_nat (ha : Uint.Means p env a x) (hn : n ≤ Uint.maxBound) :
    Boolean.Is p env (cmpGt a n) (decide (n < x)) := cmpGt_uint_nat ha.lt254 hn ha.2
theorem cmpLe_means_nat (ha : Uint.Means p env a x) (hn : n ≤ Uint.maxBound) :
    Boolean.Is p env (cmpLe a n) (decide (x ≤ n)) := cmpLe_uint_nat ha.lt254 hn ha.2
theorem cmpGe_means_nat (ha : Uint.Means p env a x) (hn : n ≤ Uint.maxBound) :
    Boolean.Is p env (cmpGe a n) (decide (n ≤ x)) := cmpGe_uint_nat ha.lt254 hn ha.2
theorem cmpEq_means_nat (ha : Uint.Means p env a x) (hn : n ≤ Uint.maxBound) :
    Boolean.Is p env (cmpEq a n) (decide (x = n)) := cmpEq_uint_nat ha.ltMod hn ha.2
theorem cmpNe_means_nat (ha : Uint.Means p env a x) (hn : n ≤ Uint.maxBound) :
    Boolean.Is p env (cmpNe a n) (decide (x ≠ n)) := cmpNe_uint_nat ha.ltMod hn ha.2

/-- `n <. a` with a literal within the limit. -/
theorem cmpLt_nat_means (ha : Uint.Means p env a x) (hn : n ≤ Uint.maxBound) :
    Boolean.Is p env (cmpLt n a) (decide (n < x)) := cmpLt_nat_uint ha.lt254 hn ha.2
theorem cmpGt_nat_means (ha : Uint.Means p env a x) (hn : n ≤ Uint.maxBound) :
    Boolean.Is p env (cmpGt n a) (decide (x < n)) := cmpGt_nat_uint ha.lt254 hn ha.2
theorem cmpLe_nat_means (ha : Uint.Means p env a x) (hn : n ≤ Uint.maxBound) :
    Boolean.Is p env (cmpLe n a) (decide (n ≤ x)) := cmpLe_nat_uint ha.lt254 hn ha.2
theorem cmpGe_nat_means (ha : Uint.Means p env a x) (hn : n ≤ Uint.maxBound) :
    Boolean.Is p env (cmpGe n a) (decide (x ≤ n)) := cmpGe_nat_uint ha.lt254 hn ha.2
theorem cmpEq_nat_means (ha : Uint.Means p env a x) (hn : n ≤ Uint.maxBound) :
    Boolean.Is p env (cmpEq n a) (decide (n = x)) := cmpEq_nat_uint ha.ltMod hn ha.2
theorem cmpNe_nat_means (ha : Uint.Means p env a x) (hn : n ≤ Uint.maxBound) :
    Boolean.Is p env (cmpNe n a) (decide (n ≠ x)) := cmpNe_nat_uint ha.ltMod hn ha.2

/-- A literal past Compact's limit has no value, so neither has a comparison with it (the
    emitter rejects the `invalid` literal). -/
theorem cmpLt_uint_nat_past_cap (a : Uint m) (hn : ¬ n ≤ Uint.maxBound) :
    (cmpLt a n).expr.eval p env = none := by
  show (Expr.lt _ a.expr (Uint.lit n).expr).eval p env = none
  simp only [Expr.eval, Uint.lit_too_large hn]
  cases a.expr.eval p env <;> rfl

end Cmp

/-! ## `Boolean` and `Field` comparisons and connectives

Every `Boolean` operation evaluates, given operands that mean truth values: `!.`, `&&.`,
`||.` are `Boolean.not_is`, `Boolean.and_is`, `Boolean.or_is`. -/

section Bool
variable {a b : Boolean} {u v : Bool}

/-- `a ==. b` on `Boolean`. -/
theorem cmpEq_boolean (ha : Boolean.Is p env a u) (hb : Boolean.Is p env b v) :
    Boolean.Is p env (cmpEq a b) (u == v) := Boolean.eq_is ha hb
/-- `a !=. b` on `Boolean`. -/
theorem cmpNe_boolean (ha : Boolean.Is p env a u) (hb : Boolean.Is p env b v) :
    Boolean.Is p env (cmpNe a b) (u != v) := Boolean.not_is (Boolean.eq_is ha hb)

/-- `a ==. b` on `Field`. -/
theorem cmpEq_field {a b : Field} {x y : Fr} (ha : Field.Is p env a x) (hb : Field.Is p env b y) :
    Boolean.Is p env (cmpEq a b) (decide (x = y)) := Field.eq_is ha hb
/-- `a !=. b` on `Field`. -/
theorem cmpNe_field {a b : Field} {x y : Fr} (ha : Field.Is p env a x) (hb : Field.Is p env b y) :
    Boolean.Is p env (cmpNe a b) (decide (x ≠ y)) := Boolean.not_is (Field.eq_is ha hb)

/-- `a &&. b` is `false` when `a` is, whatever `b` (as long as `b` has a truth value). -/
theorem Boolean.and_false_left (ha : Boolean.Is p env a Bool.false) (hb : Boolean.Is p env b v) :
    Boolean.Is p env (a.and b) Bool.false := Boolean.and_is ha hb

/-- `a ||. b` is `true` when `a` is. -/
theorem Boolean.or_true_left (ha : Boolean.Is p env a Bool.true) (hb : Boolean.Is p env b v) :
    Boolean.Is p env (a.or b) Bool.true := Boolean.or_is ha hb

/-- A `Boolean` that does not mean a truth value makes `!.` fail: the partiality the invariant
    excludes. -/
theorem Boolean.not_fails {a : Boolean} {x : Fr} (ha : a.expr.eval p env = some x) (hx : x ≠ 0) (hx1 : x ≠ 1) :
    a.not.expr.eval p env = none := by
  simp [Boolean.not, Expr.eval, ha, asBool, hx, hx1]

end Bool

end Damp
