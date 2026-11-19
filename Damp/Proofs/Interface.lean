/-
What the typed interface of `Damp/Lang/Contract.lean` promises, proved against the
reference semantics of the IR (`Damp/IR/Semantics.lean`).

A typed value is a wrapper around an IR expression. Its *meaning* in an
environment is the value that expression evaluates to there; the predicates
`Field.Is`, `Boolean.Is` and `Uint.Is` say a value means a given field element,
truth value or number. Each pure operation is shown to compute what its name
says and to preserve these predicates; each statement-building operation is
shown to emit statements that succeed exactly when its check passes, after
which its result has the promised meaning.

Hypotheses on the bounds are the exact ones each promise needs:

* `m < Fr.modulus`: a number at most `m` is a field element unchanged, so the
  number a `Uint m` means is determined (`Uint.Is.unique`) and `==` on it is
  equality of numbers;
* `m < 2 ^ 254`: the bit length of `m` is at most 254, a width ZKIR accepts in
  comparisons and range checks (`fitsBits` requires a width below 255);
* `m + k ≤ Uint.maxBound`, `m * k ≤ Uint.maxBound`: otherwise `+`/`*` build an
  `invalid` expression, which the emitter rejects.

Every one of these holds for bounds at most `Uint.maxBound = 2 ^ 248 - 1`,
Compact's own limit, and no other bound survives: every way of making a `Uint`
except `Field.unsafeToUint` passes through `Uint.capped`, so past the limit it
has no value (`*_too_large`), and the statement builders also record an error
(`*_error`), so such a circuit is never emitted. The literal, `ofNat`, numeral,
`widen` and `select` lemmas therefore assume the bound is within the limit.
Where a promise fails without its hypothesis, `Examples/Interface.lean` has the
counterexample.
-/
import Damp.Lang.Contract
import Damp.IR.Semantics
import Damp.Proofs.Field

namespace Damp
open IR

variable (p : Zkir.Prims) (env : Env)

/-! ## Meaning predicates -/

/-- `x` evaluates to the field element `v`. -/
def Field.Is (x : Field) (v : Fr) : Prop := x.expr.eval p env = some v

/-- `b` evaluates to the field element of the truth value `v` (0 or 1). -/
def Boolean.Is (b : Boolean) (v : Bool) : Prop := b.expr.eval p env = some (Fr.ofBool v)

/-- `a` evaluates to the field image of the number `n`, and `n` is within the bound of its type. -/
def Uint.Is {m : Nat} (a : Uint m) (n : Nat) : Prop := n ≤ m ∧ a.expr.eval p env = some (Fr.ofNat n)

variable {p env}

/-! ## Bit lengths -/

/-- Every number is below 2 to the power of its bit length. -/
theorem lt_two_pow_bitLen (n : Nat) : n < 2 ^ bitLen n := by
  unfold bitLen
  split
  · subst_vars; decide
  · exact Nat.lt_log2_self

/-- A number below `2 ^ b` has bit length at most `b`. -/
theorem bitLen_le_of_lt {n b : Nat} (h : n < 2 ^ b) : bitLen n ≤ b := by
  unfold bitLen
  split
  · exact Nat.zero_le _
  · rename_i h0
    exact Nat.succ_le_of_lt ((Nat.log2_lt h0).2 h)

/-- A number below `2 ^ 254` has bit length at most 254. -/
theorem bitLen_le_254 {n : Nat} (h : n < 2 ^ 254) : bitLen n ≤ 254 := bitLen_le_of_lt h

/-- Powers of two are monotone. -/
theorem two_pow_le_two_pow {a b : Nat} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b :=
  Nat.pow_le_pow_right (by decide) h

/-- A number at most `m` fits the bit length of `m`, once `m` is a legal width. -/
theorem fitsBits_of_le {x m w : Nat} (hx : x ≤ m) (hm : m < 2 ^ 254) (hw : bitLen m ≤ w) (hw' : w < 255) :
    Zkir.fitsBits (Fr.ofNat x) w = true := by
  have hxM : x < Fr.modulus := Nat.lt_of_le_of_lt hx (Nat.lt_trans hm Fr.two_pow_254_lt_modulus)
  have hlt : x < 2 ^ w :=
    Nat.lt_of_le_of_lt hx (Nat.lt_of_lt_of_le (lt_two_pow_bitLen m) (two_pow_le_two_pow hw))
  simp [Zkir.fitsBits, Zkir.frBits, Fr.val_ofNat_of_lt hxM, hw', hlt]

/-! ## Facts about the predicates -/

/-- A number below the modulus is read back unchanged from its field image. -/
theorem Uint.Is.val_eq {m : Nat} {a : Uint m} {n : Nat} (hm : m < Fr.modulus) (h : Uint.Is p env a n) :
    (Fr.ofNat n).val = n :=
  Fr.val_ofNat_of_lt (Nat.lt_of_le_of_lt h.1 hm)

/-- Once `m` is below the modulus, a `Uint m` means at most one number. -/
theorem Uint.Is.unique {m : Nat} {a : Uint m} {x y : Nat} (hm : m < Fr.modulus)
    (hx : Uint.Is p env a x) (hy : Uint.Is p env a y) : x = y := by
  have := hx.2.symm.trans hy.2
  exact (Fr.ofNat_inj (Nat.lt_of_le_of_lt hx.1 hm) (Nat.lt_of_le_of_lt hy.1 hm)).1 (Option.some.inj this)

/-- A `Boolean` means at most one truth value. -/
theorem Boolean.Is.unique {b : Boolean} {u v : Bool} (hu : Boolean.Is p env b u) (hv : Boolean.Is p env b v) :
    u = v :=
  Fr.ofBool_inj.1 (Option.some.inj (hu.symm.trans hv))

/-- The bound `Uint.maxBound` is below `2 ^ 254`, hence below the modulus. -/
theorem Uint.maxBound_lt : Uint.maxBound < 2 ^ 254 := by decide

/-! ## Evaluation helpers -/

/-- `asBool` reads back the field image of a truth value. -/
theorem asBool_ofBool (b : Bool) : asBool (Fr.ofBool b) = some b := by
  cases b <;> rfl

/-- The constant 0 reads as false. -/
theorem asBool_ofInt_zero : asBool (Fr.ofInt 0) = some false := rfl

/-- The constant 1 reads as true. -/
theorem asBool_ofInt_one : asBool (Fr.ofInt 1) = some true := rfl

/-- A natural-number constant evaluates to its field image. -/
theorem eval_const_nat (n : Nat) : (Expr.const (n : Int)).eval p env = some (Fr.ofNat n) := rfl

/-- `Expr.sel` is `select` with a negated condition folded away: it means the same. -/
theorem Expr.eval_sel (c a b : Expr) : (Expr.sel c a b).eval p env = (Expr.select c a b).eval p env := by
  unfold Expr.sel
  split
  · rename_i s
    simp only [Expr.eval]
    cases s.eval p env with
    | none => rfl
    | some sv =>
      cases a.eval p env <;> cases b.eval p env <;>
        (cases hq : asBool sv with
         | none => simp [hq]
         | some bv => cases bv <;> simp [hq, asBool_ofInt_zero, asBool_ofInt_one])
  · rfl

/-- A select on a Boolean condition picks its first branch on true. -/
theorem Expr.eval_select {c a b : Expr} {u : Bool} {x y : Fr} (hc : c.eval p env = some (Fr.ofBool u))
    (ha : a.eval p env = some x) (hb : b.eval p env = some y) :
    (Expr.select c a b).eval p env = some (if u then x else y) := by
  simp [Expr.eval, hc, ha, hb, asBool_ofBool]

/-- `Expr.sel` on a Boolean condition picks its first branch on true. -/
theorem Expr.eval_sel' {c a b : Expr} {u : Bool} {x y : Fr} (hc : c.eval p env = some (Fr.ofBool u))
    (ha : a.eval p env = some x) (hb : b.eval p env = some y) :
    (Expr.sel c a b).eval p env = some (if u then x else y) := by
  rw [Expr.eval_sel]; exact Expr.eval_select hc ha hb

/-- `¬ (y < x)` as a Boolean is `x ≤ y`. -/
theorem Bool.not_decide_lt (x y : Nat) : (!decide (y < x)) = decide (x ≤ y) := by
  by_cases h : x ≤ y <;> simp [h, Nat.not_lt] <;> omega

/-! ## The 248-bit cap

Every way of making a `Uint` except `Field.unsafeToUint` passes its expression
through `Uint.capped`, which is the expression itself within Compact's limit
and an `invalid` expression (no value; rejected by the emitter) past it. -/

/-- Within Compact's limit the cap changes nothing. -/
theorem Uint.capped_of_le {b : Nat} (h : b ≤ Uint.maxBound) (e : Expr) : Uint.capped b e = e := by
  simp [Uint.capped, h]

/-- Past Compact's limit a capped expression has no value. -/
theorem Uint.capped_eval_of_gt {b : Nat} (h : ¬ b ≤ Uint.maxBound) (e : Expr) :
    (Uint.capped b e).eval p env = none := by
  simp only [Uint.capped, h, ↓reduceIte]; rfl

/-- A capped expression means what the expression means, within the limit. -/
theorem Uint.capped_eval {b : Nat} (h : b ≤ Uint.maxBound) (e : Expr) :
    (Uint.capped b e).eval p env = e.eval p env := by rw [Uint.capped_of_le h]

/-- Compact's limit is below `2 ^ 254`: every capped bound is a legal comparison width. -/
theorem Uint.lt_of_le_maxBound {m : Nat} (h : m ≤ Uint.maxBound) : m < 2 ^ 254 :=
  Nat.lt_of_le_of_lt h (by decide)

/-- Compact's limit is below the field modulus. -/
theorem Uint.lt_modulus_of_le_maxBound {m : Nat} (h : m ≤ Uint.maxBound) : m < Fr.modulus :=
  Nat.lt_trans (Uint.lt_of_le_maxBound h) Fr.two_pow_254_lt_modulus

/-! ## Literals -/

/-- `Uint.lit n` means `n`, for `n` within Compact's limit. -/
theorem Uint.lit_is {n : Nat} (hn : n ≤ Uint.maxBound) : Uint.Is p env (Uint.lit n) n :=
  ⟨Nat.le_refl n, by show (Uint.capped n _).eval p env = _; rw [Uint.capped_eval hn]; rfl⟩

/-- Past Compact's limit, `Uint.lit n` has no value (the emitter rejects it). -/
theorem Uint.lit_too_large {n : Nat} (hn : ¬ n ≤ Uint.maxBound) : (Uint.lit n).expr.eval p env = none :=
  Uint.capped_eval_of_gt hn _

/-- `Uint.ofNat n : Uint m` means `n`, for `m` within Compact's limit. -/
theorem Uint.ofNat_is {m n : Nat} (h : n ≤ m) (hm : m ≤ Uint.maxBound) :
    Uint.Is p env (Uint.ofNat n h : Uint m) n :=
  ⟨h, by show (Uint.capped m _).eval p env = _; rw [Uint.capped_eval hm]; rfl⟩

/-- Past Compact's limit, `Uint.ofNat n : Uint m` has no value. -/
theorem Uint.ofNat_too_large {m n : Nat} (h : n ≤ m) (hm : ¬ m ≤ Uint.maxBound) :
    (Uint.ofNat n h : Uint m).expr.eval p env = none :=
  Uint.capped_eval_of_gt hm _

/-- A numeral of type `Uint m` that fits means its number, for `m` within Compact's limit. -/
theorem Uint.numeral_is {m n : Nat} (h : n ≤ m) (hm : m ≤ Uint.maxBound) :
    Uint.Is p env (OfNat.ofNat n : Uint m) n := by
  refine ⟨h, ?_⟩
  show (if n ≤ m then Uint.capped m (Expr.const n) else _).eval p env = _
  simp only [h, ↓reduceIte]; rw [Uint.capped_eval hm]; rfl

/-- A numeral of type `Uint m` that does not fit has no value (the emitter rejects it). -/
theorem Uint.numeral_too_large {m n : Nat} (h : ¬ n ≤ m) :
    (OfNat.ofNat n : Uint m).expr.eval p env = none := by
  show (if n ≤ m then Uint.capped m (Expr.const n) else _).eval p env = _
  simp only [h, ↓reduceIte]; rfl

/-- Past Compact's limit, no numeral of type `Uint m` has a value. -/
theorem Uint.numeral_past_cap {m n : Nat} (hm : ¬ m ≤ Uint.maxBound) :
    (OfNat.ofNat n : Uint m).expr.eval p env = none := by
  show (if n ≤ m then Uint.capped m (Expr.const n) else _).eval p env = _
  split
  · exact Uint.capped_eval_of_gt hm _
  · rfl

/-- A `Field` numeral means its number reduced into the field. -/
theorem Field.numeral_is (n : Nat) : Field.Is p env (OfNat.ofNat n : Field) (Fr.ofNat n) := rfl

/-- `Field.ofNat n` means `n` reduced into the field. -/
theorem Field.ofNat_is (n : Nat) : Field.Is p env (Field.ofNat n) (Fr.ofNat n) := rfl

/-! ## `Uint` arithmetic -/

/-- What `+` on `Uint` builds: the sum, or `invalid` past Compact's limit. -/
theorem Uint.add_expr {m k : Nat} (a : Uint m) (b : Uint k) :
    (a + b).expr = Uint.capped (m + k) (.add a.expr b.expr) := rfl

/-- What `*` on `Uint` builds: the product, or `invalid` past Compact's limit. -/
theorem Uint.mul_expr {m k : Nat} (a : Uint m) (b : Uint k) :
    (a * b).expr = Uint.capped (m * k) (.mul a.expr b.expr) := rfl

/-- `a + b` means the sum of the numbers, with no wrap-around, and is within `m + k`. -/
theorem Uint.add_is {m k x y : Nat} {a : Uint m} {b : Uint k} (hcap : m + k ≤ Uint.maxBound)
    (ha : Uint.Is p env a x) (hb : Uint.Is p env b y) : Uint.Is p env (a + b) (x + y) := by
  refine ⟨Nat.add_le_add ha.1 hb.1, ?_⟩
  rw [Uint.add_expr, Uint.capped_eval hcap]
  simp [Expr.eval, ha.2, hb.2, Fr.ofNat_add]

/-- Past Compact's limit, `a + b` has no value. -/
theorem Uint.add_too_large {m k : Nat} (a : Uint m) (b : Uint k) (h : ¬ m + k ≤ Uint.maxBound) :
    (a + b).expr.eval p env = none := by
  rw [Uint.add_expr]; exact Uint.capped_eval_of_gt h _

/-- `a * b` means the product of the numbers, with no wrap-around, and is within `m * k`. -/
theorem Uint.mul_is {m k x y : Nat} {a : Uint m} {b : Uint k} (hcap : m * k ≤ Uint.maxBound)
    (ha : Uint.Is p env a x) (hb : Uint.Is p env b y) : Uint.Is p env (a * b) (x * y) := by
  refine ⟨Nat.mul_le_mul ha.1 hb.1, ?_⟩
  rw [Uint.mul_expr, Uint.capped_eval hcap]
  simp [Expr.eval, ha.2, hb.2, Fr.ofNat_mul]

/-- Past Compact's limit, `a * b` has no value. -/
theorem Uint.mul_too_large {m k : Nat} (a : Uint m) (b : Uint k) (h : ¬ m * k ≤ Uint.maxBound) :
    (a * b).expr.eval p env = none := by
  rw [Uint.mul_expr]; exact Uint.capped_eval_of_gt h _

/-- Since the sum is within `Uint.maxBound`, the field value really is the sum. -/
theorem Uint.add_val {m k x y : Nat} (hcap : m + k ≤ Uint.maxBound) (hx : x ≤ m) (hy : y ≤ k) :
    (Fr.ofNat (x + y)).val = x + y :=
  Fr.val_ofNat_of_lt (by have := Uint.maxBound_lt; have := Fr.two_pow_254_lt_modulus; omega)

/-- Since the product is within `Uint.maxBound`, the field value really is the product. -/
theorem Uint.mul_val {m k x y : Nat} (hcap : m * k ≤ Uint.maxBound) (hx : x ≤ m) (hy : y ≤ k) :
    (Fr.ofNat (x * y)).val = x * y := by
  have := Nat.mul_le_mul hx hy
  exact Fr.val_ofNat_of_lt (by have := Uint.maxBound_lt; have := Fr.two_pow_254_lt_modulus; omega)

/-- `widen` keeps the number, for a new bound within Compact's limit. -/
theorem Uint.widen_is {m k n : Nat} {a : Uint m} (h : m ≤ k) (hk : k ≤ Uint.maxBound)
    (ha : Uint.Is p env a n) : Uint.Is p env (a.widen h) n :=
  ⟨Nat.le_trans ha.1 h, by show (Uint.capped k _).eval p env = _; rw [Uint.capped_eval hk]; exact ha.2⟩

/-- Widening past Compact's limit gives no value. -/
theorem Uint.widen_too_large {m k : Nat} (a : Uint m) (h : m ≤ k) (hk : ¬ k ≤ Uint.maxBound) :
    (a.widen h).expr.eval p env = none :=
  Uint.capped_eval_of_gt hk _

/-- `toField` gives the field image of the number. -/
theorem Uint.toField_is {m n : Nat} {a : Uint m} (ha : Uint.Is p env a n) :
    Field.Is p env a.toField (Fr.ofNat n) := ha.2

/-- `unsafeToUint` is a `Uint m` holding the value only when the caller's bound is right. -/
theorem Field.unsafeToUint_is {a : Field} {v : Fr} (m : Nat) (h : v.val ≤ m) (ha : Field.Is p env a v) :
    Uint.Is p env (a.unsafeToUint m) v.val := by
  refine ⟨h, ?_⟩
  show a.expr.eval p env = _
  rw [ha, Fr.ofNat_val]

/-! ## `Uint` comparisons -/

/-- `a.lt b` compares the numbers, once both bounds are below `2 ^ 254` (a legal comparison width). -/
theorem Uint.lt_is {m k x y : Nat} {a : Uint m} {b : Uint k} (hm : m < 2 ^ 254) (hk : k < 2 ^ 254)
    (ha : Uint.Is p env a x) (hb : Uint.Is p env b y) : Boolean.Is p env (a.lt b) (decide (x < y)) := by
  have hw : max (bitLen m) (bitLen k) < 255 :=
    Nat.lt_succ_of_le (Nat.max_le.2 ⟨bitLen_le_254 hm, bitLen_le_254 hk⟩)
  have fx := fitsBits_of_le ha.1 hm (Nat.le_max_left _ _) hw
  have fy := fitsBits_of_le hb.1 hk (Nat.le_max_right _ _) hw
  have hxM := Nat.lt_of_le_of_lt ha.1 (Nat.lt_trans hm Fr.two_pow_254_lt_modulus)
  have hyM := Nat.lt_of_le_of_lt hb.1 (Nat.lt_trans hk Fr.two_pow_254_lt_modulus)
  simp [Boolean.Is, Uint.lt, Expr.eval, ha.2, hb.2, fx, fy, Fr.val_ofNat_of_lt hxM, Fr.val_ofNat_of_lt hyM]

/-- With a bound of bit length 255 or more, `lt` has no value: no width is legal. -/
theorem Uint.lt_too_wide {m k : Nat} (a : Uint m) (b : Uint k) (h : 255 ≤ max (bitLen m) (bitLen k)) :
    (a.lt b).expr.eval p env = none := by
  have hw : ¬ max (bitLen m) (bitLen k) < 255 := by omega
  simp only [Uint.lt, Expr.eval]
  cases a.expr.eval p env <;> cases b.expr.eval p env <;> simp [Zkir.fitsBits, Zkir.frBits, hw]

/-- `a.eq b` is equality of the numbers, once both bounds are below the modulus. -/
theorem Uint.eq_is {m k x y : Nat} {a : Uint m} {b : Uint k} (hm : m < Fr.modulus) (hk : k < Fr.modulus)
    (ha : Uint.Is p env a x) (hb : Uint.Is p env b y) : Boolean.Is p env (a.eq b) (decide (x = y)) := by
  have e := Fr.ofNat_inj (Nat.lt_of_le_of_lt ha.1 hm) (Nat.lt_of_le_of_lt hb.1 hk)
  simp [Boolean.Is, Uint.eq, Expr.eval, ha.2, hb.2, e]

/-! ## `Boolean` -/

/-- The constant `true`. -/
theorem Boolean.true_is : Boolean.Is p env Boolean.true Bool.true := rfl

/-- The constant `false`. -/
theorem Boolean.false_is : Boolean.Is p env Boolean.false Bool.false := rfl

/-- A truth value known while building. -/
theorem Boolean.ofBool_is (b : Bool) : Boolean.Is p env (Boolean.ofBool b) b := by
  cases b <;> rfl

/-- `not` negates. -/
theorem Boolean.not_is {a : Boolean} {u : Bool} (ha : Boolean.Is p env a u) :
    Boolean.Is p env a.not (!u) := by
  unfold Boolean.Is Boolean.not
  rw [Expr.eval_select ha rfl rfl]
  cases u <;> rfl

/-- `and` is conjunction. -/
theorem Boolean.and_is {a b : Boolean} {u v : Bool} (ha : Boolean.Is p env a u) (hb : Boolean.Is p env b v) :
    Boolean.Is p env (a.and b) (u && v) := by
  unfold Boolean.Is Boolean.and
  rw [Expr.eval_sel' ha hb rfl]
  cases u <;> rfl

/-- `or` is disjunction. -/
theorem Boolean.or_is {a b : Boolean} {u v : Bool} (ha : Boolean.Is p env a u) (hb : Boolean.Is p env b v) :
    Boolean.Is p env (a.or b) (u || v) := by
  unfold Boolean.Is Boolean.or
  rw [Expr.eval_sel' ha rfl hb]
  cases u <;> rfl

/-- `eq` on `Boolean` is equality of truth values. -/
theorem Boolean.eq_is {a b : Boolean} {u v : Bool} (ha : Boolean.Is p env a u) (hb : Boolean.Is p env b v) :
    Boolean.Is p env (a.eq b) (u == v) := by
  unfold Boolean.Is Boolean.eq at *
  simp only [Expr.eval, ha, hb]
  cases u <;> cases v <;> rfl

/-- `toField` on `Boolean` is 0 or 1. -/
theorem Boolean.toField_is {a : Boolean} {u : Bool} (ha : Boolean.Is p env a u) :
    Field.Is p env a.toField (Fr.ofBool u) := ha

/-! ## Comparison forms on `Uint`

`<.`, `>.`, `<=.`, `>=.`, `==.`, `!=.` between two `Uint`s, and between a `Uint`
and a `Nat` literal on either side. -/

section Cmp
variable {m k x y n : Nat} {a : Uint m} {b : Uint k}

/-- `a < b` on two `Uint`s. -/
theorem cmpLt_uint (hm : m < 2 ^ 254) (hk : k < 2 ^ 254) (ha : Uint.Is p env a x) (hb : Uint.Is p env b y) :
    Boolean.Is p env (cmpLt a b) (decide (x < y)) := Uint.lt_is hm hk ha hb
/-- `a > b` on two `Uint`s. -/
theorem cmpGt_uint (hm : m < 2 ^ 254) (hk : k < 2 ^ 254) (ha : Uint.Is p env a x) (hb : Uint.Is p env b y) :
    Boolean.Is p env (cmpGt a b) (decide (y < x)) := Uint.lt_is hk hm hb ha
/-- `a ≤ b` on two `Uint`s. -/
theorem cmpLe_uint (hm : m < 2 ^ 254) (hk : k < 2 ^ 254) (ha : Uint.Is p env a x) (hb : Uint.Is p env b y) :
    Boolean.Is p env (cmpLe a b) (decide (x ≤ y)) := by
  have := Boolean.not_is (Uint.lt_is hk hm hb ha)
  simp only [Bool.not_decide_lt] at this
  exact this
/-- `a ≥ b` on two `Uint`s. -/
theorem cmpGe_uint (hm : m < 2 ^ 254) (hk : k < 2 ^ 254) (ha : Uint.Is p env a x) (hb : Uint.Is p env b y) :
    Boolean.Is p env (cmpGe a b) (decide (y ≤ x)) := by
  have := Boolean.not_is (Uint.lt_is hm hk ha hb)
  simp only [Bool.not_decide_lt] at this
  exact this
/-- `a == b` on two `Uint`s. -/
theorem cmpEq_uint (hm : m < Fr.modulus) (hk : k < Fr.modulus) (ha : Uint.Is p env a x) (hb : Uint.Is p env b y) :
    Boolean.Is p env (cmpEq a b) (decide (x = y)) := Uint.eq_is hm hk ha hb
/-- `a != b` on two `Uint`s. -/
theorem cmpNe_uint (hm : m < Fr.modulus) (hk : k < Fr.modulus) (ha : Uint.Is p env a x) (hb : Uint.Is p env b y) :
    Boolean.Is p env (cmpNe a b) (decide (x ≠ y)) := by
  have := Boolean.not_is (Uint.eq_is hm hk ha hb)
  exact this

/-- `a < n` with a literal. -/
theorem cmpLt_uint_nat (hm : m < 2 ^ 254) (hn : n ≤ Uint.maxBound) (ha : Uint.Is p env a x) :
    Boolean.Is p env (cmpLt a n) (decide (x < n)) := Uint.lt_is hm (Uint.lt_of_le_maxBound hn) ha (Uint.lit_is hn)
/-- `a > n` with a literal. -/
theorem cmpGt_uint_nat (hm : m < 2 ^ 254) (hn : n ≤ Uint.maxBound) (ha : Uint.Is p env a x) :
    Boolean.Is p env (cmpGt a n) (decide (n < x)) := Uint.lt_is (Uint.lt_of_le_maxBound hn) hm (Uint.lit_is hn) ha
/-- `a ≤ n` with a literal. -/
theorem cmpLe_uint_nat (hm : m < 2 ^ 254) (hn : n ≤ Uint.maxBound) (ha : Uint.Is p env a x) :
    Boolean.Is p env (cmpLe a n) (decide (x ≤ n)) := by
  have := Boolean.not_is (Uint.lt_is (Uint.lt_of_le_maxBound hn) hm (Uint.lit_is hn) ha)
  simp only [Bool.not_decide_lt] at this
  exact this
/-- `a ≥ n` with a literal. -/
theorem cmpGe_uint_nat (hm : m < 2 ^ 254) (hn : n ≤ Uint.maxBound) (ha : Uint.Is p env a x) :
    Boolean.Is p env (cmpGe a n) (decide (n ≤ x)) := by
  have := Boolean.not_is (Uint.lt_is hm (Uint.lt_of_le_maxBound hn) ha (Uint.lit_is hn))
  simp only [Bool.not_decide_lt] at this
  exact this
/-- `a == n` with a literal. -/
theorem cmpEq_uint_nat (hm : m < Fr.modulus) (hn : n ≤ Uint.maxBound) (ha : Uint.Is p env a x) :
    Boolean.Is p env (cmpEq a n) (decide (x = n)) := Uint.eq_is hm (Uint.lt_modulus_of_le_maxBound hn) ha (Uint.lit_is hn)
/-- `a != n` with a literal. -/
theorem cmpNe_uint_nat (hm : m < Fr.modulus) (hn : n ≤ Uint.maxBound) (ha : Uint.Is p env a x) :
    Boolean.Is p env (cmpNe a n) (decide (x ≠ n)) := by
  have := Boolean.not_is (Uint.eq_is hm (Uint.lt_modulus_of_le_maxBound hn) ha (Uint.lit_is hn))
  exact this

/-- `n < a` with a literal. -/
theorem cmpLt_nat_uint (hm : m < 2 ^ 254) (hn : n ≤ Uint.maxBound) (ha : Uint.Is p env a x) :
    Boolean.Is p env (cmpLt n a) (decide (n < x)) := Uint.lt_is (Uint.lt_of_le_maxBound hn) hm (Uint.lit_is hn) ha
/-- `n > a` with a literal. -/
theorem cmpGt_nat_uint (hm : m < 2 ^ 254) (hn : n ≤ Uint.maxBound) (ha : Uint.Is p env a x) :
    Boolean.Is p env (cmpGt n a) (decide (x < n)) := Uint.lt_is hm (Uint.lt_of_le_maxBound hn) ha (Uint.lit_is hn)
/-- `n ≤ a` with a literal. -/
theorem cmpLe_nat_uint (hm : m < 2 ^ 254) (hn : n ≤ Uint.maxBound) (ha : Uint.Is p env a x) :
    Boolean.Is p env (cmpLe n a) (decide (n ≤ x)) := by
  have := Boolean.not_is (Uint.lt_is hm (Uint.lt_of_le_maxBound hn) ha (Uint.lit_is hn))
  simp only [Bool.not_decide_lt] at this
  exact this
/-- `n ≥ a` with a literal. -/
theorem cmpGe_nat_uint (hm : m < 2 ^ 254) (hn : n ≤ Uint.maxBound) (ha : Uint.Is p env a x) :
    Boolean.Is p env (cmpGe n a) (decide (x ≤ n)) := by
  have := Boolean.not_is (Uint.lt_is (Uint.lt_of_le_maxBound hn) hm (Uint.lit_is hn) ha)
  simp only [Bool.not_decide_lt] at this
  exact this
/-- `n == a` with a literal. -/
theorem cmpEq_nat_uint (hm : m < Fr.modulus) (hn : n ≤ Uint.maxBound) (ha : Uint.Is p env a x) :
    Boolean.Is p env (cmpEq n a) (decide (n = x)) := Uint.eq_is (Uint.lt_modulus_of_le_maxBound hn) hm (Uint.lit_is hn) ha
/-- `n != a` with a literal. -/
theorem cmpNe_nat_uint (hm : m < Fr.modulus) (hn : n ≤ Uint.maxBound) (ha : Uint.Is p env a x) :
    Boolean.Is p env (cmpNe n a) (decide (n ≠ x)) := by
  have := Boolean.not_is (Uint.eq_is (Uint.lt_modulus_of_le_maxBound hn) hm (Uint.lit_is hn) ha)
  exact this

end Cmp

/-! ## `select` -/

/-- `select` on `Field` picks by the condition. -/
theorem select_field_is {c : Boolean} {a b : Field} {u : Bool} {x y : Fr} (hc : Boolean.Is p env c u)
    (ha : Field.Is p env a x) (hb : Field.Is p env b y) :
    Field.Is p env (select c a b) (if u then x else y) := Expr.eval_sel' hc ha hb

/-- `select` on `Boolean` picks by the condition. -/
theorem select_boolean_is {c a b : Boolean} {u v w : Bool} (hc : Boolean.Is p env c u)
    (ha : Boolean.Is p env a v) (hb : Boolean.Is p env b w) :
    Boolean.Is p env (select c a b) (if u then v else w) := by
  have := Expr.eval_sel' hc ha hb
  unfold Boolean.Is
  cases u <;> exact this

/-- `select` on `Uint m` picks by the condition, and stays within `m`. -/
theorem select_uint_is {m x y : Nat} {c : Boolean} {a b : Uint m} {u : Bool} (hm : m ≤ Uint.maxBound)
    (hc : Boolean.Is p env c u) (ha : Uint.Is p env a x) (hb : Uint.Is p env b y) :
    Uint.Is p env (select c a b) (if u then x else y) := by
  have := Expr.eval_sel' hc ha.2 hb.2
  have e : (select c a b).expr.eval p env = (Expr.sel c.expr a.expr b.expr).eval p env :=
    Uint.capped_eval hm _
  cases u
  · exact ⟨hb.1, e.trans this⟩
  · exact ⟨ha.1, e.trans this⟩

/-- Past Compact's limit, `select` on `Uint m` has no value (like every way of making one). -/
theorem select_uint_too_large {m : Nat} (c : Boolean) (a b : Uint m) (hm : ¬ m ≤ Uint.maxBound) :
    (select c a b).expr.eval p env = none :=
  Uint.capped_eval_of_gt hm _

/-! ## `Field` -/

/-- `+` on `Field` is field addition (dropping a literal zero changes nothing). -/
theorem Field.add_is {a b : Field} {x y : Fr} (ha : Field.Is p env a x) (hb : Field.Is p env b y) :
    Field.Is p env (a + b) (x + y) := by
  show (Field.add a b).expr.eval p env = some (x + y)
  unfold Field.add
  unfold Field.Is at *
  split
  next _ _ h =>
    rw [h] at ha
    have hx : (0 : Fr) = x := Option.some.inj ha
    subst hx
    rw [Fr.zero_add]; exact hb
  next _ _ h _ =>
    rw [h] at hb
    have hy : (0 : Fr) = y := Option.some.inj hb
    subst hy
    rw [Fr.add_zero]; exact ha
  next => simp [Expr.eval, ha, hb]

/-- `*` on `Field` is field multiplication. -/
theorem Field.mul_is {a b : Field} {x y : Fr} (ha : Field.Is p env a x) (hb : Field.Is p env b y) :
    Field.Is p env (a * b) (x * y) := by
  unfold Field.Is at *
  show (Expr.mul a.expr b.expr).eval p env = _
  simp [Expr.eval, ha, hb]

/-- Negation on `Field`. -/
theorem Field.neg_is {a : Field} {x : Fr} (ha : Field.Is p env a x) : Field.Is p env (-a) (-x) := by
  unfold Field.Is at *
  show (Expr.neg a.expr).eval p env = _
  simp [Expr.eval, ha]

/-- `-` on `Field` is field subtraction. -/
theorem Field.sub_is {a b : Field} {x y : Fr} (ha : Field.Is p env a x) (hb : Field.Is p env b y) :
    Field.Is p env (a - b) (x - y) := by
  unfold Field.Is at *
  show (Expr.add a.expr (.neg b.expr)).eval p env = _
  simp [Expr.eval, ha, hb]; rfl

/-- `eq` on `Field` is equality of field elements. -/
theorem Field.eq_is {a b : Field} {x y : Fr} (ha : Field.Is p env a x) (hb : Field.Is p env b y) :
    Boolean.Is p env (a.eq b) (decide (x = y)) := by
  unfold Field.Is at *
  simp [Boolean.Is, Field.eq, Expr.eval, ha, hb]

/-! ## Statements

A statement-building operation is described by two lemmas: what running it does
to the builder state (`*_run`, exact), and what the statements it appends do
when executed (`*_correct`). The guard is the builder's `guard` at the time;
its meaning is a truth value `gb`. At the top level of a circuit it is the
constant 1, and the `*_unguarded` corollaries state that case. -/

/-- Running a bind runs the first part, then the second from where it left off. -/
theorem CircuitM.bind_run {α β : Type} (x : CircuitM α) (f : α → CircuitM β) (s : Build) :
    (x >>= f).run s = (f (x.run s).1).run (x.run s).2 := rfl

/-- Running `pure` changes nothing. -/
theorem CircuitM.pure_run {α : Type} (a : α) (s : Build) : (pure a : CircuitM α).run s = (a, s) := rfl

/-- Executing a list of statements in two parts. -/
theorem execAll_append (l₁ l₂ : List Stmt) (st : RunState) :
    execAll p (l₁ ++ l₂) st = (execAll p l₁ st).bind (execAll p l₂) := by
  induction l₁ generalizing st with
  | nil => rfl
  | cons s l ih =>
    simp only [List.cons_append, execAll]
    cases s.exec p st with
    | none => rfl
    | some st' => exact ih st'

/-- Executing a single statement. -/
theorem execAll_single (s : Stmt) (st : RunState) : execAll p [s] st = s.exec p st := by
  simp only [execAll]; cases s.exec p st <;> rfl

/-- The constant guard 1 means true. -/
theorem guard_one_is : Boolean.Is p env ⟨.const 1⟩ true := rfl

/-! ### Guards -/

/-- The condition `require` asserts under guard `g`: `c`, or `c` where `g` holds and true elsewhere. -/
def requireCond (g c : Expr) : Expr :=
  match g with
  | .const 1 => c
  | g => .select g c (.const 1)

/-- The value a checked operation returns under guard `g` (`Damp.guarded`). -/
def guardedExpr (g e : Expr) : Expr :=
  match g with
  | .const 1 => e
  | g => .select g e (.const 0)

/-- `guarded` reads the guard and builds `guardedExpr`. -/
theorem guarded_run (e : Expr) (s : Build) : (guarded e).run s = (guardedExpr s.guard e, s) := by
  obtain ⟨n, st, g, er⟩ := s
  cases g with
  | const c =>
    match c with
    | .ofNat 0 => rfl | .ofNat 1 => rfl | .ofNat (_+2) => rfl | .negSucc _ => rfl
  | _ => rfl

/-- The constant 1 means true and nothing else. -/
theorem const_one_is {gb : Bool} (h : (Expr.const 1).eval p env = some (Fr.ofBool gb)) : gb = true := by
  cases gb
  · exact absurd (Option.some.inj h) (by decide)
  · rfl

/-- The `require` condition means `¬g ∨ c`. Note that `c` is evaluated even where `g` is false. -/
theorem requireCond_eval {g c : Expr} {gb cb : Bool} (hg : g.eval p env = some (Fr.ofBool gb))
    (hc : c.eval p env = some (Fr.ofBool cb)) :
    (requireCond g c).eval p env = some (Fr.ofBool (!gb || cb)) := by
  unfold requireCond
  split
  · rw [const_one_is hg]; exact hc
  · rw [Expr.eval_select hg hc rfl]; cases gb <;> rfl

/-- A guarded value is the value where the guard holds and 0 elsewhere. -/
theorem guardedExpr_eval {g e : Expr} {gb : Bool} {v : Fr} (hg : g.eval p env = some (Fr.ofBool gb))
    (he : e.eval p env = some v) :
    (guardedExpr g e).eval p env = some (if gb then v else 0) := by
  unfold guardedExpr
  split
  · rw [const_one_is hg]; exact he
  · exact Expr.eval_select hg he rfl

/-! ### Executing single statements -/

/-- An assert of a Boolean succeeds exactly when it is true, and changes nothing. -/
theorem exec_assert {st : RunState} {c : Expr} {b : Bool} (msg : String)
    (h : c.eval p st.env = some (Fr.ofBool b)) :
    Stmt.exec p st (.assert c msg) = if b then some st else none := by
  simp [Stmt.exec, h, asBool_ofBool]

/-- A range check succeeds exactly when the value is in range, and changes nothing. -/
theorem exec_constrain {st : RunState} {e : Expr} {v : Fr} (r : Range) (h : e.eval p st.env = some v) :
    Stmt.exec p st (.constrain e r) = if r.holds v then some st else none := by
  simp [Stmt.exec, h]

/-! ### The range bridge -/

/-- The range Compact checks for a `Uint k` (the single entry of `Ty.ranges (.uint k)`). -/
def uintRange (k : Nat) : Range :=
  if k = 0 then .zero
  else if k = 1 then .bool
  else if k + 1 = 2 ^ bitLen k then .bits (bitLen k)
  else .below (k + 1) (bitLen (k + 1) + bitLen (k + 1) % 2)

/-- `Ty.ranges (.uint k)` is the single range `uintRange k`. -/
theorem ranges_uint (k : Nat) : Ty.ranges (.uint k) = [some (uintRange k)] := by
  simp only [Ty.ranges, uintRange]
  by_cases h0 : k = 0 <;> by_cases h1 : k = 1 <;> by_cases h2 : k + 1 = 2 ^ bitLen k <;> simp [h0, h1, h2]

/-- `Ty.ranges .bool` is the single range `.bool`. -/
theorem ranges_bool : Ty.ranges .bool = [some .bool] := rfl

/-- A number at least `2 ^ b` has bit length above `b`. -/
theorem lt_bitLen_of_le {n b : Nat} (h : 2 ^ b ≤ n) : b < bitLen n := by
  have hn : n ≠ 0 := by have := Nat.two_pow_pos b; omega
  unfold bitLen
  simp only [hn, ↓reduceIte]
  exact Nat.lt_succ_of_le ((Nat.le_log2 hn).2 h)

/-- The range check of `Uint k` holds exactly for values at most `k`, for every `k < 2 ^ 254`. -/
theorem uintRange_holds {k : Nat} (hk : k < 2 ^ 254) (x : Fr) :
    (uintRange k).holds x = decide (x.val ≤ k) := by
  have hkM : k + 1 < Fr.modulus := by have := Fr.two_pow_254_lt_modulus; omega
  have hb : (Fr.ofInt ((k + 1 : Nat) : Int)).val = k + 1 := Fr.val_ofNat_of_lt hkM
  unfold uintRange
  by_cases h0 : k = 0
  · subst h0
    simp only [↓reduceIte, Range.holds]
    rw [Bool.eq_iff_iff]; simp [Fr.eq_zero_iff]
  by_cases h1 : k = 1
  · subst h1
    simp only [↓reduceIte, Range.holds, h0]
    rw [Bool.eq_iff_iff]; simp [Fr.eq_zero_iff, Fr.eq_one_iff]; omega
  simp only [h0, h1, ↓reduceIte]
  by_cases h2 : k + 1 = 2 ^ bitLen k
  · simp only [h2, ↓reduceIte, Range.holds, Zkir.fitsBits, Zkir.frBits]
    have hw : bitLen k < 255 := Nat.lt_succ_of_le (bitLen_le_254 hk)
    rw [← h2, Bool.eq_iff_iff]; simp [hw]; omega
  · simp only [h2, ↓reduceIte, Range.holds, Zkir.fitsBits, Zkir.frBits, hb]
    -- `k + 1 = 2 ^ 254` would make the bit length of `k` exactly 254, the case above.
    have hk1 : k + 1 < 2 ^ 254 := by
      refine Nat.lt_of_le_of_ne (by omega) fun he => h2 ?_
      have h254 : bitLen k = 254 := by
        have := bitLen_le_254 hk
        have := lt_bitLen_of_le (show 2 ^ 253 ≤ k by
          have : 2 ^ 254 = 2 * 2 ^ 253 := by rw [Nat.pow_succ, Nat.mul_comm]
          omega)
        omega
      rw [h254, he]
    have hn := bitLen_le_of_lt hk1
    have hw : bitLen (k + 1) + bitLen (k + 1) % 2 < 255 := by omega
    have hkw : k + 1 < 2 ^ (bitLen (k + 1) + bitLen (k + 1) % 2) :=
      Nat.lt_of_lt_of_le (lt_two_pow_bitLen _) (two_pow_le_two_pow (Nat.le_add_right _ _))
    rw [Bool.eq_iff_iff]; simp [hw, hkw]; omega

/-- For `k ≥ 2 ^ 254` the range check of `Uint k` holds for no value: no legal width exists. -/
theorem uintRange_never {k : Nat} (hk : 2 ^ 254 ≤ k) (x : Fr) : (uintRange k).holds x = false := by
  have h0 : k ≠ 0 := by have := Nat.two_pow_pos 254; omega
  have h2 : 2 ≤ 2 ^ 254 := by decide
  have h1 : k ≠ 1 := by omega
  unfold uintRange
  simp only [h0, h1, ↓reduceIte]
  split
  · have := lt_bitLen_of_le hk
    have hw : ¬ bitLen k < 255 := by omega
    simp [Range.holds, Zkir.fitsBits, Zkir.frBits, hw]
  · have := lt_bitLen_of_le (show 2 ^ 254 ≤ k + 1 by omega)
    have hw : ¬ bitLen (k + 1) + bitLen (k + 1) % 2 < 255 := by omega
    simp [Range.holds, Zkir.fitsBits, Zkir.frBits, hw]

/-- The `Boolean` range check holds exactly for the images of truth values. -/
theorem boolRange_holds (x : Fr) : Range.bool.holds x = true ↔ ∃ b, x = Fr.ofBool b := by
  simp only [Range.holds, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (h | h)
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  · rintro ⟨b, rfl⟩; cases b
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- A variable holding a value that passed the `Uint m` range check is a `Uint m`. -/
theorem uint_of_holds {m : Nat} (hm : m < 2 ^ 254) {v : Var} (h : (uintRange m).holds (env v) = true) :
    Uint.Is p env (⟨.var v⟩ : Uint m) (env v).val := by
  rw [uintRange_holds hm] at h
  exact ⟨of_decide_eq_true h, by show some (env v) = _; rw [Fr.ofNat_val]⟩

/-- A variable holding a value that passed the `Boolean` range check is a `Boolean`. -/
theorem boolean_of_holds {v : Var} (h : Range.bool.holds (env v) = true) :
    ∃ b, Boolean.Is p env (⟨.var v⟩ : Boolean) b := by
  obtain ⟨b, hb⟩ := (boolRange_holds _).1 h
  exact ⟨b, by show some (env v) = _; rw [hb]⟩

/-! ### `require` -/

/-- `require c` appends one assert of `requireCond guard c`. -/
theorem require_run (c : Boolean) (msg : String) (s : Build) :
    (require c msg).run s = ((), { s with stmts := s.stmts.push (.assert (requireCond s.guard c.expr) msg) }) :=
  rfl

/-- `require c` succeeds exactly when the guard is false or `c` is true. -/
theorem require_correct {st : RunState} {g : Expr} {c : Boolean} {gb cb : Bool} (msg : String)
    (hg : Boolean.Is p st.env ⟨g⟩ gb) (hc : Boolean.Is p st.env c cb) :
    execAll p [.assert (requireCond g c.expr) msg] st = if (!gb || cb) then some st else none := by
  rw [execAll_single, exec_assert msg (requireCond_eval hg hc)]

/-- `require c` at the top level succeeds exactly when `c` is true. -/
theorem require_correct_unguarded {st : RunState} {c : Boolean} {cb : Bool} (msg : String)
    (hc : Boolean.Is p st.env c cb) :
    execAll p [.assert (requireCond (.const 1) c.expr) msg] st = if cb then some st else none := by
  rw [require_correct msg guard_one_is hc]; rfl

/-! ### `Uint.sub` -/

/-- `a.sub b` appends the non-negativity assert and returns the guarded difference. -/
theorem Uint.sub_run {m k : Nat} (a : Uint m) (b : Uint k) (s : Build) :
    (a.sub b).run s =
      (⟨guardedExpr s.guard (.add a.expr (.neg b.expr))⟩,
       { s with stmts := s.stmts.push (.assert (requireCond s.guard (a.lt b).not.expr)
           "result of subtraction would be negative") }) := by
  unfold Uint.sub
  rw [CircuitM.bind_run]
  show (do let r ← guarded (.add a.expr (.neg b.expr)); pure (⟨r⟩ : Uint m) : CircuitM _).run
    { s with stmts := s.stmts.push _ } = _
  rw [CircuitM.bind_run, guarded_run]; rfl

/-- `a.sub b`: the assert succeeds exactly when the guard is false or `y ≤ x`; when it
    does, the result is `x - y` where the guard holds and 0 where it does not. -/
theorem Uint.sub_correct {m k x y : Nat} {a : Uint m} {b : Uint k} {g : Expr} {gb : Bool} {st : RunState}
    (hm : m < 2 ^ 254) (hk : k < 2 ^ 254)
    (ha : Uint.Is p st.env a x) (hb : Uint.Is p st.env b y) (hg : Boolean.Is p st.env ⟨g⟩ gb) :
    execAll p [.assert (requireCond g (a.lt b).not.expr) "result of subtraction would be negative"] st
        = (if (!gb || decide (y ≤ x)) then some st else none) ∧
    ((!gb || decide (y ≤ x)) = true →
      Uint.Is p st.env (⟨guardedExpr g (.add a.expr (.neg b.expr))⟩ : Uint m) (if gb then x - y else 0)) := by
  have hc := Boolean.not_is (Uint.lt_is hm hk ha hb)
  rw [Bool.not_decide_lt] at hc
  refine ⟨require_correct _ hg hc, fun hok => ?_⟩
  have hxM : x < Fr.modulus := Nat.lt_of_le_of_lt ha.1 (Nat.lt_trans hm Fr.two_pow_254_lt_modulus)
  cases gb
  · exact ⟨Nat.zero_le _, guardedExpr_eval hg (v := Fr.ofNat x + -Fr.ofNat y)
      (by simp [Expr.eval, ha.2, hb.2])⟩
  · have hyx : y ≤ x := by simpa using hok
    refine ⟨Nat.le_trans (Nat.sub_le x y) ha.1, ?_⟩
    rw [guardedExpr_eval hg (v := Fr.ofNat x + -Fr.ofNat y) (by simp [Expr.eval, ha.2, hb.2])]
    simp [Fr.ofNat_add_neg hyx hxM]

/-- `a.sub b` at the top level: succeeds exactly when `y ≤ x`, and then means `x - y`. -/
theorem Uint.sub_correct_unguarded {m k x y : Nat} {a : Uint m} {b : Uint k} {st : RunState}
    (hm : m < 2 ^ 254) (hk : k < 2 ^ 254) (ha : Uint.Is p st.env a x) (hb : Uint.Is p st.env b y) :
    execAll p [.assert (requireCond (.const 1) (a.lt b).not.expr) "result of subtraction would be negative"] st
        = (if y ≤ x then some st else none) ∧
    (y ≤ x → Uint.Is p st.env (⟨guardedExpr (.const 1) (.add a.expr (.neg b.expr))⟩ : Uint m) (x - y)) := by
  have h := Uint.sub_correct hm hk ha hb guard_one_is
  simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq, ↓reduceIte] at h
  exact ⟨by rw [h.1], h.2⟩

/-! ### Range checks: `constrainTy`, `Uint.castTo`, `Field.toUint` -/

/-- `constrainTy e (.uint k)` appends one range check. -/
theorem constrainTy_uint_run (e : Expr) (k : Nat) (s : Build) :
    (constrainTy e (.uint k)).run s = ((), { s with stmts := s.stmts.push (.constrain e (uintRange k)) }) := by
  unfold constrainTy; rw [ranges_uint]; rfl

/-- Checking a `Uint k` type within Compact's limit changes nothing. -/
theorem checkUintBounds_uint_run {k : Nat} (hk : k ≤ Uint.maxBound) (s : Build) :
    (checkUintBounds [.uint k]).run s = ((), s) := by
  show ((if k ≤ Uint.maxBound then pure () else buildError (Uint.tooLarge k) : CircuitM Unit)
    >>= fun _ => pure ()).run s = _
  rw [CircuitM.bind_run]; simp only [hk, ↓reduceIte]; rfl

/-- Checking a `Uint k` type past Compact's limit records the error. -/
theorem checkUintBounds_uint_run_gt {k : Nat} (hk : ¬ k ≤ Uint.maxBound) (s : Build) :
    (checkUintBounds [.uint k]).run s = ((), { s with errors := s.errors.push (Uint.tooLarge k) }) := by
  show ((if k ≤ Uint.maxBound then pure () else buildError (Uint.tooLarge k) : CircuitM Unit)
    >>= fun _ => pure ()).run s = _
  rw [CircuitM.bind_run]; simp only [hk, ↓reduceIte]; rfl

/-- Widening `castTo` emits nothing and returns the value unchanged. -/
theorem Uint.castTo_run_le {m : Nat} (a : Uint m) {k : Nat} (h : m ≤ k) (hk : k ≤ Uint.maxBound)
    (s : Build) : (a.castTo k).run s = (⟨a.expr⟩, s) := by
  unfold Uint.castTo
  rw [CircuitM.bind_run, checkUintBounds_uint_run hk]
  simp only [h, ↓reduceIte, Uint.capped_of_le hk]; rfl

/-- Narrowing `castTo` appends a range check of the guarded value, and returns that value. -/
theorem Uint.castTo_run_gt {m : Nat} (a : Uint m) {k : Nat} (h : ¬ m ≤ k) (hk : k ≤ Uint.maxBound)
    (s : Build) :
    (a.castTo k).run s =
      (⟨guardedExpr s.guard a.expr⟩,
       { s with stmts := s.stmts.push (.constrain (guardedExpr s.guard a.expr) (uintRange k)) }) := by
  unfold Uint.castTo
  rw [CircuitM.bind_run, checkUintBounds_uint_run hk]
  simp only [h, ↓reduceIte, Uint.capped_of_le hk]
  rw [CircuitM.bind_run, guarded_run, CircuitM.bind_run, constrainTy_uint_run]; rfl

/-- `castTo` to a bound past Compact's limit records an error, so the circuit is not emitted. -/
theorem Uint.castTo_error {m : Nat} (a : Uint m) {k : Nat} (hk : ¬ k ≤ Uint.maxBound) (s : Build) :
    ((a.castTo k).run s).2.errors = s.errors.push (Uint.tooLarge k) := by
  unfold Uint.castTo
  rw [CircuitM.bind_run, checkUintBounds_uint_run_gt hk]
  by_cases h : m ≤ k
  · simp only [h, ↓reduceIte]; rfl
  · simp only [h, ↓reduceIte]
    rw [CircuitM.bind_run, guarded_run, CircuitM.bind_run, constrainTy_uint_run]; rfl

/-- Widening `castTo` keeps the number. -/
theorem Uint.castTo_le_correct {m k x : Nat} {a : Uint m} (h : m ≤ k) (ha : Uint.Is p env a x) :
    Uint.Is p env (⟨a.expr⟩ : Uint k) x := ⟨Nat.le_trans ha.1 h, ha.2⟩

/-- A guarded range check of `Uint k` succeeds exactly when the guard is false or the value
    is at most `k`; the guarded value then means the number where the guard holds and 0 elsewhere. -/
theorem guarded_check_correct {k : Nat} {e g : Expr} {v : Fr} {gb : Bool} {st : RunState} (hk : k < 2 ^ 254)
    (he : e.eval p st.env = some v) (hg : Boolean.Is p st.env ⟨g⟩ gb) :
    execAll p [.constrain (guardedExpr g e) (uintRange k)] st
        = (if (!gb || decide (v.val ≤ k)) then some st else none) ∧
    ((!gb || decide (v.val ≤ k)) = true →
      Uint.Is p st.env (⟨guardedExpr g e⟩ : Uint k) (if gb then v.val else 0)) := by
  have hge := guardedExpr_eval hg he
  rw [execAll_single, exec_constrain _ hge, uintRange_holds hk]
  cases gb
  · refine ⟨by simp [Fr.val_zero], fun _ => ⟨Nat.zero_le _, ?_⟩⟩
    rw [hge]; rfl
  · refine ⟨by simp, fun hok => ⟨by simpa using hok, ?_⟩⟩
    rw [hge]; simp [Fr.ofNat_val]

/-- Narrowing `a.castTo k`: succeeds exactly when the guard is false or `x ≤ k`, and then
    means `x` where the guard holds and 0 elsewhere. -/
theorem Uint.castTo_correct {m k x : Nat} {a : Uint m} {g : Expr} {gb : Bool} {st : RunState}
    (hm : m < Fr.modulus) (hk : k < 2 ^ 254) (ha : Uint.Is p st.env a x) (hg : Boolean.Is p st.env ⟨g⟩ gb) :
    execAll p [.constrain (guardedExpr g a.expr) (uintRange k)] st
        = (if (!gb || decide (x ≤ k)) then some st else none) ∧
    ((!gb || decide (x ≤ k)) = true →
      Uint.Is p st.env (⟨guardedExpr g a.expr⟩ : Uint k) (if gb then x else 0)) := by
  have h := guarded_check_correct hk ha.2 hg
  rw [ha.val_eq hm] at h
  exact h

/-- Narrowing `a.castTo k` at the top level: succeeds exactly when `x ≤ k`, and then means `x`. -/
theorem Uint.castTo_correct_unguarded {m k x : Nat} {a : Uint m} {st : RunState}
    (hm : m < Fr.modulus) (hk : k < 2 ^ 254) (ha : Uint.Is p st.env a x) :
    execAll p [.constrain (guardedExpr (.const 1) a.expr) (uintRange k)] st
        = (if x ≤ k then some st else none) ∧
    (x ≤ k → Uint.Is p st.env (⟨guardedExpr (.const 1) a.expr⟩ : Uint k) x) := by
  have h := Uint.castTo_correct hm hk ha guard_one_is
  simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq, ↓reduceIte] at h
  exact ⟨by rw [h.1], h.2⟩

/-- `a.toUint k` appends a range check of the guarded value, and returns that value. -/
theorem Field.toUint_run (a : Field) {k : Nat} (hk : k ≤ Uint.maxBound) (s : Build) :
    (a.toUint k).run s =
      (⟨guardedExpr s.guard a.expr⟩,
       { s with stmts := s.stmts.push (.constrain (guardedExpr s.guard a.expr) (uintRange k)) }) := by
  unfold Field.toUint
  rw [CircuitM.bind_run, checkUintBounds_uint_run hk]
  rw [CircuitM.bind_run, guarded_run, CircuitM.bind_run, constrainTy_uint_run]
  simp only [Uint.capped_of_le hk]; rfl

/-- `toUint` to a bound past Compact's limit records an error, so the circuit is not emitted. -/
theorem Field.toUint_error (a : Field) {k : Nat} (hk : ¬ k ≤ Uint.maxBound) (s : Build) :
    ((a.toUint k).run s).2.errors = s.errors.push (Uint.tooLarge k) := by
  unfold Field.toUint
  rw [CircuitM.bind_run, checkUintBounds_uint_run_gt hk]
  rw [CircuitM.bind_run, guarded_run, CircuitM.bind_run, constrainTy_uint_run]; rfl

/-- `a.toUint k`: succeeds exactly when the guard is false or `v ≤ k`, and then means `v`
    where the guard holds and 0 elsewhere. -/
theorem Field.toUint_correct {k : Nat} {a : Field} {v : Fr} {g : Expr} {gb : Bool} {st : RunState}
    (hk : k < 2 ^ 254) (ha : Field.Is p st.env a v) (hg : Boolean.Is p st.env ⟨g⟩ gb) :
    execAll p [.constrain (guardedExpr g a.expr) (uintRange k)] st
        = (if (!gb || decide (v.val ≤ k)) then some st else none) ∧
    ((!gb || decide (v.val ≤ k)) = true →
      Uint.Is p st.env (⟨guardedExpr g a.expr⟩ : Uint k) (if gb then v.val else 0)) :=
  guarded_check_correct hk ha hg

/-- `a.toUint k` at the top level: succeeds exactly when `v ≤ k`, and then means `v`. -/
theorem Field.toUint_correct_unguarded {k : Nat} {a : Field} {v : Fr} {st : RunState}
    (hk : k < 2 ^ 254) (ha : Field.Is p st.env a v) :
    execAll p [.constrain (guardedExpr (.const 1) a.expr) (uintRange k)] st
        = (if v.val ≤ k then some st else none) ∧
    (v.val ≤ k → Uint.Is p st.env (⟨guardedExpr (.const 1) a.expr⟩ : Uint k) v.val) := by
  have h := Field.toUint_correct hk ha guard_one_is
  simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq, ↓reduceIte] at h
  exact ⟨by rw [h.1], h.2⟩

/-- With a bound of `2 ^ 254` or more, `toUint` never succeeds, guard or no guard. -/
theorem Field.toUint_too_wide {k : Nat} {a : Field} {v : Fr} {g : Expr} {gb : Bool} {st : RunState}
    (hk : 2 ^ 254 ≤ k) (ha : Field.Is p st.env a v) (hg : Boolean.Is p st.env ⟨g⟩ gb) :
    execAll p [.constrain (guardedExpr g a.expr) (uintRange k)] st = none := by
  rw [execAll_single, exec_constrain _ (guardedExpr_eval hg ha), uintRange_never hk]; rfl

/-! ### Witnesses -/

/-- A witness statement reading one value checked against `r`: when it succeeds, the
    variable holds a value that passed `r` (the value 0 if the guard was false). -/
theorem exec_witness_single {g : Expr} {name : String} {args : List Expr} {v : Var} {r : Range}
    {shape : Shape} {st st' : RunState}
    (h : Stmt.exec p st (.witness g name args [(v, some r)] shape) = some st') :
    r.holds (st'.env v) = true := by
  simp only [Stmt.exec, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at h
  cases hg : g.eval p st.env with
  | none => simp [hg] at h
  | some gv =>
    cases ha : asBool gv with
    | none => simp [hg, ha] at h
    | some act =>
      cases ho : Zkir.readOne act st.priv with
      | none => simp [hg, ha, readAll, ho] at h
      | some xr =>
        obtain ⟨x, rest⟩ := xr
        by_cases hx : r.holds x = true
        · simp [hg, ha, readAll, ho, hx] at h
          subst h
          simp [Env.set, hx]
        · simp [hg, ha, readAll, ho, hx] at h

/-- `Value.ranges (Uint m)` is the single range `uintRange m`. -/
theorem valueRanges_uint (m : Nat) : Value.ranges (Uint m) = [some (uintRange m)] := by
  show Shape.ranges (.prim (.uint m)) = _
  simp [Shape.ranges, Shape.tys, ranges_uint]

/-- Asking for a `Uint m` appends one witness statement reading a fresh variable checked
    against the `Uint m` range. -/
theorem askWitness_uint_run {m : Nat} (hm : m ≤ Uint.maxBound) (name : String) (args : List Expr)
    (s : Build) :
    (askWitness name (Uint m) args).run s =
      (⟨.var s.«next»⟩, { s with
        «next» := s.«next» + 1
        stmts := s.stmts.push (.witness s.guard name args [(s.«next», some (uintRange m))] (.prim (.uint m))) }) := by
  unfold askWitness
  simp only [valueRanges_uint]
  show (do let x ← checkUintBounds [.uint m]; pure (⟨Uint.capped m (.var s.«next»)⟩ : Uint m) : CircuitM _).run
    { s with «next» := s.«next» + 1, stmts := _ } = _
  rw [CircuitM.bind_run, checkUintBounds_uint_run hm, Uint.capped_of_le hm]; rfl

/-- Asking for a `Uint m` past Compact's limit records an error, so the circuit is not emitted. -/
theorem askWitness_uint_error {m : Nat} (hm : ¬ m ≤ Uint.maxBound) (name : String) (args : List Expr)
    (s : Build) : ((askWitness name (Uint m) args).run s).2.errors = s.errors.push (Uint.tooLarge m) := by
  unfold askWitness
  simp only [valueRanges_uint]
  show ((do let x ← checkUintBounds [.uint m]; pure (⟨Uint.capped m (.var s.«next»)⟩ : Uint m) : CircuitM _).run
    { s with «next» := s.«next» + 1, stmts := _ }).2.errors = _
  rw [CircuitM.bind_run, checkUintBounds_uint_run_gt hm]; rfl

/-- Asking for a `Boolean` appends one witness statement reading a fresh variable checked
    against the `Boolean` range. -/
theorem askWitness_boolean_run (name : String) (args : List Expr) (s : Build) :
    (askWitness name Boolean args).run s =
      (⟨.var s.«next»⟩, { s with
        «next» := s.«next» + 1
        stmts := s.stmts.push (.witness s.guard name args [(s.«next», some .bool)] (.prim .bool)) }) := rfl

/-- When the witness statement for a `Uint m` succeeds, its result is a `Uint m`. -/
theorem askWitness_uint_correct {m : Nat} (hm : m < 2 ^ 254) {g : Expr} {name : String} {args : List Expr}
    {v : Var} {shape : Shape} {st st' : RunState}
    (h : Stmt.exec p st (.witness g name args [(v, some (uintRange m))] shape) = some st') :
    Uint.Is p st'.env (⟨.var v⟩ : Uint m) (st'.env v).val :=
  uint_of_holds hm (exec_witness_single h)

/-- When the witness statement for a `Boolean` succeeds, its result is a `Boolean`. -/
theorem askWitness_boolean_correct {g : Expr} {name : String} {args : List Expr}
    {v : Var} {shape : Shape} {st st' : RunState}
    (h : Stmt.exec p st (.witness g name args [(v, some .bool)] shape) = some st') :
    ∃ b, Boolean.Is p st'.env (⟨.var v⟩ : Boolean) b :=
  boolean_of_holds (exec_witness_single h)

/-! ### Circuit inputs (`mkCircuit`) -/

/-- The range checks `mkCircuit` puts in front of the body, one per checked input. -/
def inputChecks (ins : List Input) : List Stmt :=
  ins.filterMap fun i => i.range.map (Stmt.constrain (.var i.var))

/-- The body of `mkCircuit` starts with the range checks of its inputs. -/
theorem mkCircuit_body {φ : Type} [CircuitFn φ] (name : String) (names : List String) (f : φ) :
    ∃ rest, (mkCircuit name names f).body.toList = inputChecks (mkCircuit name names f).inputs ++ rest := by
  unfold mkCircuit
  generalize (CircuitFn.build f names).run = q
  obtain ⟨sig, st⟩ := q
  exact ⟨st.stmts.toList, by simp [inputChecks]⟩

/-- When the input checks succeed they change nothing, and every checked input is in range. -/
theorem execAll_inputChecks (ins : List Input) {st st' : RunState}
    (h : execAll p (inputChecks ins) st = some st') :
    st' = st ∧ ∀ i ∈ ins, ∀ r, i.range = some r → r.holds (st.env i.var) = true := by
  induction ins with
  | nil =>
    simp only [inputChecks, List.filterMap_nil, execAll, Option.some.injEq] at h
    exact ⟨h.symm, by simp⟩
  | cons i is ih =>
    cases hr : i.range with
    | none =>
      have h' : execAll p (inputChecks is) st = some st' := by simpa [inputChecks, hr] using h
      obtain ⟨e, hall⟩ := ih h'
      refine ⟨e, fun j hj r hjr => ?_⟩
      rcases List.mem_cons.1 hj with rfl | hj
      · rw [hr] at hjr; cases hjr
      · exact hall j hj r hjr
    | some r =>
      have h' : execAll p (Stmt.constrain (.var i.var) r :: inputChecks is) st = some st' := by
        simpa [inputChecks, hr] using h
      simp only [execAll, exec_constrain r (show (Expr.var i.var).eval p st.env = some (st.env i.var) from rfl)] at h'
      by_cases hx : r.holds (st.env i.var) = true
      · simp only [hx, ↓reduceIte] at h'
        obtain ⟨e, hall⟩ := ih h'
        refine ⟨e, fun j hj r' hjr => ?_⟩
        rcases List.mem_cons.1 hj with rfl | hj
        · rw [hr] at hjr; cases hjr; exact hx
        · exact hall j hj r' hjr
      · simp [hx] at h'

/-- If the body of `mkCircuit` runs, every circuit input passed its range check
    (evaluated in the environment the body starts from). -/
theorem mkCircuit_inputs_hold {φ : Type} [CircuitFn φ] (name : String) (names : List String) (f : φ)
    {st st' : RunState} (h : execAll p (mkCircuit name names f).body.toList st = some st') :
    ∀ i ∈ (mkCircuit name names f).inputs, ∀ r, i.range = some r → r.holds (st.env i.var) = true := by
  obtain ⟨rest, hb⟩ := mkCircuit_body name names f
  rw [hb, execAll_append] at h
  cases hc : execAll p (inputChecks (mkCircuit name names f).inputs) st with
  | none => rw [hc] at h; cases h
  | some s => exact (execAll_inputChecks _ hc).2

/-- The first input of a circuit whose first argument is a `Uint m` is variable 0 with the
    `Uint m` range check; the function is applied to `⟨.var 0⟩`. -/
theorem mkCircuit_uint_first {m : Nat} {φ : Type} [CircuitFn φ] (name : String) (names : List String)
    (f : Uint m → φ) :
    ∃ rest, (mkCircuit name names f).inputs =
      { name := names.headD "arg", var := 0, range := some (uintRange m) } :: rest := by
  unfold mkCircuit
  simp only [CircuitFn.build, valueRanges_uint]
  exact ⟨_, rfl⟩

/-- The first input of a circuit whose first argument is a `Boolean` is variable 0 with the
    `Boolean` range check; the function is applied to `⟨.var 0⟩`. -/
theorem mkCircuit_boolean_first {φ : Type} [CircuitFn φ] (name : String) (names : List String)
    (f : Boolean → φ) :
    ∃ rest, (mkCircuit name names f).inputs =
      { name := names.headD "arg", var := 0, range := some .bool } :: rest :=
  ⟨_, rfl⟩

/-- In a circuit whose first argument is a `Uint m`, once the body runs, the value the
    function receives (`Value.ofExprs [.var 0]`) is a `Uint m` in the environment the
    body starts from. -/
theorem mkCircuit_uint_arg {m : Nat} (hm : m ≤ Uint.maxBound) {φ : Type} [CircuitFn φ] (name : String)
    (names : List String) (f : Uint m → φ) {st st' : RunState}
    (h : execAll p (mkCircuit name names f).body.toList st = some st') :
    Uint.Is p st.env (Value.ofExprs [.var 0] : Uint m) (st.env 0).val := by
  obtain ⟨rest, hi⟩ := mkCircuit_uint_first name names f
  have := mkCircuit_inputs_hold name names f h _ (by rw [hi]; exact List.mem_cons_self ..) _ rfl
  have hv := uint_of_holds (p := p) (Uint.lt_of_le_maxBound hm) this
  exact ⟨hv.1, by show (Uint.capped m _).eval p st.env = _; rw [Uint.capped_eval hm]; exact hv.2⟩

/-- A circuit whose first argument is a `Uint m` past Compact's limit records an error, so
    it is not emitted, whether or not the argument is used. -/
theorem mkCircuit_uint_error {m : Nat} (hm : ¬ m ≤ Uint.maxBound) {φ : Type} [CircuitFn φ] (name : String)
    (names : List String) (f : Uint m → φ) : Uint.tooLarge m ∈ (mkCircuit name names f).errors := by
  -- The argument check is the last thing building the circuit does.
  obtain ⟨S, hS⟩ : ∃ S, ((CircuitFn.build f names).run).2 = ((checkUintBounds [.uint m]).run S).2 :=
    ⟨_, rfl⟩
  rw [checkUintBounds_uint_run_gt hm] at hS
  unfold mkCircuit
  generalize (CircuitFn.build f names).run = q at hS
  obtain ⟨sig, st⟩ := q
  simp only at hS
  simp [hS]

/-- In a circuit whose first argument is a `Boolean`, once the body runs that argument
    (`⟨.var 0⟩`) is a `Boolean` in the environment the body starts from. -/
theorem mkCircuit_boolean_arg {φ : Type} [CircuitFn φ] (name : String) (names : List String)
    (f : Boolean → φ) {st st' : RunState} (h : execAll p (mkCircuit name names f).body.toList st = some st') :
    ∃ b, Boolean.Is p st.env (⟨.var 0⟩ : Boolean) b := by
  obtain ⟨rest, hi⟩ := mkCircuit_boolean_first name names f
  have := mkCircuit_inputs_hold name names f h _ (by rw [hi]; exact List.mem_cons_self ..) _ rfl
  exact boolean_of_holds this

/-! ## Equality of whole values (`valueEq`, `Bytes.eq`) -/

/-- Evaluating a nonempty list of expressions, element by element. -/
theorem evalList_cons {e : Expr} {es : List Expr} {xs : List Fr} :
    Expr.evalList p env (e :: es) = some xs ↔
      ∃ x xs', e.eval p env = some x ∧ Expr.evalList p env es = some xs' ∧ xs = x :: xs' := by
  simp only [Expr.evalList]
  cases he : e.eval p env <;> cases hes : Expr.evalList p env es <;> simp [eq_comm]

/-- Element-wise equality tests evaluate to the element-wise comparisons. -/
theorem evalList_zipWith_eq : ∀ (es fs : List Expr) (xs ys : List Fr),
    Expr.evalList p env es = some xs → Expr.evalList p env fs = some ys →
    Expr.evalList p env (List.zipWith Expr.eq es fs) =
      some ((List.zipWith (fun x y => decide (x = y)) xs ys).map Fr.ofBool)
  | [], _, xs, _, h, _ => by
    simp only [Expr.evalList, Option.some.injEq] at h; subst h; rfl
  | _ :: _, [], _, ys, _, h => by
    simp only [Expr.evalList, Option.some.injEq] at h; subst h
    simp [Expr.evalList]
  | e :: es, f :: fs, xs, ys, hx, hy => by
    obtain ⟨x, xs', he, hes, rfl⟩ := evalList_cons.1 hx
    obtain ⟨y, ys', hf, hfs, rfl⟩ := evalList_cons.1 hy
    have ih := evalList_zipWith_eq es fs xs' ys' hes hfs
    simp [Expr.evalList, Expr.eval, he, hf, ih]

/-- Folding Boolean expressions with `select acc e 0` is their conjunction. -/
theorem eval_foldl_and : ∀ (es : List Expr) (acc : Expr) (b : Bool) (bs : List Bool),
    acc.eval p env = some (Fr.ofBool b) → Expr.evalList p env es = some (bs.map Fr.ofBool) →
    (es.foldl (fun acc e => .select acc e (.const 0)) acc).eval p env = some (Fr.ofBool (b && bs.all id))
  | [], _, b, bs, hacc, h => by
    cases bs with
    | nil => simpa using hacc
    | cons _ _ => simp [Expr.evalList] at h
  | e :: es, acc, b, bs, hacc, h => by
    cases bs with
    | nil =>
      obtain ⟨_, _, _, _, hh⟩ := evalList_cons.1 h
      simp at hh
    | cons c cs =>
      obtain ⟨x, xs', he, hes, hh⟩ := evalList_cons.1 h
      simp only [List.map_cons, List.cons.injEq] at hh
      obtain ⟨rfl, rfl⟩ := hh
      have hstep : (Expr.select acc e (.const 0)).eval p env = some (Fr.ofBool (b && c)) := by
        rw [Expr.eval_select hacc he rfl]; cases b <;> rfl
      have := eval_foldl_and es _ (b && c) cs hstep hes
      simpa [Bool.and_assoc] using this

/-- Element-wise comparison of equal-length lists is equality of the lists. -/
theorem all_zipWith_eq : ∀ (xs ys : List Fr), xs.length = ys.length →
    (List.zipWith (fun x y => decide (x = y)) xs ys).all id = decide (xs = ys)
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    have ih := all_zipWith_eq xs ys (by simpa using h)
    simp only [List.zipWith_cons_cons, List.all_cons, id, ih, List.cons.injEq]
    by_cases hxy : x = y <;> simp [hxy]

/-- `valueEq a b` is true exactly when all field elements of `a` and `b` are equal, given
    that they evaluate and have the same number of elements (always so for one type). -/
theorem valueEq_is {α : Type} [Value α] {a b : α} {xs ys : List Fr}
    (ha : Expr.evalList p env (Value.toExprs a) = some xs) (hb : Expr.evalList p env (Value.toExprs b) = some ys)
    (hl : xs.length = ys.length) :
    Boolean.Is p env (valueEq a b) (decide (xs = ys)) := by
  have hz := evalList_zipWith_eq _ _ _ _ ha hb
  rw [← all_zipWith_eq xs ys hl]
  unfold valueEq Boolean.Is
  generalize List.zipWith Expr.eq (Value.toExprs a) (Value.toExprs b) = zs at hz
  generalize List.zipWith (fun x y => decide (x = y)) xs ys = bs at hz
  cases zs with
  | nil =>
    cases bs with
    | nil => rfl
    | cons _ _ => simp [Expr.evalList] at hz
  | cons e es =>
    cases bs with
    | nil => obtain ⟨_, _, _, _, hh⟩ := evalList_cons.1 hz; simp at hh
    | cons c cs =>
      obtain ⟨x, xs', he, hes, hh⟩ := evalList_cons.1 hz
      simp only [List.map_cons, List.cons.injEq] at hh
      obtain ⟨rfl, rfl⟩ := hh
      have := eval_foldl_and es e c cs he hes
      simpa using this

/-- The limbs of a `Bytes n` value evaluate to these field elements. -/
def Bytes.Is (p : Zkir.Prims) (env : Env) {n : Nat} (a : Bytes n) (vs : List Fr) : Prop := Expr.evalList p env a.limbs = some vs

/-- `Bytes.eq` is true exactly when all limbs are equal. -/
theorem Bytes.eq_is {n : Nat} {a b : Bytes n} {xs ys : List Fr} (ha : Bytes.Is p env a xs) (hb : Bytes.Is p env b ys)
    (hl : xs.length = ys.length) : Boolean.Is p env (a.eq b) (decide (xs = ys)) :=
  valueEq_is (α := Bytes n) ha hb hl

end Damp
