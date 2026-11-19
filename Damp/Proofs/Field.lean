/-
Arithmetic facts about `Fr` needed to read field values back as numbers:
below the modulus, `Fr.ofNat` is faithful and `+`, `*`, subtraction and
comparison agree with the natural-number ones.
-/
import Damp.Field

namespace Damp.Fr

/-- `2 ^ 254` is below the modulus, so every number of at most 254 bits is a field element. -/
theorem two_pow_254_lt_modulus : 2 ^ 254 < modulus := by decide

/-- The value of `ofNat n` is `n` reduced modulo the field order. -/
theorem val_ofNat (n : Nat) : (ofNat n).val = n % modulus := rfl

/-- Below the modulus, `ofNat` keeps the number as it is. -/
theorem val_ofNat_of_lt {n : Nat} (h : n < modulus) : (ofNat n).val = n := Nat.mod_eq_of_lt h

/-- Below the modulus, `ofNat` is injective. -/
theorem ofNat_inj {a b : Nat} (ha : a < modulus) (hb : b < modulus) : ofNat a = ofNat b ↔ a = b := by
  constructor
  · intro h
    have := congrArg Fr.val h
    rwa [val_ofNat_of_lt ha, val_ofNat_of_lt hb] at this
  · intro h; rw [h]

/-- A nonnegative integer literal is the field element of that number. -/
theorem ofInt_natCast (n : Nat) : ofInt (n : Int) = ofNat n := rfl

/-- Field addition of two numbers is the field image of their sum. -/
theorem ofNat_add (a b : Nat) : ofNat a + ofNat b = ofNat (a + b) := by
  apply ext
  show (a % modulus + b % modulus) % modulus = (a + b) % modulus
  rw [← Nat.add_mod]

/-- Field multiplication of two numbers is the field image of their product. -/
theorem ofNat_mul (a b : Nat) : ofNat a * ofNat b = ofNat (a * b) := by
  apply ext
  show (a % modulus * (b % modulus)) % modulus = (a * b) % modulus
  rw [← Nat.mul_mod]

/-- Below the modulus, `a + -b` is the natural difference when `b ≤ a`. -/
theorem ofNat_add_neg {a b : Nat} (hba : b ≤ a) (ha : a < modulus) :
    ofNat a + -ofNat b = ofNat (a - b) := by
  apply ext
  have hb : b < modulus := Nat.lt_of_le_of_lt hba ha
  show (a % modulus + (modulus - b % modulus) % modulus) % modulus = (a - b) % modulus
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  by_cases h0 : b = 0
  · subst h0; simp [Nat.mod_self]
  · rw [Nat.mod_eq_of_lt (show modulus - b < modulus by omega)]
    have : a + (modulus - b) = (a - b) + modulus := by omega
    rw [this, Nat.add_mod_right]

/-- The value of `ofBool b`: 1 or 0. -/
theorem val_ofBool (b : Bool) : (ofBool b).val = if b then 1 else 0 := by
  cases b <;> rfl

/-- `ofBool` is injective. -/
theorem ofBool_inj {a b : Bool} : ofBool a = ofBool b ↔ a = b := by
  cases a <;> cases b <;> decide

/-- A field element is zero exactly when its value is 0. -/
theorem eq_zero_iff (x : Fr) : x = 0 ↔ x.val = 0 :=
  ⟨fun h => h ▸ val_zero, fun h => ext (h.trans val_zero.symm)⟩

/-- A field element is one exactly when its value is 1. -/
theorem eq_one_iff (x : Fr) : x = 1 ↔ x.val = 1 :=
  ⟨fun h => h ▸ val_one, fun h => ext (h.trans val_one.symm)⟩

/-- Zero is the image of the number 0. -/
theorem zero_eq_ofNat : (0 : Fr) = ofNat 0 := rfl

/-- One is the image of the number 1. -/
theorem one_eq_ofNat : (1 : Fr) = ofNat 1 := rfl

end Damp.Fr
