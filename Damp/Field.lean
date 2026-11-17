/-
The native field of Midnight circuits: the scalar field of BLS12-381.

Core Lean only. `Nat` is arbitrary precision, so this is executable as is.
-/
namespace Damp

/-- Order of the BLS12-381 scalar field. -/
def Fr.modulus : Nat :=
  0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

theorem Fr.modulus_pos : 0 < Fr.modulus := by decide

/-- An element of the BLS12-381 scalar field, in canonical form. -/
structure Fr where
  val : Nat
  isLt : val < Fr.modulus

namespace Fr

theorem ext {a b : Fr} (h : a.val = b.val) : a = b := by
  cases a; cases b; cases h; rfl

instance : DecidableEq Fr := fun a b =>
  if h : a.val = b.val then isTrue (ext h) else isFalse (fun e => h (e ▸ rfl))

def ofNat (n : Nat) : Fr := ⟨n % modulus, Nat.mod_lt _ modulus_pos⟩

instance : OfNat Fr n := ⟨ofNat n⟩
instance : Inhabited Fr := ⟨0⟩
instance : Repr Fr := ⟨fun a _ => repr a.val⟩
instance : ToString Fr := ⟨fun a => toString a.val⟩

def add (a b : Fr) : Fr := ofNat (a.val + b.val)
def mul (a b : Fr) : Fr := ofNat (a.val * b.val)
def neg (a : Fr) : Fr := ofNat (modulus - a.val)
def sub (a b : Fr) : Fr := add a (neg b)

instance : Add Fr := ⟨add⟩
instance : Mul Fr := ⟨mul⟩
instance : Neg Fr := ⟨neg⟩
instance : Sub Fr := ⟨sub⟩

/-- Signed integers map to the field the way ZKIR immediates do: `-n` is the negation of `n`. -/
def ofInt : Int → Fr
  | .ofNat n => ofNat n
  | .negSucc n => neg (ofNat (n + 1))

def ofBool (b : Bool) : Fr := if b then 1 else 0

end Fr
end Damp

/-! ## Algebra

The few identities the optimizer relies on, proved from the definition. -/
namespace Damp.Fr

theorem ofNat_val (a : Fr) : ofNat a.val = a := ext (Nat.mod_eq_of_lt a.isLt)

theorem val_zero : (0 : Fr).val = 0 := Nat.zero_mod _
theorem val_one : (1 : Fr).val = 1 := Nat.mod_eq_of_lt (by decide)

theorem ofInt_zero : ofInt 0 = 0 := rfl
theorem ofInt_one : ofInt 1 = 1 := rfl
theorem ofInt_ofNat_val (a : Fr) : ofInt (Int.ofNat a.val) = a := ofNat_val a

theorem zero_ne_one : (0 : Fr) ≠ 1 := by decide

theorem add_zero (a : Fr) : a + 0 = a := by
  show ofNat (a.val + (0 : Fr).val) = a
  rw [val_zero, Nat.add_zero, ofNat_val]

theorem zero_add (a : Fr) : 0 + a = a := by
  show ofNat ((0 : Fr).val + a.val) = a
  rw [val_zero, Nat.zero_add, ofNat_val]

theorem mul_one (a : Fr) : a * 1 = a := by
  show ofNat (a.val * (1 : Fr).val) = a
  rw [val_one, Nat.mul_one, ofNat_val]

theorem one_mul (a : Fr) : 1 * a = a := by
  show ofNat ((1 : Fr).val * a.val) = a
  rw [val_one, Nat.one_mul, ofNat_val]

theorem mul_zero (a : Fr) : a * 0 = 0 := by
  show ofNat (a.val * (0 : Fr).val) = 0
  rw [val_zero, Nat.mul_zero]; rfl

theorem zero_mul (a : Fr) : 0 * a = 0 := by
  show ofNat ((0 : Fr).val * a.val) = 0
  rw [val_zero, Nat.zero_mul]; rfl

theorem neg_neg (a : Fr) : - - a = a := by
  apply ext
  show (modulus - (modulus - a.val) % modulus) % modulus = a.val
  have h := a.isLt
  by_cases h0 : a.val = 0
  · rw [h0, Nat.sub_zero, Nat.mod_self, Nat.sub_zero, Nat.mod_self]
  · have h1 : (modulus - a.val) % modulus = modulus - a.val := Nat.mod_eq_of_lt (by omega)
    have h2 : modulus - (modulus - a.val) = a.val := by omega
    rw [h1, h2]
    exact Nat.mod_eq_of_lt h

end Damp.Fr
