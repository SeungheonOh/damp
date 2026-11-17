/-
The circuit IR: the single description of a circuit that the ZKIR emitter, the
reference semantics and the executor all read.

A circuit is a list of statements over field-valued variables. There is no
control flow: a conditional is a `select`, and an effect under a branch carries
the branch condition as its guard. A contract written with the `Contract`
interface *is* a value of this type, built by ordinary Lean evaluation, so a
theorem about `Circuit.run` of that value is a theorem about what is compiled.
-/
import Damp.Impact

namespace Damp.IR
open Damp.Zkir (AlignAtom)

abbrev Var := Nat

/-- Pure field-valued expressions. Booleans are the field elements 0 and 1. -/
inductive Expr where
  | var (v : Var)
  | const (c : Int)
  | add (a b : Expr)
  | mul (a b : Expr)
  | neg (a : Expr)
  /-- `a < b` as integers, both known to fit in `bits` bits. -/
  | lt (bits : Nat) (a b : Expr)
  | eq (a b : Expr)
  /-- `a` if `c` is 1, otherwise `b`. -/
  | select (c a b : Expr)
  /-- The transient (Poseidon) hash. -/
  | hash (xs : List Expr)
  /-- One half of the persistent (SHA-256) hash of a value with the given
      alignment: the top byte if `high`, otherwise the low 31 bytes. -/
  | phash (high : Bool) (align : List AlignAtom) (xs : List Expr)
  /-- The value of `a` divided by `2 ^ bits`: the quotient if `quot`, otherwise
      the remainder. Fails for `bits` above 248. -/
  | divmod (quot : Bool) (bits : Nat) (a : Expr)
  /-- Not a value: a mistake found while building, such as a literal that does
      not fit its type. A circuit containing one is rejected by the emitter. -/
  | invalid (msg : String)
  /-- `e`, marked as deliberately made public. Has the value of `e`; only the
      disclosure check looks at the marker. -/
  | disclose (e : Expr)
  deriving Inhabited, Repr

/-! ### Equality of expressions

Lean cannot derive a lawful `==` for a type that contains lists of itself, so
it is written out and proved here. The emitter's sharing of equal expressions
and two of the optimizer's rules rest on it. -/

mutual
def Expr.same : Expr → Expr → Bool
  | .var v, .var w => v == w
  | .const c, .const d => c == d
  | .add a b, .add c d => a.same c && b.same d
  | .mul a b, .mul c d => a.same c && b.same d
  | .neg a, .neg c => a.same c
  | .lt n a b, .lt m c d => n == m && a.same c && b.same d
  | .eq a b, .eq c d => a.same c && b.same d
  | .select c a b, .select c' a' b' => c.same c' && a.same a' && b.same b'
  | .hash xs, .hash ys => Expr.sameList xs ys
  | .phash h al xs, .phash h' al' ys => h == h' && al == al' && Expr.sameList xs ys
  | .divmod q n a, .divmod q' n' a' => q == q' && n == n' && a.same a'
  | .invalid m, .invalid m' => m == m'
  | .disclose a, .disclose c => a.same c
  | _, _ => false
def Expr.sameList : List Expr → List Expr → Bool
  | [], [] => true
  | x :: xs, y :: ys => x.same y && Expr.sameList xs ys
  | _, _ => false
end

mutual
theorem Expr.same_eq : ∀ a b : Expr, a.same b = true → a = b
  | .var _, b, h => by cases b <;> simp_all [Expr.same]
  | .const _, b, h => by cases b <;> simp_all [Expr.same]
  | .invalid _, b, h => by cases b <;> simp_all [Expr.same]
  | .add a1 a2, b, h => by
      cases b <;> simp [Expr.same] at h
      rw [Expr.same_eq _ _ h.1, Expr.same_eq _ _ h.2]
  | .mul a1 a2, b, h => by
      cases b <;> simp [Expr.same] at h
      rw [Expr.same_eq _ _ h.1, Expr.same_eq _ _ h.2]
  | .eq a1 a2, b, h => by
      cases b <;> simp [Expr.same] at h
      rw [Expr.same_eq _ _ h.1, Expr.same_eq _ _ h.2]
  | .lt _ a1 a2, b, h => by
      cases b <;> simp [Expr.same] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      rw [h1, Expr.same_eq _ _ h2, Expr.same_eq _ _ h3]
  | .select c1 a1 a2, b, h => by
      cases b <;> simp [Expr.same] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      rw [Expr.same_eq _ _ h1, Expr.same_eq _ _ h2, Expr.same_eq _ _ h3]
  | .neg a1, b, h => by
      cases b <;> simp [Expr.same] at h
      rw [Expr.same_eq _ _ h]
  | .disclose a1, b, h => by
      cases b <;> simp [Expr.same] at h
      rw [Expr.same_eq _ _ h]
  | .divmod _ _ a1, b, h => by
      cases b <;> simp [Expr.same] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      rw [h1, h2, Expr.same_eq _ _ h3]
  | .hash xs, b, h => by
      cases b <;> simp [Expr.same] at h
      rw [Expr.sameList_eq _ _ h]
  | .phash _ _ xs, b, h => by
      cases b <;> simp [Expr.same] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      rw [h1, h2, Expr.sameList_eq _ _ h3]
theorem Expr.sameList_eq : ∀ xs ys : List Expr, Expr.sameList xs ys = true → xs = ys
  | [], ys, h => by cases ys <;> simp_all [Expr.sameList]
  | x :: xs, ys, h => by
      cases ys <;> simp [Expr.sameList] at h
      rw [Expr.same_eq _ _ h.1, Expr.sameList_eq _ _ h.2]
end

mutual
theorem Expr.same_refl : ∀ a : Expr, a.same a = true
  | .var _ | .const _ | .invalid _ => by simp [Expr.same]
  | .add a b | .mul a b | .eq a b | .lt _ a b => by simp [Expr.same, Expr.same_refl a, Expr.same_refl b]
  | .select c a b => by simp [Expr.same, Expr.same_refl c, Expr.same_refl a, Expr.same_refl b]
  | .neg a | .disclose a | .divmod _ _ a => by simp [Expr.same, Expr.same_refl a]
  | .hash xs | .phash _ _ xs => by simp [Expr.same, Expr.sameList_refl xs]
theorem Expr.sameList_refl : ∀ xs : List Expr, Expr.sameList xs xs = true
  | [] => by simp [Expr.sameList]
  | x :: xs => by simp [Expr.sameList, Expr.same_refl x, Expr.sameList_refl xs]
end

instance : BEq Expr := ⟨Expr.same⟩

instance : LawfulBEq Expr where
  eq_of_beq := Expr.same_eq _ _
  rfl := Expr.same_refl _

/-- `select`, simplified the way Compact does when the condition is a negation. -/
def Expr.sel (c a b : Expr) : Expr :=
  match c with
  | .select s (.const 0) (.const 1) => .select s b a
  | c => .select c a b

mutual
/-- Variables an expression mentions. -/
def Expr.vars : Expr → List Var
  | .var v => [v]
  | .const _ | .invalid _ => []
  | .add a b | .mul a b | .lt _ a b | .eq a b => a.vars ++ b.vars
  | .neg a | .disclose a | .divmod _ _ a => a.vars
  | .select c a b => c.vars ++ a.vars ++ b.vars
  | .hash xs | .phash _ _ xs => Expr.varsList xs
def Expr.varsList : List Expr → List Var
  | [] => []
  | x :: xs => x.vars ++ Expr.varsList xs
end

/-- A range a value is constrained to. -/
inductive Range where
  | zero
  | bool
  | bits (n : Nat)
  /-- Strictly below `bound`; `bits` is the width used for the comparison. -/
  | below (bound : Nat) (bits : Nat)
  deriving Repr, BEq, Inhabited

/-- Interface types: what arguments, results, witness values and ledger cells are made of. -/
inductive Ty where
  | field
  | bool
  /-- Unsigned integer no greater than `max` (Compact's `Uint<0..max+1>`). -/
  | uint (max : Nat)
  /-- `n` bytes, held as 31-byte limbs, most significant limb first. -/
  | bytes (n : Nat)
  /-- An enumeration whose variants are numbered `0..max`. -/
  | enum (max : Nat)
  deriving Repr, BEq, Inhabited

def bitLen (n : Nat) : Nat := if n = 0 then 0 else Nat.log2 n + 1

/-- Number of 31-byte limbs holding `n` bytes. -/
def byteLimbs (n : Nat) : Nat := (n + 30) / 31

/-- The range checks Compact applies to a value of this type entering a
    circuit, one entry per field element the value occupies. -/
def Ty.ranges : Ty → List (Option Range)
  | .field => [none]
  | .bool => [some .bool]
  | .uint max | .enum max =>
      if max = 0 then [some .zero]
      else if max = 1 then [some .bool]
      else if max + 1 = 2 ^ bitLen max then [some (.bits (bitLen max))]
      else
        let n := bitLen (max + 1)
        [some (.below (max + 1) (n + n % 2))]
  | .bytes n =>
      let limbs := byteLimbs n
      -- The first limb holds whatever the others, 31 bytes each, leave over.
      (List.range limbs).map fun j =>
        some (.bits (if j = 0 then 8 * (n - 31 * (limbs - 1)) else 248))

/-- Number of field elements a value of this type occupies. -/
def Ty.width (t : Ty) : Nat := t.ranges.length

/-- How a value of this type is aligned in ledger cells and hashes. -/
def Ty.align : Ty → AlignAtom
  | .field => .field
  | .bool => .bytes 1
  | .uint max | .enum max => .bytes ((bitLen max + 7) / 8)
  | .bytes n => .bytes n

/-- The structure of a value at a circuit's boundary: how the executor maps it
    to and from the flat list of field elements the circuit works with. -/
inductive Shape where
  | prim (ty : Ty)
  | struct (name : String) (fieldNames : List String) (fields : List Shape)
  | tuple (elems : List Shape)
  | vector (n : Nat) (elem : Shape)
  deriving Inhabited

mutual
/-- The primitive values a value of this shape is made of, in order. -/
def Shape.tys : Shape → List Ty
  | .prim t => [t]
  | .struct _ _ fs => Shape.tysList fs
  | .tuple es => Shape.tysList es
  | .vector n e => (List.replicate n e.tys).flatten
def Shape.tysList : List Shape → List Ty
  | [] => []
  | s :: ss => s.tys ++ Shape.tysList ss
end

/-- Range checks for a value of this shape, one per field element. -/
def Shape.ranges (s : Shape) : List (Option Range) := s.tys.flatMap Ty.ranges

inductive Stmt where
  /-- Name the value of an expression. -/
  | bind (v : Var) (hint : String) (e : Expr)
  | assert (cond : Expr) (msg : String)
  | constrain (e : Expr) (r : Range)
  /-- Ask the private oracle. If the guard is 0 nothing is asked and the outputs are 0. -/
  | witness (guard : Expr) (name : String) (args : List Expr) (outs : List (Var × Option Range)) (shape : Shape)
  /-- Run Impact instructions against the public state. `reads` are the variables
      bound by the `popeq` results, in order. If the guard is 0 nothing runs and
      they are 0. -/
  | ledger (guard : Expr) (reads : List Var) (ops : List (Impact.Op Expr))
  deriving Inhabited

structure Input where
  name : String
  var : Var
  range : Option Range
  deriving Repr, Inhabited

structure Circuit where
  name : String
  /-- Arguments as the caller sees them. -/
  args : List (String × Shape)
  /-- The same arguments, flattened to circuit inputs. -/
  inputs : List Input
  body : Array Stmt
  result : Shape
  outputs : List Expr
  /-- Problems found while the circuit was being built. A circuit with any is not emitted. -/
  errors : List String := []
  deriving Inhabited

/-- Whether a call of this circuit must be proved. A circuit that never touches
    the ledger changes no public state; like Compact, we emit no ZKIR for it and
    it runs only in the executor. -/
def Circuit.needsProof (c : Circuit) : Bool :=
  c.body.any fun | .ledger .. => true | _ => false

end Damp.IR
