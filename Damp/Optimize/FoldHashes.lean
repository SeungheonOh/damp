/-
Folding hashes and `divmod` whose inputs are constants.

`Expr.foldK p hashes` rewrites an expression bottom up and replaces

* `divmod quot bits (const k)` with `bits ≤ 248` by the constant it evaluates
  to (the quotient or remainder of `k`'s canonical value by `2 ^ bits`). With
  `bits > 248` the `divmod` fails and is left alone. This rule does not depend
  on the hash functions.
* when `hashes` is set, `hash [const k₁, …]` by the constant
  `p.transientHash [k₁, …]`, and `phash high align [const k₁, …]` by the half of
  `p.persistentHash align [k₁, …]` it selects (the top byte if `high`,
  otherwise the low 31 bytes, as `Expr.eval` takes them through
  `bytesToNatives`). A persistent hash whose inputs do not fit the alignment
  fails, and is left alone.

Everything else is rebuilt as it was, so an expression with nothing to fold
comes out unchanged.

Two passes use it:

* `Circuit.foldDivmod` folds only `divmod`. It preserves `Expr.eval` for every
  `Prims`, so it is an ordinary sound pass (`Circuit.foldDivmod_sound`).
* `Circuit.foldHashes p` also folds hashes, computed with `p`. It preserves
  `Expr.eval` at that `p` only: what the circuit computes with other hash
  functions changes. So it is sound *relative to `p`*
  (`Pass.SoundFor p (Circuit.foldHashes p)`, `Circuit.foldHashes_soundFor` in
  `Damp/Proofs/Optimize/FoldHashes.lean`). The pipeline instantiates it with
  `Damp.Crypto.prims`, the Lean implementations of Midnight's Poseidon and
  SHA-256 (`--O3` only).
-/
import Damp.Optimize.Algebra

namespace Damp.IR
open Damp.Zkir (Prims bytesToNatives)

/-- The constants of a list of constant expressions, if they all are. -/
def constsOf : List Expr → Option (List Int)
  | [] => some []
  | .const k :: xs => (constsOf xs).map (k :: ·)
  | _ :: _ => none

/-- `divmod quot bits` of a constant, if it can be computed. -/
def foldDivmodConst (quot : Bool) (bits : Nat) : Expr → Expr
  | .const k =>
      if bits ≤ 248 then
        canon (Fr.ofNat (if quot then (Fr.ofInt k).val / 2 ^ bits else (Fr.ofInt k).val % 2 ^ bits))
      else .divmod quot bits (.const k)
  | a => .divmod quot bits a

/-- `hash xs` of constants, computed with `p`. -/
def foldHashConst (p : Prims) (xs : List Expr) : Expr :=
  match constsOf xs with
  | some ks => canon (p.transientHash (ks.map Fr.ofInt))
  | none => .hash xs

/-- `phash high align xs` of constants, computed with `p`, when it has a value. -/
def foldPHashConst (p : Prims) (high : Bool) (align : List Zkir.AlignAtom) (xs : List Expr) : Expr :=
  match constsOf xs with
  | some ks =>
      match p.persistentHash align (ks.map Fr.ofInt) with
      | some digest =>
          match bytesToNatives digest with
          | [lo, hi] => canon (if high then hi else lo)
          | _ => .phash high align xs
      | none => .phash high align xs
  | none => .phash high align xs

mutual
/-- Fold `divmod` (and, with `hashes`, hashes computed with `p`) of constants, bottom up. -/
def Expr.foldK (p : Prims) (hashes : Bool) : Expr → Expr
  | .add a b => .add (a.foldK p hashes) (b.foldK p hashes)
  | .mul a b => .mul (a.foldK p hashes) (b.foldK p hashes)
  | .neg a => .neg (a.foldK p hashes)
  | .lt bits a b => .lt bits (a.foldK p hashes) (b.foldK p hashes)
  | .eq a b => .eq (a.foldK p hashes) (b.foldK p hashes)
  | .select c a b => .select (c.foldK p hashes) (a.foldK p hashes) (b.foldK p hashes)
  | .divmod quot bits a => foldDivmodConst quot bits (a.foldK p hashes)
  | .hash xs =>
      let xs' := Expr.foldKList p hashes xs
      if hashes then foldHashConst p xs' else .hash xs'
  | .phash high align xs =>
      let xs' := Expr.foldKList p hashes xs
      if hashes then foldPHashConst p high align xs' else .phash high align xs'
  | .var v => .var v
  | .const c => .const c
  | .invalid msg => .invalid msg
  | .disclose e => .disclose (e.foldK p hashes)
def Expr.foldKList (p : Prims) (hashes : Bool) : List Expr → List Expr
  | [] => []
  | x :: xs => x.foldK p hashes :: Expr.foldKList p hashes xs
end

/-- Hash functions that are never called: `Circuit.foldDivmod` folds no hash. -/
def noPrims : Prims where
  transientHash _ := 0
  persistentHash _ _ := Option.none
  transientCommit _ _ := 0

/-- Fold `divmod` of constants. Sound for every `Prims`. -/
def Circuit.foldDivmod : Circuit → Circuit := Circuit.mapExprs (Expr.foldK noPrims false)

/-- Fold `divmod` and hashes of constants, the hashes computed with `p`. Sound
    relative to `p` only. -/
def Circuit.foldHashes (p : Prims) : Circuit → Circuit := Circuit.mapExprs (Expr.foldK p true)

end Damp.IR
