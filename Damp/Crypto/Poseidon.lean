/-
Poseidon over the BLS12-381 scalar field, as Midnight computes it off-circuit,
and the two primitives built on it: `transient_hash` and `transient_commit`.

Sources (read, then checked by `test/semantics.sh` against the runtime):
- `midnight-circuits` 7.3.0, `src/hash/poseidon/constants/mod.rs`: width 3,
  rate 2, 8 full rounds, 60 partial rounds; `constants/blstrs.rs`: the round
  constants and MDS matrix (copied mechanically into `PoseidonConstants.lean`).
- `src/hash/poseidon/poseidon_cpu.rs`:
  * the permutation adds `ROUND_CONSTANTS[0]`, then runs rounds `r = 0..67`;
    each applies the S-box `x ↦ x^5` (to every cell in rounds 0–3 and 64–67,
    to the last cell, index 2, in rounds 4–63) and then
    `state ← MDS · state + ROUND_CONSTANTS[r+1]` (zero after the last round).
    The CPU code batches partial rounds ("round skips"); it says this computes
    the same permutation, and we implement the plain one.
  * the sponge for a fixed-length input of length `n` starts from
    `[0, 0, n]`, adds the input two elements at a time into cells 0 and 1
    (a final odd element into cell 0 alone), permutes after each chunk, and
    returns cell 0. There is no padding; an empty input is never permuted.
- `midnight-transient-crypto` 3.0.1, `src/hash.rs`:
  `transient_hash(xs) = PoseidonChip::hash(xs)`, and
  `transient_commit(value, opening) = transient_hash(opening :: field_repr(value))`;
  for a slice of field elements `field_repr` is the elements themselves.
-/
import Damp.Field
import Damp.Crypto.PoseidonConstants

namespace Damp.Crypto.Poseidon
open Damp

def roundConstants : Array Fr := (roundConstantsRaw.map Fr.ofNat).toArray
def mdsArr : Array Fr := (mdsRaw.map Fr.ofNat).toArray

def nbFullRounds : Nat := 8
def nbPartialRounds : Nat := 60
def nbRounds : Nat := nbFullRounds + nbPartialRounds

/-- The permutation state: three cells. -/
structure State where
  c0 : Fr
  c1 : Fr
  c2 : Fr
  deriving DecidableEq, Repr

/-- `ROUND_CONSTANTS[r]`, or zeros past the last round. -/
def rc (r : Nat) : State :=
  if r < nbRounds then
    ⟨roundConstants.getD (3 * r) 0, roundConstants.getD (3 * r + 1) 0, roundConstants.getD (3 * r + 2) 0⟩
  else ⟨0, 0, 0⟩

def mds (i j : Nat) : Fr := mdsArr.getD (3 * i + j) 0

def pow5 (x : Fr) : Fr := let x2 := x * x; x2 * x2 * x

/-- `linear_layer`: `MDS · s + k`. -/
def linear (s k : State) : State :=
  let row (i : Nat) (ki : Fr) := ki + mds i 0 * s.c0 + mds i 1 * s.c1 + mds i 2 * s.c2
  ⟨row 0 k.c0, row 1 k.c1, row 2 k.c2⟩

def isFull (r : Nat) : Bool := r < nbFullRounds / 2 || nbFullRounds / 2 + nbPartialRounds ≤ r

/-- Round `r` (shifted form: the constants added are those of round `r+1`). -/
def round (s : State) (r : Nat) : State :=
  let s := if isFull r then ⟨pow5 s.c0, pow5 s.c1, pow5 s.c2⟩ else ⟨s.c0, s.c1, pow5 s.c2⟩
  linear s (rc (r + 1))

def permute (s : State) : State :=
  let k := rc 0
  (List.range nbRounds).foldl round ⟨s.c0 + k.c0, s.c1 + k.c1, s.c2 + k.c2⟩

/-- Absorb two elements at a time, permuting after each chunk. -/
def absorb : List Fr → State → State
  | [], s => s
  | [a], s => permute ⟨s.c0 + a, s.c1, s.c2⟩
  | a :: b :: rest, s => absorb rest (permute ⟨s.c0 + a, s.c1 + b, s.c2⟩)

/-- `PoseidonChip::hash`, fixed-length sponge with the length in the capacity cell. -/
def hash (xs : List Fr) : Fr := (absorb xs ⟨0, 0, Fr.ofNat xs.length⟩).c0

end Damp.Crypto.Poseidon

namespace Damp.Crypto
open Damp

/-- `transient_hash`. -/
def transientHash (xs : List Fr) : Fr := Poseidon.hash xs

/-- `transient_commit(values, opening)`: the opening is hashed first. -/
def transientCommit (xs : List Fr) (opening : Fr) : Fr := Poseidon.hash (opening :: xs)

end Damp.Crypto
