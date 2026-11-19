/-
`persistent_hash` as ZKIR's reference evaluator computes it, and the concrete
`Zkir.Prims` that `Damp/Zkir/Semantics.lean` takes as a parameter.

`persistent_hash alignment inputs` in `IrSource::preprocess`
(midnight-zkir 3.2.1, `zkir/src/ir_vm.rs`) is

    let value = alignment.parse_field_repr(&inputs)?;   // else "Inputs did not match alignment"
    let mut repr = Vec::new();
    ValueReprAlignedValue(value).binary_repr(&mut repr);
    Sha256::digest(&repr)

Sources for the two middle steps (`midnight-transient-crypto` 3.0.1,
`src/fab.rs` and `src/repr.rs`):

- `Alignment::parse_field_repr` parses the atoms in order from the front of the
  inputs and returns the value **without checking that every input was used**:
  surplus inputs are ignored.
- `AlignmentAtom::Compress` cannot be parsed: `None`.
- `AlignmentAtom::Field` takes one element. Its binary form is the element's 32
  little-endian bytes (`value_atom_as_field` then `Fr::binary_repr`).
- `AlignmentAtom::Bytes { length: n }` is `bytes_from_field_repr(repr, n)`:
  with `stray = n % 31` and `chunks = n / 31` it needs at least
  `chunks + (stray ≠ 0)` elements, else `None`. If `stray > 0`, the first
  element must be below `2^(8·stray)` and gives the **last** `stray` bytes,
  little-endian. The next `chunks` elements must each be below `2^248`; element
  `chunks-1-i` gives bytes `31·i .. 31·i+30`, little-endian. So the most
  significant chunk comes first. Its binary form is the `n` bytes.

`test/semantics.sh` checks this against the real evaluator (synthetic
circuits run through `zkir-v3`'s `check`) and against the runtime's
`persistentHash`.
-/
import Damp.Zkir.Semantics
import Damp.Crypto.Sha256
import Damp.Crypto.Poseidon

namespace Damp.Crypto
open Damp Damp.Zkir

/-- The `k` low bytes of `x`, least significant first. -/
def leBytes (k x : Nat) : List Nat := (List.range k).map fun i => x / 256 ^ i % 256

/-- `AlignmentAtom::Bytes{n}` parsed from field elements: the `n` bytes and the rest. -/
def parseBytesAtom (n : Nat) (repr : List Fr) : Option (List Nat × List Fr) :=
  let stray := n % 31
  let chunks := n / 31
  let expected := chunks + (if stray ≠ 0 then 1 else 0)
  if repr.length < expected then none else
  let (strayBytes, repr) :=
    if stray = 0 then (some [], repr)
    else match repr with
      | f :: rest => (if f.val < 2 ^ (8 * stray) then some (leBytes stray f.val) else none, rest)
      | [] => (none, [])
  let full := repr.take chunks
  if full.all (·.val < 2 ^ 248) then
    strayBytes.map fun sb => ((full.reverse.flatMap fun f => leBytes 31 f.val) ++ sb, repr.drop chunks)
  else none

/-- One atom: its binary representation and the unread elements. -/
def parseAtom : AlignAtom → List Fr → Option (List Nat × List Fr)
  | .compress, _ => none
  | .field, [] => none
  | .field, f :: rest => some (leBytes 32 f.val, rest)
  | .bytes n, repr => parseBytesAtom n repr

/-- `ValueReprAlignedValue(alignment.parse_field_repr(xs)?).binary_repr()`.
    Surplus elements are ignored, as upstream. -/
def binaryRepr : Alignment → List Fr → Option (List Nat)
  | [], _ => some []
  | a :: al, xs => do
      let (bs, rest) ← parseAtom a xs
      let more ← binaryRepr al rest
      pure (bs ++ more)

/-- `persistent_hash` on field elements read under an alignment. -/
def persistentHash (al : Alignment) (xs : List Fr) : Option (List Nat) :=
  (binaryRepr al xs).map Sha256.hashNat

/-- Midnight's cryptography, as the ZKIR reference evaluator uses it. -/
def prims : Zkir.Prims where
  transientHash := transientHash
  persistentHash := persistentHash
  transientCommit := transientCommit

end Damp.Crypto
