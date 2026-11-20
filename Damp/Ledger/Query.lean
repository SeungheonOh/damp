/-
Running a request against a contract, and the ledger oracle it induces.

`QueryContext::query` (`onchain-runtime/src/context.rs`, tag
`onchain-runtime-4.0.2`) runs a program on the stack
`[context, effects, state]` (bottom first): the call context and the
effects weak, the contract's state strong. The program must leave exactly
three values; the top one, strong, is the new state, and the one below is
decoded back into the effects.

`ledgerOracle` is what Damp's executor (`Exec.Oracles.ledger` in
`Damp/Executor/Spec.lean`) is given: the field elements the `popeq`s read and
the ledger afterwards. It mirrors `oracles(...).ledger` in
`executor/src/executor.mjs`: instructions converted (`Op.toR`), run with
`QueryContext.query`, and each `popeq`'s value read back under the alignment
the instruction states.

The effects are decoded into typed Rust values (`TryFrom<VmValue> for
Effects`) and re-encoded, for all nine slots (`decodeEffects`): the hash sets
(0 to 2), the claimed contract calls (3), the mint maps (4, 5), and the
unshielded inputs, outputs and spends (6 to 8), keyed by `TokenType` and
`(TokenType, PublicAddress)`. A key or value that is not a well-formed value
of its type makes the query fail, as in the runtime. See
`docs/ledger-model.md`.
-/
import Damp.Ledger.Vm
import Damp.Executor.Spec

namespace Damp.Ledger
open Damp.Impact

/-- What `QueryContext` holds that the VM sees: the call context, the effects
    so far, and the contract's state. -/
structure LedgerState where
  context : SV
  effects : SV
  state : SV
  deriving Inhabited

/-- The VM stack `QueryContext::to_vm_stack` builds. -/
def LedgerState.vm (q : LedgerState) : VmState :=
  VmState.init [(q.context, false), (q.effects, false), (q.state, true)]

/-! ### Typed decoding of the effects' keys

Each decoder is a `TryFrom<&ValueSlice>` of the runtime on the key's atoms
(its alignment is not consulted); on success the key is re-encoded with the
type's own alignment (`From<T> for AlignedValue`). Every decoder below
accepts atoms only when re-encoding gives them back unchanged (the atoms are
normalised), so only the alignment changes. -/

/-- `TryFrom<&ValueAtom> for HashOutput` (and for `ContractAddress`,
    `UserAddress`, ...): at most 32 bytes. -/
def hashOk (x : Nat) : Bool := x < 2 ^ 256

/-- `TokenType` (`coin-structure/src/coin.rs`): three atoms, a `u8` tag then
    two hashes. Tag 0 (shielded): the first hash empty; tag 1 (unshielded): the
    second empty; tag 2 (dust): both empty. Compact's `TokenType`, an
    `Either<Bytes<32>, Bytes<32>>` with `is_left` set for an unshielded token,
    is exactly this. -/
def tokenTypeOk : List Nat → Bool
  | [t, a, b] => (t == 0 && a == 0 && hashOk b) || (t == 1 && b == 0 && hashOk a) || (t == 2 && a == 0 && b == 0)
  | _ => false

/-- `PublicAddress`: three atoms, a `bool` then two hashes; `true` (a contract)
    needs the second hash empty, `false` (a user) the first. Compact's
    `Either<ContractAddress, UserAddress>`. -/
def publicAddressOk : List Nat → Bool
  | [b, a, u] => (b == 1 && u == 0 && hashOk a) || (b == 0 && a == 0 && hashOk u)
  | _ => false

/-- `ClaimedContractCallsValue`: four atoms, a `u64`, a `ContractAddress`, a
    `HashOutput` and an `Fr` (below the field's modulus). -/
def contractCallOk : List Nat → Bool
  | [p, a, h, f] => p < 2 ^ 64 && hashOk a && hashOk h && decide (f < Fr.modulus)
  | _ => false

/-- `ClaimedUnshieldedSpendsKey`: six atoms, a `TokenType` then a `PublicAddress`. -/
def spendKeyOk (xs : List Nat) : Bool := xs.length == 6 && tokenTypeOk (xs.take 3) && publicAddressOk (xs.drop 3)

def alignTokenType : List Zkir.AlignAtom := [.bytes 1, .bytes 32, .bytes 32]
def alignPublicAddress : List Zkir.AlignAtom := [.bytes 1, .bytes 32, .bytes 32]
def alignContractCall : List Zkir.AlignAtom := [.bytes 8, .bytes 32, .bytes 32, .field]

/-- The key of an effects map in slot `slot`, decoded and re-encoded. -/
def effectKey (slot : Nat) (k : AV) : Option AV :=
  if slot ≤ 2 ∨ slot = 4 ∨ slot = 5 then do
    let h ← k.toHash
    pure (AV.ofHash h)
  else if slot = 3 then
    if contractCallOk k.atoms then some ⟨alignContractCall, k.atoms⟩ else none
  else if slot = 6 ∨ slot = 7 then
    if tokenTypeOk k.atoms then some ⟨alignTokenType, k.atoms⟩ else none
  else if slot = 8 then
    if spendKeyOk k.atoms then some ⟨alignTokenType ++ alignPublicAddress, k.atoms⟩ else none
  else none

/-- `TryFrom<&ValueSlice> for u128`: one atom of at most 16 bytes. -/
def AV.toU128 (v : AV) : Option Nat :=
  match v.atoms with
  | [x] => if x < 2 ^ 128 then some x else none
  | _ => none

/-- The value of an effects map entry in slot `slot`, decoded and re-encoded:
    `()` for the sets (slots 0 to 3), stored as null; `u64` for the mints
    (slots 4, 5) and `u128` for the unshielded amounts (slots 6 to 8), stored
    as cells. A null value decodes as the default (`()`, 0). -/
def effectValue (slot : Nat) (v : SV) : Option SV :=
  if slot ≤ 3 then
    match v with
    | .null => some .null
    | .cell c => if c.atoms = [] then some .null else none
    | _ => none
  else if slot = 4 ∨ slot = 5 then do
    let x ← match v with
      | .null => some 0
      | .cell c => c.toU64
      | _ => none
    pure (.cell (AV.ofU64 x))
  else do
    let x ← match v with
      | .null => some 0
      | .cell c => c.toU128
      | _ => none
    pure (.cell ⟨[.bytes 16], [x]⟩)

/-- One entry of an effects map, through `TryFrom<VmValue> for Effects` and
    back (`From<&Effects> for VmValue`, `onchain-runtime/src/context.rs`):
    `map_from` decodes the key and the value with the slot's types. -/
def effectEntry (slot : Nat) (k : AV) (v : SV) : Option (AV × SV) := do
  let v' ← effectValue slot v
  let k' ← effectKey slot k
  pure (k', v')

/-- Normalise a map's entries: later entries win when two keys decode alike. -/
def effectMap (slot : Nat) : List (AV × SV) → Option (List (AV × SV))
  | [] => some []
  | (k, v) :: rest => do
      let rest ← effectMap slot rest
      let (k', v') ← effectEntry slot k v
      pure (if (assocGet k' rest).isSome then rest else assocSet k' v' rest)

/-- The effects after a query: `TryFrom<VmValue> for Effects` (nine maps), then
    re-encoded, as far as `effectEntry` models it. -/
def decodeEffects : SV → Option SV
  | .array es =>
      if es.length = 9 then do
        let es' ← (es.zipIdx).mapM fun (e, i) => match e with
          | .map m => (effectMap i m).map SV.map
          | _ => none
        pure (.array es')
      else none
  | _ => none

/-- `QueryContext::query`, gathering: the values read, and the context after. -/
def query (H : Hooks) (rops : List ROp) (q : LedgerState) : Option (List AV × LedgerState) := do
  let s ← runR H rops q.vm
  match s.stack with
  | [st, eff, _] =>
      if st.strong then do
        let effects ← decodeEffects eff.val
        pure (s.reads, { q with state := st.val, effects })
      else none
  | _ => none

/-- The alignments of a program's `popeq`s, in program order. -/
def popeqAligns : List (Op Fr) → List (List Zkir.AlignAtom)
  | [] => []
  | .popeq _ align _ :: ops => align :: popeqAligns ops
  | _ :: ops => popeqAligns ops

/-- Pair each `popeq` with the value it read and read it back as field
    elements. The runtime fills the `popeq`s of the program in order with the
    read events; a `popeq` left without one (skipped by a branch) makes the
    executor fail. -/
def readBack : List (List Zkir.AlignAtom) → List AV → Option (List Fr)
  | [], [] => some []
  | a :: as, v :: vs => do
      let f ← fieldsOf a v.atoms
      let rest ← readBack as vs
      pure (f ++ rest)
  | _, _ => none

/-- The ledger oracle the VM model induces: Damp's executor's `O.ledger`. -/
def ledgerOracle (H : Hooks) (ops : List (Op Fr)) (q : LedgerState) : Option (List Fr × LedgerState) := do
  let rops ← ops.mapM Op.toR
  let (reads, q') ← query H rops q
  let vals ← readBack (popeqAligns ops) reads
  pure (vals, q')

/-- Damp's executor run against this model of the ledger: `Exec.run p
    (oracles H w)` is a concrete instance of the executor's specification. -/
def oracles {ω : Type} (H : Hooks) (witness : String → List Fr → ω → Option (List Fr × ω)) :
    Exec.Oracles ω LedgerState where
  witness := witness
  ledger := ledgerOracle H

end Damp.Ledger
