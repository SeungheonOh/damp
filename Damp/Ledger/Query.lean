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
Effects`) and re-encoded. The model does this for the hash sets and the mint
maps (slots 0 to 2, 4 and 5, `decodeEffects`); for the other four slots it
checks only that values are cells or null and keeps the entries as they are
(abstracted). See `docs/ledger-model.md`.
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

/-- One entry of an effects map, through `TryFrom<VmValue> for Effects` and
    back (`From<&Effects> for VmValue`, `onchain-runtime/src/context.rs`).
    Slots 0 to 2 are sets of hashes (`HashOutput` keys, `()` values, stored as
    null); slots 4 and 5 map hashes to `u64` (a null value decodes as 0). The
    other slots (claimed contract calls, unshielded inputs, outputs and
    spends, keyed by composite types) are kept as they are: their typed
    decoding is abstracted. -/
def effectEntry (slot : Nat) (k : AV) (v : SV) : Option (AV × SV) :=
  if slot ≤ 2 then do
    let h ← k.toHash
    match v with
    | .null => pure (AV.ofHash h, .null)
    | .cell c => if c.atoms = [] then pure (AV.ofHash h, .null) else none
    | _ => none
  else if slot = 4 ∨ slot = 5 then do
    let h ← k.toHash
    let x ← match v with
      | .null => some 0
      | .cell c => c.toU64
      | _ => none
    pure (AV.ofHash h, .cell (AV.ofU64 x))
  else
    match v with
    | .null | .cell _ => some (k, v)
    | _ => none

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
