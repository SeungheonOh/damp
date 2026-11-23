#!/usr/bin/env bash
# What a witness can touch, established on the runtime (docs/ledger-model.md, "What a witness can
# touch"; Damp/Executor/Witnesses.lean, `WitnessesOK`).
#
# 1. Builds the contract `witness_effects` (below) at --O2.
# 2. Runs executor/test/witness-effects.mjs: every query of the call is logged with the whole VM
#    stack before and after (call context slot by slot, effects, contract state), and, for each
#    witness the contract calls between two ledger statements, the difference between what the
#    first query left and what the second starts from is the witness's effect on the ledger state.
#    It checks the footprint of each class: `createZswapOutput` changes call-context slot 1 only
#    (and inserts its commitment at the Zswap local state's current index); `createZswapInput`
#    and `ownPublicKey` change nothing in the ledger state; a user's witness sees the contract
#    state as the ledger statements before it left it, and cannot change it. Cross-contract calls:
#    test/calls-isolation.sh.
#
# WE_OUT overrides the output directory (default build/witness-effects).
set -euo pipefail
cd "$(dirname "$0")/.."
out="${WE_OUT:-build/witness-effects}"
rm -rf "$out"; mkdir -p "$out"

lake build Bench >/dev/null
cat > "$out/Effects.lean" <<'LEAN'
import Bench
open Damp

namespace WitnessEffects
abbrev SR := Either ZswapCoinPublicKey ContractAddress

ledger
  count : Cell Field

/-- A user's witness: answers what it sees of `count`. -/
witness peek : Field
/-- A user's witness that tries to change the ledger view it is given. -/
witness tamper : Field

/-- `createZswapOutput` between two writes. -/
circuit outC (coin : ShieldedCoinInfo) (pk : ZswapCoinPublicKey) : Field := do
  count.write 1
  createZswapOutput (disclose coin) (left (disclose pk) : SR)
  count.write 2
  return 0

/-- `createZswapInput` between two writes. -/
circuit inC (coin : QualifiedShieldedCoinInfo) : Field := do
  count.write 1
  createZswapInput (disclose coin)
  count.write 2
  return 0

/-- `ownPublicKey` between two writes. -/
circuit pkC : ZswapCoinPublicKey := do
  count.write 1
  const k ← ownPublicKey
  count.write 2
  return k

/-- A user's witness between two writes: it sees the first. -/
circuit userC (v : Field) : Field := do
  count.write (disclose v)
  const x ← peek
  count.write 6
  return disclose x

/-- A user's witness that tries to write the ledger view. -/
circuit tamperC : Field := do
  count.write 5
  const x ← tamper
  const y ← count.read
  return disclose (x + y)

contract witness_effects
end WitnessEffects

def main (args : List String) : IO UInt32 := do
  let out := System.FilePath.mk (args.headD "build")
  let c := WitnessEffects.contract
  let m := c.optimize .full false
  let srcs ← IO.ofExcept m.emitAll
  m.writeFiles (out / c.name) srcs
  return 0
LEAN
lake env lean --run "$out/Effects.lean" "$out" >/dev/null
ln -sfn "$(pwd)/executor/node_modules" "$out/node_modules"
(cd executor && node test/witness-effects.mjs "../$out")
