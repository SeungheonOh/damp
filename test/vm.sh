#!/usr/bin/env bash
# Differential test of Damp/Ledger/Vm.lean (the model of Midnight's on-chain VM)
# and Damp/Ledger/Query.lean against the real VM. See docs/ledger-model.md.
#
# 1. Writes every example contract's contract.json (lake exe damp-examples)
#    into $DAMP_VM_OUT/lean (default build/vm-ledger).
# 2. Runs calls of every example through the executor, capturing every program
#    sent to the ledger with the state it ran on; derives failing variants; runs
#    all of them through the real VM (runProgram and QueryContext.query) and
#    writes vectors.json (executor/test/vm-vectors.mjs).
# 3. Runs the Lean model on every vector and compares (lake exe damp-vm-test).
#    Exits non-zero on any disagreement.
#
# VM_REUSE=1 skips step 1 when the contract.json files already exist.
set -euo pipefail
cd "$(dirname "$0")/.."

out="${DAMP_VM_OUT:-build/vm-ledger}"

if [[ "${VM_REUSE:-0}" != 1 || ! -d "$out/lean" ]]; then
  rm -rf "$out/lean"
  lake exe damp-examples "$out/lean" >"$out.examples.log" 2>&1 || { echo "damp-examples failed (see $out.examples.log)" >&2; exit 1; }
fi

lake build damp-vm-test >/dev/null
mkdir -p "$out/vectors"
(cd executor && node test/vm-vectors.mjs "../$out/lean" "../$out/vectors")

.lake/build/bin/damp-vm-test "$out/vectors/vectors.json"
