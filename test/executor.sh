#!/usr/bin/env bash
# Conformance of the JavaScript executor (executor/src/executor.mjs) to its
# definition, `Damp.Exec.run` in Damp/Executor.lean. See docs/executor.md.
#
# 1. `damp-executor-test export` (Test/Executor.lean) writes contract.json for
#    every example contract (optimized, as the build writes it) and for a
#    synthetic contract of raw IR, and the synthetic calls, into $DAMP_EXEC_OUT
#    (default build/executor).
# 2. executor/test/conformance.mjs runs every call of the executor tests' call
#    table and every synthetic call through the JS executor with its trace hook
#    on, and writes traces.json (with the field elements of each completed
#    call's proof preimage, as the runtime serializes it).
# 3. `damp-executor-test check` replays each call through the Lean definition
#    with scripted oracles: one ok/FAIL line per call, then a summary. Exits
#    non-zero on any disagreement.
#
# Needs nothing from the Compact toolchain beyond the runtime in executor/node_modules.
set -euo pipefail
cd "$(dirname "$0")/.."

out="${DAMP_EXEC_OUT:-build/executor}"
lake build damp-executor-test >/dev/null
rm -rf "$out"; mkdir -p "$out"
.lake/build/bin/damp-executor-test export "$out" >/dev/null
(cd executor && node test/conformance.mjs "../$out" >/dev/null)
.lake/build/bin/damp-executor-test check "$out"
