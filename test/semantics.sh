#!/usr/bin/env bash
# Differential test of Damp/Zkir/Semantics.lean (with Damp/Crypto) against
# Midnight's real ZKIR evaluator. See docs/zkir-semantics.md.
#
# 1. Builds the example contracts and their circuits (test/oracle.sh) into
#    $DAMP_ORACLE (default build/oracle-vec).
# 2. Runs real calls through the executor, tampers with the proof data, runs
#    everything through zkir-v3's `check`, and writes test vectors
#    (executor/test/semantics-vectors.mjs) into $DAMP_SEM_OUT (default build/semantics).
# 3. Runs the Lean evaluator on every vector (lake exe damp-semantics-test):
#    one ok/FAIL line per check, then a summary. Exits non-zero on any FAIL.
#
# SEM_REUSE=1 skips step 1 when $DAMP_ORACLE already holds a build.
set -euo pipefail
cd "$(dirname "$0")/.."

oracle="${DAMP_ORACLE:-build/oracle-vec}"
out="${DAMP_SEM_OUT:-build/semantics}"

if [[ "${SEM_REUSE:-0}" != 1 || ! -d "$oracle/lean" ]]; then
  # oracle.sh starts by deleting its output directory, so build into a fresh
  # one and keep the previous build if this one cannot be made.
  if DAMP_OUT="$oracle.new" ./test/oracle.sh >"$out.oracle.log" 2>&1 || [[ -d "$oracle.new/lean" ]]; then
    rm -rf "$oracle"; mv "$oracle.new" "$oracle"
  elif [[ -d "$oracle/lean" ]]; then
    echo "warning: test/oracle.sh failed (see $out.oracle.log); using the previous build in $oracle" >&2
  else
    echo "test/oracle.sh failed (see $out.oracle.log)" >&2; exit 1
  fi
fi

lake build damp-semantics-test >/dev/null
rm -rf "$out"; mkdir -p "$out"
(cd executor && node test/semantics-vectors.mjs "../$oracle" "../$out")

.lake/build/bin/damp-semantics-test "$out/vectors.json" \
  --emitted "$oracle"/lean/*/zkir/*.zkir \
  --other "$out"/synthetic/*.zkir "$oracle"/compact/*/zkir/*.zkir
