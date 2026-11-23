#!/usr/bin/env bash
# `--O3` folded constants end to end (audit finding F3): test/O3Fold.lean writes a contract whose
# `check` circuit requires hashes of literals (constants at --O3) to equal hashes the runtime
# computed in an earlier call, at --O2 and --O3; executor/test/o3-fold.mjs runs both calls through
# Damp's executor and the real runtime, compares the result with the runtime's own hash functions,
# and hands every call's proof data to Midnight's ZKIR checker.
#   O3F_OUT  output directory (default build/o3-fold)
# Run under the memory wrapper:
#   timeout 1800 systemd-run --user --scope -q -p MemoryMax=10G -p MemorySwapMax=0 test/o3-fold.sh
set -euo pipefail
cd "$(dirname "$0")/.."
out="${O3F_OUT:-build/o3-fold}"
rm -rf "$out"; mkdir -p "$out"
lake build Bench >/dev/null
lake env lean --run test/O3Fold.lean "$out" >/dev/null
ln -sfn ../executor/node_modules build/node_modules
(cd executor && node test/o3-fold.mjs "../$out")
