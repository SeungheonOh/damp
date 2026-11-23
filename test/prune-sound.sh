#!/usr/bin/env bash
# The shipped ZKIR rejects what the source rejects, at every level (Examples/PruneSound.lean,
# Damp/Proofs/Shipped.lean), checked with Midnight's own ZKIR checker: test/PruneSound.lean writes
# the circuits of Examples/PruneSound.lean at --no-opt, default, --O2 and --O3 with honest and forged
# proof data, and executor/test/prune-sound.mjs runs them through `check` from @midnightntwrk/zkir-v3,
# and the two contracts through the JS executor too.
#   PRUNE_OUT   output directory (default build/prune-sound)
# Run under the memory wrapper:
#   timeout 1800 systemd-run --user --scope -q -p MemoryMax=10G -p MemorySwapMax=0 test/prune-sound.sh
set -euo pipefail
cd "$(dirname "$0")/.."
out="${PRUNE_OUT:-build/prune-sound}"
rm -rf "$out"; mkdir -p "$out"
lake build Examples.PruneSound >/dev/null
lake env lean --run test/PruneSound.lean "$out" >/dev/null
ln -sfn ../executor/node_modules build/node_modules
(cd executor && node test/prune-sound.mjs "../$out")
