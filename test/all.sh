#!/usr/bin/env bash
# Full test run: verifier keys against compactc, then the executor.
set -euo pipefail
cd "$(dirname "$0")/.."
out="${DAMP_OUT:-build/oracle}"
./test/oracle.sh
ln -sfn ../executor/node_modules build/node_modules   # lets compactc's generated modules resolve the runtime
(cd executor && node test/run.mjs "../$out")
(cd executor && node test/bytes-limbs.mjs "../$out" && node test/either-both.mjs "../$out")
