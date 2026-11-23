#!/usr/bin/env bash
# The JSON text layer: Lean core's `Json.pretty` and `Json.parse` against Damp's
# total reference lexer and parser (Damp/Zkir/JsonText.lean), about which the
# round trip is proved (Damp/Proofs/JsonText.lean, Damp/Proofs/ZkirText.lean).
#
# Builds every contract of Examples and Bench at every level (and --O2 --ledger-opt) and runs
# test/JsonText.lean on every .zkir and contract.json written, and on random values.
#
#   JSONTEXT_OUT     output directory (default build/jsontext)
#   JSONTEXT_RANDOM  number of random values (default 3000)
set -euo pipefail
cd "$(dirname "$0")/.."

out="${JSONTEXT_OUT:-build/jsontext}"
rm -rf "$out"; mkdir -p "$out"

lake build damp-examples damp-bench Damp.Compile.Export >/dev/null
for level in no-opt default O2 O3 O2-ledger-opt; do
  case $level in default) flag="";; O2-ledger-opt) flag="--O2 --ledger-opt";; *) flag="--$level";; esac
  lake exe damp-examples $flag "$out/examples-$level" >/dev/null
  lake exe damp-bench $flag "$out/bench-$level" >/dev/null
done

lake env lean --run test/JsonText.lean "$out" --random "${JSONTEXT_RANDOM:-3000}"
