#!/usr/bin/env bash
# The cross-contract call assumption of --ledger-opt, tested with real
# contracts: a callee changes only its own state, never its caller's
# (Damp/Proofs/Ledger/Calls.lean, executor/test/call-isolation.mjs,
# docs/ledger-model.md "Calls").
#
# 1. Writes the example contracts' contract.json (lake exe damp-examples) into
#    $DAMP_ISO_OUT/lean (default build/calls-isolation), unless ISO_REUSE=1 and
#    they exist.
# 2. Compiles `back` (below; a contract calling back into the contract stored
#    in its ledger) with compactc --skip-zk.
# 3. Runs the calls of executor/test/call-isolation.mjs with every query of every
#    contract logged, and checks that each contract's queries thread.
#
#   COMPACT_HOME  directory holding compactc.bin
set -euo pipefail
cd "$(dirname "$0")/.."

COMPACT_HOME="${COMPACT_HOME:-$HOME/.compact/versions/0.36.1/x86_64-unknown-linux-musl}"
out="${DAMP_ISO_OUT:-build/calls-isolation}"
mkdir -p "$out"

if [[ "${ISO_REUSE:-0}" != 1 || ! -f "$out/lean/caller/contract.json" ]]; then
  rm -rf "$out/lean"
  lake exe damp-examples "$out/lean" >"$out/examples.log" 2>&1 || { echo "damp-examples failed (see $out/examples.log)" >&2; exit 1; }
fi

mkdir -p "$out/src"
cat >"$out/src/back.compact" <<'EOF'
pragma language_version >= 0.16;
import CompactStandardLibrary;
// Calls `bump` of the contract stored in `target` (the call-isolation test).
// It has the circuits of Examples.Caller's contract type `Adder`, so the
// caller can call it as an adder.
contract Bumper {
  circuit bump(x: Field): Field;
}
export ledger target: Bumper;
export ledger hits: Counter;
constructor(t: Bumper) {
  target = disclose(t);
}
export circuit addTo(x: Field): Field {
  hits.increment(1);
  return target.bump(disclose(x));
}
export circuit clear(): [] {
  hits.increment(2);
}
EOF
rm -rf "$out/compact/back"
"$COMPACT_HOME/compactc.bin" --skip-zk "$out/src/back.compact" "$out/compact/back" >"$out/compactc.log" 2>&1 \
  || { echo "compactc failed (see $out/compactc.log)" >&2; exit 1; }
# compactc's module imports the runtime from the nearest node_modules.
[[ -e "$out/node_modules" ]] || ln -s "$(pwd)/executor/node_modules" "$out/node_modules"

(cd executor && node test/call-isolation.mjs "../$out/lean" "../$out/compact/back")
