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

(cd executor && node test/call-isolation.mjs "../$out/lean" "../$out/compact/back" "../$out/results-lean.json")

# The same calls against the callers built with --O2 --ledger-opt: under the call assumption a call is
# an isolated witness (`isolatedWitness`, Damp/Optimize/LedgerFrame.lean), which no ledger pass treats
# as a barrier. The results and every contract's final state must be those of the build damp-examples
# writes. (In these callers the statements after a call use its result, so none moves above one; the
# rewrites that happen merge statements between calls.)
cat >"$out/CallsLo.lean" <<'LEAN'
import Examples
open Damp

def main (args : List String) : IO UInt32 := do
  let out := System.FilePath.mk (args.headD "build")
  for c in [Examples.Adder.contract, Examples.Rich.contract, Examples.Caller.contract, Examples.Relay.contract,
      Examples.Top.contract] do
    let m := c.optimize .full true
    for circ in m.circuits ++ m.«constructor».toList do
      if let .error e := circ.checkLedger then throw (IO.userError s!"{c.name}: {e}")
    let srcs ← IO.ofExcept m.emitAll
    m.writeFiles (out / c.name) srcs
  return 0
LEAN
rm -rf "$out/lo"
lake env lean --run "$out/CallsLo.lean" "$out/lo" >/dev/null
python3 -I - "$out/lean" "$out/lo" <<'PYEOF'
import json, os, sys
a, b = sys.argv[1], sys.argv[2]
sh = lambda bd: ''.join({'ledger': 'L', 'witness': 'W', 'bind': 'B'}.get(s['kind'], 'A') for s in bd)
for n in ['caller', 'relay', 'top']:
    ca, cb = (json.load(open(os.path.join(d, n, 'contract.json')))['circuits'] for d in (a, b))
    for x in ca:
        y = next(c for c in cb if c['name'] == x['name'])
        if x['body'] != y['body']:
            print(f'{n}.{x["name"]}: {sh(x["body"])} -> {sh(y["body"])} with --ledger-opt')
PYEOF
(cd executor && node test/call-isolation.mjs "../$out/lo" "../$out/compact/back" "../$out/results-lo.json")
python3 -I - "$out/results-lean.json" "$out/results-lo.json" <<'PYEOF'
import json, sys
a, b = (json.load(open(p)) for p in sys.argv[1:3])
if a != b:
    print('FAIL: the --ledger-opt callers differ from the damp-examples build:', a, b); sys.exit(1)
print('the --ledger-opt callers give the same results and final states:', {k: v for k, v in a.items() if k != 'states'})
PYEOF
