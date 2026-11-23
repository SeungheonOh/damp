#!/usr/bin/env bash
# The opt-in ledger passes (`--ledger-opt`: `Circuit.ledgerReuse`, then `Circuit.ledgerDeadStore`;
# Damp/Optimize/LedgerReuse.lean, LedgerDeadStore.lean), end to end.
#
# 1. Builds every benchmark program at --O2 ($out/o2) and at --O2 --ledger-opt ($out/lo).
# 2. Prints, for every circuit the pass changed, instructions and rows (zkir-v3 mock-compile).
# 3. Runs the benchmark calls through the real runtime against both builds and requires equal
#    results, ledger states, Zswap states and private transcripts, and the ZKIR checker's
#    acceptance of the rewritten circuits' proof data (executor/test/ledger-opt.mjs); reports gas.
#
# LO_OUT overrides the output directory (default build/ledger-opt).
set -euo pipefail
cd "$(dirname "$0")/.."

COMPACT_HOME="${COMPACT_HOME:-$HOME/.compact/versions/0.36.1/x86_64-unknown-linux-musl}"
export PATH="$COMPACT_HOME:$PATH"
out="${LO_OUT:-build/ledger-opt}"
rm -rf "$out"; mkdir -p "$out"

lake build damp-bench >/dev/null
lake exe damp-bench --O2 "$out/o2" >/dev/null
lake exe damp-bench --O2 --ledger-opt "$out/lo" >/dev/null
# --ledger-opt is refused with --no-opt.
if lake exe damp-bench --no-opt --ledger-opt "$out/refused" >/dev/null 2>&1; then
  echo "damp-bench accepted --no-opt --ledger-opt"; exit 1
fi

python3 -I - "$out/o2" "$out/lo" <<'PY'
import glob, json, os, re, subprocess, sys, tempfile, shutil
a, b = sys.argv[1], sys.argv[2]
tmp = tempfile.mkdtemp()
def rows(p):
    q = os.path.join(tmp, 'x.zkir'); shutil.copy(p, q)
    r = subprocess.run(['zkir-v3', 'mock-compile', q], capture_output=True, text=True)
    m = re.search(r'rows[^0-9]*([0-9]+)', r.stdout + r.stderr)
    return int(m.group(1)) if m else None
ti = tr = tot = n = 0
for f in sorted(glob.glob(os.path.join(a, '*', 'zkir', '*.zkir'))):
    rel = os.path.relpath(f, a); g = os.path.join(b, rel)
    da, db = json.load(open(f)), json.load(open(g))
    ra = rows(f); tot += ra
    if da == db: continue
    rb = rows(g); n += 1
    ia, ib = len(da['instructions']), len(db['instructions'])
    ti += ia - ib; tr += ra - rb
    print('%-60s instr %5d -> %5d   rows %6d -> %6d' % (rel, ia, ib, ra, rb))
print(f'{n} circuits changed; instructions saved {ti}, rows saved {tr} of {tot}')
PY

# What the passes leave (bench/ledger_headroom.py --classes, the frame analysis ported): every read
# a fact answers and every dead store the pass handles must be gone. Left: forwarding blocked by the
# operand size cap or a multi-limb value, and dead stores across writes of other fields at the top
# level (unsound in the model when the contract state is a map, see docs/benchmarks.md).
python3 -I bench/ledger_headroom.py "$out/lo" --classes --json "$out/classes.json" >/dev/null
python3 -I - "$out/classes.json" <<'PY'
import json, sys
tot = json.load(open(sys.argv[1]))['total']
left = {k: v for k, v in tot.items() if (k.startswith('R:') and 'BIG' not in k and 'MULTILIMB' not in k)
        or (k.startswith('D:') and 'across-root-writes' not in k and 'guard' not in k)}
print('left by the passes:', {k: v for k, v in tot.items() if k.startswith(('R:', 'D:'))})
if left:
    print('FAIL: rewrites the passes should have made:', left); sys.exit(1)
PY

ln -sfn ../executor/node_modules build/node_modules
(cd executor && node test/ledger-opt.mjs "../$out")
