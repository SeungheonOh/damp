#!/usr/bin/env bash
# The opt-in ledger passes (`--ledger-opt`: `Circuit.ledgerReuse`, the --O2 passes again,
# `Circuit.ledgerDeadStore`, `Circuit.ledgerMerge`; Damp/Optimize/Ledger*.lean), end to end.
#
# 1. Builds every benchmark program at --O2 ($out/o2), at --O2 --ledger-opt ($out/lo), and at --O2
#    with every ledger pass but `ledgerMerge` ($out/nm, through a small Lean driver written to
#    $out/NoMerge.lean), and zerocash_core with compactc ($out/compact, for its Merkle paths).
# 2. Prints, for every circuit the pass changed, instructions and rows (zkir-v3 mock-compile).
# 3. Runs the benchmark calls through the real runtime against both builds and requires equal
#    results, ledger states, Zswap states and private transcripts, and the ZKIR checker's
#    acceptance of the rewritten circuits' proof data (executor/test/ledger-opt.mjs); reports gas.
#
# LO_OUT overrides the output directory (default build/ledger-opt).
# 4. Requires that `ledgerMerge` changes no circuit's rows and saves ledger programs (nm -> lo).
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
# --O2 and the ledger passes without the last one, `ledgerMerge`: what the merge is measured against.
cat > "$out/NoMerge.lean" <<'LEAN'
import Bench
open Damp

/-- `Contract.optimize .full true` with `IR.ledgerPasses` minus its last pass, `ledgerMerge`. -/
def noMerge (c : Contract) : Contract :=
  let f : IR.Pass := fun circ => IR.runPasses (IR.ledgerPasses.take 3) circ.optimizeFull
  { c with circuits := c.circuits.map f, «constructor» := c.«constructor».map f }

def main (args : List String) : IO UInt32 := do
  let out := System.FilePath.mk (args.headD "nm")
  unless IR.ledgerPasses.length = 4 do throw (IO.userError "ledgerPasses changed: update NoMerge")
  for c in [Bench.Counter.contract, Bench.Tiny.contract, Bench.Threading.contract, Bench.GasCost.contract,
      Bench.BlockTime.contract, Bench.UnshieldedTokens.contract, Bench.Coracle.contract,
      Bench.ElectionCore.contract, Bench.ZerocashCore.contract, Bench.Pm20028.contract,
      Bench.Pm19287.contract, Bench.Types.contract, Bench.AssertMisc.contract,
      Bench.AdtCounter.contract, Bench.AdtListStruct.contract, Bench.AdtMapList.contract,
      Bench.AdtMerkle.contract, Bench.ComposableInner.contract, Bench.ComposableOuter.contract,
      Bench.Vectors.contract, Bench.Test01.contract, Bench.ProofData.contract,
      Bench.ZkirGeneration.contract] do
    let m := noMerge c
    for circ in m.circuits ++ m.«constructor».toList do
      if let .error e := circ.checkLedger then throw (IO.userError s!"{c.name}: {e}")
    let srcs ← IO.ofExcept m.emitAll
    m.writeFiles (out / c.name) srcs
  return 0
LEAN
lake env lean --run "$out/NoMerge.lean" "$out/nm" >/dev/null
mkdir -p "$out/compact"
compactc.bin --skip-zk bench/compact/zerocash_core.compact "$out/compact/zerocash_core" >/dev/null

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

# `ledgerMerge` only regroups ledger statements: the same rows, fewer ledger programs.
python3 -I - "$out/nm" "$out/lo" <<'PY'
import glob, json, os, re, subprocess, sys, tempfile, shutil
a, b = sys.argv[1], sys.argv[2]
tmp = tempfile.mkdtemp()
def rows(p):
    q = os.path.join(tmp, 'x.zkir'); shutil.copy(p, q)
    r = subprocess.run(['zkir-v3', 'mock-compile', q], capture_output=True, text=True)
    m = re.search(r'rows[^0-9]*([0-9]+)', r.stdout + r.stderr)
    return int(m.group(1)) if m else None
nl = lambda c: sum(1 for s in c['body'] if s['kind'] == 'ledger' and s['ops'])
n = before = after = bad = 0
for f in sorted(glob.glob(os.path.join(a, '*', 'contract.json'))):
    prog = os.path.basename(os.path.dirname(f))
    ca, cb = json.load(open(f)), json.load(open(os.path.join(b, prog, 'contract.json')))
    for x in ca['circuits']:
        y = next(c for c in cb['circuits'] if c['name'] == x['name'])
        before += nl(x); after += nl(y)
        if x['body'] == y['body']: continue
        n += 1
        za, zb = (os.path.join(d, prog, 'zkir', x['name'] + '.zkir') for d in (a, b))
        ra, rb = rows(za), rows(zb)
        ia, ib = (len(json.load(open(z))['instructions']) for z in (za, zb))
        print('%-50s ledger programs %3d -> %3d  instr %4d -> %4d  rows %6d -> %6d' % (prog + '.' + x['name'], nl(x), nl(y), ia, ib, ra, rb))
        if ra != rb or ia != ib or nl(y) >= nl(x): bad += 1
print(f'ledgerMerge: {n} circuits merged; ledger programs {before} -> {after}')
if bad: print('FAIL: a merged circuit changed rows or instructions, or kept its ledger programs'); sys.exit(1)
PY

ln -sfn ../executor/node_modules build/node_modules
(cd executor && node test/ledger-opt.mjs "../$out")
