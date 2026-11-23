#!/usr/bin/env bash
# The opt-in ledger passes (`--ledger-opt`: `Circuit.ledgerReuse`, the --O2 passes again,
# `Circuit.ledgerDeadStore`, `Circuit.ledgerHoist`, `Circuit.ledgerMerge`; Damp/Optimize/Ledger*.lean),
# end to end.
#
# 1. Builds every benchmark program at --O2 ($out/o2), at --O2 --ledger-opt ($out/lo), and at --O2
#    with every ledger pass but `ledgerHoist` and `ledgerMerge` ($out/nm, through a small Lean driver written to
#    $out/NoMerge.lean), and zerocash_core with compactc ($out/compact, for its Merkle paths).
# 2. Prints, for every circuit the pass changed, instructions and rows (zkir-v3 mock-compile).
# 3. Runs the benchmark calls through the real runtime against both builds and requires equal
#    results, ledger states, Zswap states and private transcripts, and the ZKIR checker's
#    acceptance of the rewritten circuits' proof data (executor/test/ledger-opt.mjs); reports gas.
#
# LO_OUT overrides the output directory (default build/ledger-opt).
# 4. Requires that `ledgerHoist` and `ledgerMerge` change no circuit's rows or instruction count and save
#    ledger programs (nm -> lo).
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
# --O2 and the ledger passes without the last two, `ledgerHoist` and `ledgerMerge` (which only regroup
# ledger statements into requests): what the merge is measured against.
cat > "$out/NoMerge.lean" <<'LEAN'
import Bench
open Damp

/-- `Contract.optimize .full true` with `IR.ledgerPasses` minus its last two, `ledgerHoist` and `ledgerMerge`. -/
def noMerge (c : Contract) : Contract :=
  let f : IR.Pass := fun circ => IR.runPasses (IR.ledgerPasses.take 3) circ.optimizeFull
  { c with circuits := c.circuits.map f, «constructor» := c.«constructor».map f }

def main (args : List String) : IO UInt32 := do
  let out := System.FilePath.mk (args.headD "nm")
  unless IR.ledgerPasses.length = 5 do throw (IO.userError "ledgerPasses changed: update NoMerge")
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
# Programs for the witness barriers (Damp/Optimize/LedgerFrame.lean), built at o2, nm and lo by their
# own driver (they are not benchmark programs): `lo_barrier`, a ledger statement that reads the call
# context never moves above `createZswapOutput` (which writes call-context slot 1); `lo_witness`, no
# write is dropped or moved across a user's witness (which reads the contract state), while
# `ownPublicKey` and `createZswapInput` (isolated) are crossed. Then the rewrites the barriers must
# allow and forbid are checked on the built circuits.
cat > "$out/Barrier.lean" <<'LEAN'
import Bench
open Damp

/-! A contract for the witness barrier (`ctxWitness`, Damp/Optimize/LedgerFrame.lean): the runtime's
`createZswapOutput` inserts the coin's commitment into the call context (`insertCommitment`), and
`writeCoin` reads it back from there. A ledger statement reading the context must not move above it. -/
namespace LoBarrier
abbrev SR := Either ZswapCoinPublicKey ContractAddress

ledger
  count : Cell Field
  held : Cell QualifiedShieldedCoinInfo

/-- The contract's address, a guarded write (so that the next request does not bind it), a read,
    the coin output, the coin-storing write, a write and a read. Without the barrier the
    coin-storing write is merged into the read's request, above the output. -/
circuit store (coin : ShieldedCoinInfo) (b : Boolean) : Field := do
  const me ← Kernel.self
  if% disclose b then count.write 1
  const n ← count.read
  createZswapOutput (disclose coin) (right me : SR)
  held.writeCoin (disclose coin) (right me : SR)
  count.write (n + 1)
  return (← count.read)

/-- The same through `receiveShielded` (the output and the claim of its commitment). -/
circuit receive (coin : ShieldedCoinInfo) : Field := do
  const n ← count.read
  receiveShielded (disclose coin)
  held.writeCoin (disclose coin) (right (← Kernel.self) : SR)
  count.write (n + 1)
  return (← count.read)

/-- The stored coin's index. -/
circuit peek : Uint64 := do
  return (← held.read).mt_index

contract lo_barrier
end LoBarrier

/-! A contract for the barriers at the other witnesses (`stateWitness`, `isolatedWitness`,
Damp/Optimize/LedgerFrame.lean; the footprints of Damp/Executor/Witnesses.lean). A user's witness
is handed the contract's current state (`WitnessContext.ledger`): `ledgerDeadStore` must not drop a
write it could read, `ledgerMerge` must not move a write above it (`deadstore`, `merge`, from the
audit's repro, test/audit/LedgerWitness.lean). A context read may move above it (`hoistUser`).
`ownPublicKey` and `createZswapInput` neither see nor change the ledger: the passes cross them
(`mergePk`, `mergeIn`, `deadIn`), and the runtime agrees. -/
namespace LoWitness

ledger
  c : Cell Field
  d : Cell Field

witness peekC : Field
witness peekD : Field

circuit deadstore : Field := do
  c.write 1
  const x ← peekC
  c.write 2
  return disclose x

circuit merge (v : Field) : Field := do
  c.write (disclose v)
  const x ← peekD
  d.write (disclose v + 7)
  return disclose x

circuit control : Field := do
  c.write 3
  const x ← peekC
  return disclose x

/-- The address read moves above the user's witness, into the write's request. -/
circuit hoistUser (v : Field) : ContractAddress := do
  c.write (disclose v)
  const x ← peekC
  const me ← Kernel.self
  d.write (disclose x)
  return me

circuit mergePk (v : Field) : ZswapCoinPublicKey := do
  c.write (disclose v)
  const k ← ownPublicKey
  d.write (disclose v + 1)
  return k

circuit mergeIn (coin : QualifiedShieldedCoinInfo) (v : Field) : Field := do
  c.write (disclose v)
  createZswapInput (disclose coin)
  d.write (disclose v + 2)
  return (← d.read)

circuit deadIn (coin : QualifiedShieldedCoinInfo) : Field := do
  c.write 4
  createZswapInput (disclose coin)
  c.write 5
  return (← c.read)

contract lo_witness
end LoWitness

/-- `IR.ledgerPasses` minus `ledgerHoist` and `ledgerMerge`, as in NoMerge.lean. -/
def noMerge (c : Contract) : Contract :=
  let f : IR.Pass := fun circ => IR.runPasses (IR.ledgerPasses.take 3) circ.optimizeFull
  { c with circuits := c.circuits.map f, «constructor» := c.«constructor».map f }

def main (args : List String) : IO UInt32 := do
  let out := System.FilePath.mk (args.headD "build")
  for c in [LoBarrier.contract, LoWitness.contract] do
    for (dir, m) in [("o2", c.optimize .full false), ("nm", noMerge c), ("lo", c.optimize .full true)] do
      for circ in m.circuits ++ m.«constructor».toList do
        if let .error e := circ.checkLedger then throw (IO.userError s!"{c.name}: {e}")
      let srcs ← IO.ofExcept m.emitAll
      m.writeFiles (out / dir / c.name) srcs
  return 0
LEAN
lake env lean --run "$out/Barrier.lean" "$out" >/dev/null
python3 -I - "$out" <<'PYEOF'
import json, os, sys
root = sys.argv[1]
sh = lambda bd: ''.join({'ledger': 'L', 'witness': 'W', 'bind': 'B'}.get(s['kind'], 'A') for s in bd if s['kind'] != 'ledger' or s['ops'])
def body(level, circ):
    return next(c for c in json.load(open(os.path.join(root, level, 'lo_witness', 'contract.json')))['circuits'] if c['name'] == circ)['body']
bad = 0
def want(circ, cond, what):
    global bad
    a, b = sh(body('o2', circ)), sh(body('lo', circ))
    ok = cond(a, b)
    print(f'{"ok  " if ok else "FAIL"} lo_witness.{circ}: {a} -> {b}  ({what})')
    bad += not ok
nl = lambda s: s.count('L')
want('deadstore', lambda a, b: nl(b) == nl(a), 'no write dropped across a user witness')
want('merge', lambda a, b: nl(b) == nl(a), 'no write moved above a user witness')
want('hoistUser', lambda a, b: nl(b) < nl(a), 'the address read moved above the user witness and merged')
want('mergePk', lambda a, b: nl(b) < nl(a), 'merged across ownPublicKey')
want('mergeIn', lambda a, b: nl(b) < nl(a), 'merged across createZswapInput')
want('deadIn', lambda a, b: nl(b) < nl(a), 'a write dropped across createZswapInput')
sys.exit(1 if bad else 0)
PYEOF
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
# (The barrier contracts lo_* are left out: the classifier does not know the witness barriers, and
# lo_witness.deadstore is a dead store across a user's witness, which must stay.)
rm -rf "$out/lo-bench"; mkdir -p "$out/lo-bench"
for d in "$out/lo"/*/; do case "$(basename "$d")" in lo_*) ;; *) ln -s "$(cd "$d" && pwd)" "$out/lo-bench/$(basename "$d")" ;; esac; done
python3 -I bench/ledger_headroom.py "$out/lo-bench" --classes --json "$out/classes.json" >/dev/null
python3 -I - "$out/classes.json" <<'PY'
import json, sys
tot = json.load(open(sys.argv[1]))['total']
left = {k: v for k, v in tot.items() if (k.startswith('R:') and 'BIG' not in k and 'MULTILIMB' not in k)
        or (k.startswith('D:') and 'across-root' not in k and 'guard' not in k)}
print('left by the passes:', {k: v for k, v in tot.items() if k.startswith(('R:', 'D:'))})
if left:
    print('FAIL: rewrites the passes should have made:', left); sys.exit(1)
PY

# `ledgerHoist` and `ledgerMerge` only reorder and regroup ledger statements: the same rows and
# instruction count, fewer ledger programs.
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
