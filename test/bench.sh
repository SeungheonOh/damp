#!/usr/bin/env bash
# Damp against compactc on real Compact programs.
#
# 1. compiles every bench/compact/*.compact with compactc (--skip-zk);
# 2. builds the Damp ports (Bench/*.lean) with --no-opt, by default, with --O2 and with --O3,
#    and with --O2 --ledger-opt and --O3 --ledger-opt (columns O2+L, O3+L);
# 3. bench/report.py prints one row per circuit (ZKIR instructions, and rows of the
#    proof system's table from `zkir-v3 mock-compile`) for compactc and the Damp
#    builds, size classes k, whether Damp's default output is compactc's circuit (up to variable names,
#    exactly or after test/zkir-normalize.py), totals, and the two ranked lists; it
#    writes build/bench/results.json;
# 3a. the --O3 level (--O2 plus hashes of constants computed at compile time): every circuit
#    where it differs from --O2, and the totals of the four Damp levels;
# 3b. bench/headroom.py: what a sound optimizer could still remove from compactc's and from Damp's
#    default circuits (dead code, repeated computations, constant folding, redundant range checks,
#    repeated ledger reads, adjacent impacts), measured in instructions and rows;
# 4. executor/test/bench.mjs runs calls through Damp's executor (default, --O2, --O3)
#    and compactc's generated module and requires equal results and ledger state.
#
#   BENCH_OUT   output directory (default build/bench)
#   BENCH_SKIP_EXEC=1  skip step 4
set -euo pipefail
cd "$(dirname "$0")/.."

COMPACT_HOME="${COMPACT_HOME:-$HOME/.compact/versions/0.36.1/x86_64-unknown-linux-musl}"
export PATH="$COMPACT_HOME:$PATH"
out="${BENCH_OUT:-build/bench}"
rm -rf "$out"; mkdir -p "$out"

lake build damp-bench >/dev/null
lake exe damp-bench --no-opt "$out/noopt" >/dev/null
lake exe damp-bench "$out/opt" >/dev/null
lake exe damp-bench --O2 "$out/o2" >/dev/null
lake exe damp-bench --O3 "$out/o3" >/dev/null
lake exe damp-bench --O2 --ledger-opt "$out/o2l" >/dev/null
lake exe damp-bench --O3 --ledger-opt "$out/o3l" >/dev/null

for src in bench/compact/*.compact; do
  name=$(basename "$src" .compact)
  compactc.bin --skip-zk "$src" "$out/compact/$name" >/dev/null 2>"$out/$name.log" \
    || { echo "compactc failed on $src:"; cat "$out/$name.log"; exit 1; }
done

python3 -I bench/report.py "$out" --json "$out/results.json"
echo "wrote $out/results.json"

# --O3 against --O2, circuit by circuit, and the totals of every level.
python3 -I - "$out" <<'PY'
import glob, json, os, re, subprocess, sys
root = sys.argv[1]
def rows(path):
    r = subprocess.run(['zkir-v3', 'mock-compile', path], capture_output=True, text=True)
    m = re.search(r'rows[^0-9]*([0-9]+)', r.stdout + r.stderr)
    for b in glob.glob(path[:-5] + '.bzkir'): os.remove(b)
    return int(m.group(1)) if m else 0
res = json.load(open(os.path.join(root, 'results.json')))['circuits']
tot = {'instr': 0, 'rows': 0}
print(f"\n{'--O3 where it differs from --O2':<56}{'instructions':>14}{'rows':>18}")
for key in sorted(res):
    prog, circ = key.split('.', 1)
    o2 = os.path.join(root, 'o2', prog, 'zkir', circ + '.zkir')
    o3 = os.path.join(root, 'o3', prog, 'zkir', circ + '.zkir')
    if not os.path.exists(o3): continue
    i3 = len(json.load(open(o3))['instructions'])
    same = open(o2).read() == open(o3).read()
    r3 = rows(o3)
    tot['instr'] += i3; tot['rows'] += r3
    if not same:
        i2 = len(json.load(open(o2))['instructions'])
        print(f"{key:<56}{i2:>6} -> {i3:<6}{rows(o2):>8} -> {r3:<8}")
print(f"{'TOTAL --O3':<56}{tot['instr']:>14}{tot['rows']:>18}")
json.dump(tot, open(os.path.join(root, 'o3-totals.json'), 'w'))
PY

# What an optimizer could still remove from compactc's circuits and from Damp's default ones.
echo; python3 -I bench/headroom.py "$out" compact --json "$out/headroom-compactc.json"
echo; python3 -I bench/headroom.py "$out" opt --json "$out/headroom-damp.json"

if [[ -z "${BENCH_SKIP_EXEC:-}" ]]; then
  ln -sfn ../executor/node_modules build/node_modules
  (cd executor && node test/bench.mjs "../$out")
fi
