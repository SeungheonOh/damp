"""Compare Damp's ZKIR with compactc's on the benchmark programs.

usage: python3 -I bench/report.py ROOT [--json FILE]

ROOT (build/bench) holds
  compact/<program>/zkir/*.zkir      compactc 0.36.1 --skip-zk
  noopt|opt|o2|o3/<program>/zkir/*.zkir Damp --no-opt, default, --O2, --O3
  o2l|o3l/<program>/zkir/*.zkir        Damp --O2 --ledger-opt, --O3 --ledger-opt (optional)
For every circuit compactc emitted a ZKIR for it prints instruction counts and
proof-system rows (`zkir-v3 mock-compile`), and whether Damp's default output is
the same circuit as compactc's (equal up to variable names), exactly (=), after
test/zkir-normalize.py (~), or after that and dropping `copy` instructions (c). Writes ROOT/results.json (or --json).

Then the size class of every circuit at every level: the `k` that mock-compile reports, the
proof system's table having 2^k rows. Measured (docs/benchmarks.md, "Size classes"): a circuit
is in class k = max(floor, least k with rows <= 2^k - u), where u is the number of rows the
proof system keeps unusable (7 with `do_communications_commitment`, as every compactc and Damp
circuit has, 6 without) and the floor comes from the lookup tables its instructions use (13 with
a `persistent_hash`, 9 with a `less_than`, `div_mod_power_of_two` or `reconstitute_field`, 4
otherwise). So it moves down a class when it loses `rows - (2^(k-1) - u)` rows ("above", printed
per level), unless k is its floor ("floor"). Proving time and key size step with k, not with rows. Summary:
how many circuits have a smaller (larger) k than compactc's at each level, and the circuits within
5 % above their lower boundary at --O3 with their rows by kind of instruction outside the hashes.
"""
import importlib.util, json, os, re, subprocess, sys, tempfile, glob
from collections import Counter
from concurrent.futures import ThreadPoolExecutor

root = sys.argv[1]
out_json = sys.argv[sys.argv.index('--json') + 1] if '--json' in sys.argv else os.path.join(root, 'results.json')
here = os.path.dirname(os.path.abspath(__file__))
normalizer = os.path.join(here, '..', 'test', 'zkir-normalize.py')
VARIANTS = ['compact', 'noopt', 'opt', 'o2', 'o3', 'o2l', 'o3l']
NAMES = {'compact': 'compactc', 'noopt': 'no-opt', 'opt': 'default', 'o2': 'O2', 'o3': 'O3', 'o2l': 'O2+L', 'o3l': 'O3+L'}
sys.dont_write_bytecode = True
_spec = importlib.util.spec_from_file_location('costs', os.path.join(here, 'costs.py'))
costs = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(costs)

def load(path): return json.load(open(path))

def k_rows_of(path):
    r = subprocess.run(['zkir-v3', 'mock-compile', path], capture_output=True, text=True)
    m = re.search(r'k=([0-9]+), rows=([0-9]+)', r.stdout + r.stderr)
    for b in glob.glob(path[:-5] + '.bzkir'): os.remove(b)
    return (int(m.group(1)), int(m.group(2))) if m else (None, None)

def unusable(d):
    """Rows of the table the proof system does not let the circuit use."""
    return 7 if d.get('do_communications_commitment') else 6

def boundary(k, u=7):
    """The most rows a circuit of class k - 1 can have."""
    return 2 ** (k - 1) - u

FLOOR = {'persistent_hash': 13, 'less_than': 9, 'div_mod_power_of_two': 9, 'reconstitute_field': 9}
def floor_k(d):
    """The least k the lookup tables of the circuit's instructions allow, whatever its rows."""
    return max([4] + [FLOOR.get(i['op'], 4) for i in d['instructions']])

def drop_copies(d):
    """The circuit without `copy` instructions (later uses refer to the source)."""
    ren, ins = {}, []
    sub = lambda v: ren.get(v, v) if isinstance(v, str) else [sub(x) for x in v] if isinstance(v, list) else v
    for i in d['instructions']:
        i = {k: sub(v) for k, v in i.items()}
        if i['op'] == 'copy': ren[i['output']] = i['val']; continue
        ins.append(i)
    return {**d, 'instructions': ins}

def canon(d):
    """The circuit with every variable renamed by order of first appearance."""
    names = {}
    def ren(v):
        if isinstance(v, str) and v.startswith('%'):
            return names.setdefault(v, '%' + str(len(names)))
        if isinstance(v, list): return [ren(x) for x in v]
        return v
    ins = []
    for i in d['instructions']:
        j = {}
        for k in ('output', 'outputs'):          # definitions first, so names are stable
            if k in i: j[k] = ren(i[k])
        for k, v in i.items():
            if k not in j: j[k] = ren(v)
        ins.append(j)
    return json.dumps({'inputs': [ren(x['name']) for x in d.get('inputs', [])],
                       'outputs': d.get('outputs'), 'instructions': ins}, sort_keys=True)

def measure(path):
    d = load(path)
    k, rows = k_rows_of(path)
    return {'instructions': len(d['instructions']),
            'rows': rows, 'k': k, 'floor': floor_k(d),
            'above': None if k is None or k <= floor_k(d) else rows - boundary(k, unusable(d)),
            'ops': dict(sorted(Counter(i['op'] for i in d['instructions']).items()))}

jobs, results = [], {}
for prog in sorted(os.listdir(os.path.join(root, 'compact'))):
    for f in sorted(glob.glob(os.path.join(root, 'compact', prog, 'zkir', '*.zkir'))):
        circ = os.path.basename(f)[:-5]
        results[f'{prog}.{circ}'] = {'program': prog, 'circuit': circ, 'variants': {}}
        for v in VARIANTS:
            p = os.path.join(root, v, prog, 'zkir', circ + '.zkir')
            if os.path.exists(p): jobs.append((f'{prog}.{circ}', v, p))
with ThreadPoolExecutor(16) as ex:
    for (key, v, p), m in zip(jobs, ex.map(lambda j: measure(j[2]), jobs)):
        results[key]['variants'][v] = m

tmp = tempfile.mkdtemp()
def compare(r, key, variant):
    """How Damp's circuit at `variant` relates to compactc's."""
    vs = r['variants']
    if 'compact' not in vs or variant not in vs: return None
    a = os.path.join(root, 'compact', r['program'], 'zkir', r['circuit'] + '.zkir')
    b = os.path.join(root, variant, r['program'], 'zkir', r['circuit'] + '.zkir')
    n = os.path.join(tmp, f'{key}.{variant}.zkir')
    subprocess.run([sys.executable, '-I', normalizer, a, n], check=True)
    cb = canon(load(b))
    r.setdefault('compactc_reduction', {})[variant] = {
        'raw': len(load(a)['instructions']), 'after_normalization': len(load(n)['instructions']),
        'after_dropping_copies': len(drop_copies(load(n))['instructions']), 'damp': len(load(b)['instructions'])}
    return ('identical' if canon(load(a)) == cb else
            'identical-after-normalization' if canon(load(n)) == cb else
            'identical-without-copies' if canon(drop_copies(load(n))) == canon(drop_copies(load(b))) else 'differs')
for key, r in results.items():
    r['damp_default_vs_compactc'] = compare(r, key, 'opt')
    r['damp_o2_vs_compactc'] = compare(r, key, 'o2')

json.dump({'circuits': results}, open(out_json, 'w'), indent=1)

def cell(r, v, k):
    m = r['variants'].get(v)
    return '-' if m is None or m[k] is None else m[k]
sym = {'identical': '=', 'identical-after-normalization': '~', 'identical-without-copies': 'c', 'differs': 'x', None: '?'}
IW, RW = (9, 8, 8, 8, 8, 8, 8), (10, 9, 9, 9, 9, 9, 9)
print(f"{'circuit':<46}{'instructions':>{sum(IW)}}{'rows':>{sum(RW) + 2}}  same   (+L: --ledger-opt)")
print(f"{'':<46}" + ''.join(f"{NAMES[v]:>{w}}" for v, w in zip(VARIANTS, IW)) + '  '
      + ''.join(f"{NAMES[v]:>{w}}" for v, w in zip(VARIANTS, RW)))
tot = {v: {'instructions': 0, 'rows': 0} for v in VARIANTS}
for key, r in results.items():
    print(f"{key:<46}" + ''.join(f"{cell(r, v, 'instructions'):>{w}}" for v, w in zip(VARIANTS, IW))
          + '  ' + ''.join(f"{cell(r, v, 'rows'):>{w}}" for v, w in zip(VARIANTS, RW)) + f"  {sym[r['damp_default_vs_compactc']]}")
    for v in VARIANTS:
        for k in ('instructions', 'rows'):
            x = cell(r, v, k)
            if x != '-': tot[v][k] += x
print(f"{'TOTAL':<46}" + ''.join(f"{tot[v]['instructions']:>{w}}" for v, w in zip(VARIANTS, IW))
      + '  ' + ''.join(f"{tot[v]['rows']:>{w}}" for v, w in zip(VARIANTS, RW)))
n = len(results)
cnt = Counter(r['damp_default_vs_compactc'] for r in results.values())
missing = [k for k, r in results.items() if r['damp_default_vs_compactc'] is None]
if missing: print('\nnot built by Damp (compactc emitted a ZKIR): ' + ', '.join(missing))
print(f"\n{n} circuits; default Damp ZKIR identical to compactc's: {cnt['identical']} exactly, "
      f"{cnt['identical-after-normalization']} after normalization, {cnt['identical-without-copies']} equal once compactc's `copy` instructions are dropped, {cnt['differs']} different, {cnt[None]} not built")
def ranked(title, sign):
    items = []
    for key, r in results.items():
        c, d = cell(r, 'compact', 'instructions'), cell(r, 'opt', 'instructions')
        cr, dr = cell(r, 'compact', 'rows'), cell(r, 'opt', 'rows')
        if '-' in (c, d, cr, dr): continue
        if sign * (d - c) > 0: items.append((sign * (d - c), sign * (dr - cr), key, c, d, cr, dr))
    print(f"\n{title}")
    if not items: print('  none')
    for dd, dr, key, c, d, cr, dr_ in sorted(items, reverse=True):
        print(f"  {key:<46} instructions {c:>5} vs {d:>5} ({'+' if sign > 0 else '-'}{dd}), rows {cr} vs {dr_} ({dr_ - cr:+d})")
def split():
    print("\nWhere compactc's output is larger than Damp's default, by what kind of difference (instructions):")
    print(f"  {'circuit':<46}{'total':>6}{'recomputed hash/const':>23}{'copy of a variable':>20}{'other':>7}")
    t = [0, 0, 0, 0]
    for key, r in results.items():
        x = r.get('compactc_reduction', {}).get('opt')
        if not x or x['raw'] <= x['damp']: continue
        a, b, c = x['raw'] - x['after_normalization'], x['after_normalization'] - x['after_dropping_copies'], x['after_dropping_copies'] - x['damp']
        print(f"  {key:<46}{x['raw'] - x['damp']:>6}{a:>23}{b:>20}{c:>7}")
        for i, v in enumerate((x['raw'] - x['damp'], a, b, c)): t[i] += v
    print(f"  {'TOTAL':<46}{t[0]:>6}{t[1]:>23}{t[2]:>20}{t[3]:>7}")
ranked('Circuits where Damp (default) is LARGER than compactc (by instructions):', 1)
ranked('Circuits where compactc is larger than Damp (default):', -1)
split()

def size_classes():
    print("\nSize class k (the circuit fits a table of 2^k rows: rows <= 2^k - 7), and rows above the next")
    print("lower boundary 2^(k-1) - 7 (what the circuit must lose to drop one class; 'floor': the lookup")
    print("tables of its instructions need 2^k rows whatever the row count):")
    print(f"  {'circuit':<44}" + ''.join(f"{NAMES[v]:>15}" for v in VARIANTS))
    for key, r in results.items():
        print(f"  {key:<44}" + ''.join(
            f"{'-':>15}" if cell(r, v, 'k') == '-' else
            f"{cell(r, v, 'k'):>4} {'floor' if cell(r, v, 'above') == '-' else '+' + str(cell(r, v, 'above')):>10}"
            for v in VARIANTS))
    print("\nCircuits by k relative to compactc's (smaller / equal / larger), and the sum of 2^k over the suite:")
    for v in VARIANTS:
        c = Counter()
        for r in results.values():
            a, b = cell(r, 'compact', 'k'), cell(r, v, 'k')
            if '-' in (a, b): continue
            c['smaller' if b < a else 'larger' if b > a else 'equal'] += 1
        s2 = sum(2 ** cell(r, v, 'k') for r in results.values() if cell(r, v, 'k') != '-')
        print(f"  {NAMES[v]:<10} smaller {c['smaller']:>3}  equal {c['equal']:>3}  larger {c['larger']:>3}  sum 2^k {s2:>9}")
    near = [(key, r) for key, r in results.items() if cell(r, 'o3', 'above') != '-'
            and cell(r, 'o3', 'above') <= 0.05 * (cell(r, 'o3', 'rows') - cell(r, 'o3', 'above'))]
    print(f"\nAt their floor at --O3 (no row count lowers k): {sum(cell(r, 'o3', 'k') != '-' and cell(r, 'o3', 'above') == '-' for r in results.values())} circuits")
    print("\nWithin 5 % above their lower boundary at --O3, with the rows each kind of instruction costs")
    print("(bench/costs.py --attribute; 'outside hashes': the circuit with every persistent and transient")
    print("hash replaced by private inputs):")
    tmp_ = tempfile.mkdtemp()
    for key, r in near:
        p = os.path.join(root, 'o3', r['program'], 'zkir', r['circuit'] + '.zkir')
        a = costs.attribute(p, key)
        nh = costs.rows_of(costs.without_kinds(load(p), {'persistent_hash', 'transient_hash'}), key + '.nh')
        r['near_boundary_o3'] = {'kinds': a['kinds'], 'outside_hashes': nh}
        ks = ', '.join(f"{k} x{x['n']}: {x['rows']}" for k, x in sorted(a['kinds'].items(), key=lambda x: -x[1]['rows'])
                       if x['rows'] and k != 'persistent_hash')
        print(f"  {key:<40} k={cell(r, 'o3', 'k')} rows {cell(r, 'o3', 'rows')} (+{cell(r, 'o3', 'above')} over "
              f"{cell(r, 'o3', 'rows') - cell(r, 'o3', 'above')}); outside hashes {nh}: {ks}")
    if not near: print('  none')
    json.dump({'circuits': results}, open(out_json, 'w'), indent=1)
size_classes()
