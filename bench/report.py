"""Compare Damp's ZKIR with compactc's on the benchmark programs.

usage: python3 -I bench/report.py ROOT [--json FILE]

ROOT (build/bench) holds
  compact/<program>/zkir/*.zkir      compactc 0.36.1 --skip-zk
  noopt|opt|o2/<program>/zkir/*.zkir Damp --no-opt, default, --O2
For every circuit compactc emitted a ZKIR for it prints instruction counts and
proof-system rows (`zkir-v3 mock-compile`), and whether Damp's default output is
the same circuit as compactc's (equal up to variable names), exactly (=), after
test/zkir-normalize.py (~), or after that and dropping `copy` instructions (c). Writes ROOT/results.json (or --json).
"""
import json, os, re, subprocess, sys, tempfile, glob
from collections import Counter
from concurrent.futures import ThreadPoolExecutor

root = sys.argv[1]
out_json = sys.argv[sys.argv.index('--json') + 1] if '--json' in sys.argv else os.path.join(root, 'results.json')
here = os.path.dirname(os.path.abspath(__file__))
normalizer = os.path.join(here, '..', 'test', 'zkir-normalize.py')
VARIANTS = ['compact', 'noopt', 'opt', 'o2']

def load(path): return json.load(open(path))

def rows_of(path):
    r = subprocess.run(['zkir-v3', 'mock-compile', path], capture_output=True, text=True)
    m = re.search(r'rows[^0-9]*([0-9]+)', r.stdout + r.stderr)
    for b in glob.glob(path[:-5] + '.bzkir'): os.remove(b)
    return int(m.group(1)) if m else None

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
    return {'instructions': len(d['instructions']),
            'rows': rows_of(path),
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
print(f"{'circuit':<46}{'instructions':>34}{'rows':>40}  same")
print(f"{'':<46}{'compactc':>9}{'no-opt':>8}{'default':>8}{'O2':>8}  {'compactc':>10}{'no-opt':>9}{'default':>9}{'O2':>9}")
tot = {v: {'instructions': 0, 'rows': 0} for v in VARIANTS}
for key, r in results.items():
    print(f"{key:<46}" + ''.join(f"{cell(r, v, 'instructions'):>{w}}" for v, w in zip(VARIANTS, (9, 8, 8, 8)))
          + '  ' + ''.join(f"{cell(r, v, 'rows'):>{w}}" for v, w in zip(VARIANTS, (10, 9, 9, 9))) + f"  {sym[r['damp_default_vs_compactc']]}")
    for v in VARIANTS:
        for k in ('instructions', 'rows'):
            x = cell(r, v, k)
            if x != '-': tot[v][k] += x
print(f"{'TOTAL':<46}" + ''.join(f"{tot[v]['instructions']:>{w}}" for v, w in zip(VARIANTS, (9, 8, 8, 8)))
      + '  ' + ''.join(f"{tot[v]['rows']:>{w}}" for v, w in zip(VARIANTS, (10, 9, 9, 9))))
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
