"""Print two ZKIR circuits side by side as canonical text, one instruction per line,
variables renamed by order of first appearance, and diff them.

usage: python3 -I bench/zdiff.py COMPACTC.zkir DAMP.zkir [--normalize] [--show | --multiset]
  --normalize  first apply test/zkir-normalize.py to the first file
  --show       print the instructions of both instead of diffing
  --multiset   ignore order and wiring: list the instructions (variables written `%`) that
               only one side has
"""
import difflib, json, os, subprocess, sys, tempfile
args = [a for a in sys.argv[1:] if not a.startswith('--')]
a, b = args
if '--normalize' in sys.argv:
    n = tempfile.mktemp(suffix='.zkir')
    subprocess.run([sys.executable, '-I', os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'test', 'zkir-normalize.py'), a, n], check=True)
    a = n

def lines(path):
    d = json.load(open(path)); names = {}
    def ren(v):
        if isinstance(v, str) and v.startswith('%'): return names.setdefault(v, '%' + str(len(names)))
        if isinstance(v, list): return [ren(x) for x in v]
        return v
    for x in d.get('inputs', []): ren(x['name'])
    out = []
    for i, ins in enumerate(d['instructions']):
        j = {}
        for k in ('output', 'outputs'):
            if k in ins: j[k] = ren(ins[k])
        for k, v in ins.items():
            if k not in j: j[k] = ren(v)
        op = j.pop('op'); g = j.pop('guard', 'none')
        al = ''
        if 'alignment' in ins:
            al = ' align=' + ','.join(f"{x['value']['tag']}{x['value'].get('length', '')}" if x.get('tag') == 'atom' else json.dumps(x, sort_keys=True) for x in ins['alignment'])
        out.append(f"{op:<19}" + ' '.join(f"{k}={json.dumps(v, separators=(',', ':'), sort_keys=True)}" for k, v in sorted(j.items()) if k != 'alignment')
                   + (f" guard={g}" if g not in ('0x01',) else '') + al)
    return out
la, lb = lines(a), lines(b)
if '--multiset' in sys.argv:
    import collections, re
    sig = lambda ls: collections.Counter(re.sub(r'%\d+', '%', l) for l in ls)
    A, B = sig(la), sig(lb)
    print(f'compactc {len(la)} instructions, damp {len(lb)}')
    for l, n in sorted((A - B).items()): print(f'  only compactc x{n}: {l}')
    for l, n in sorted((B - A).items()): print(f'  only damp     x{n}: {l}')
elif '--show' in sys.argv:
    print(f'--- {a}'); [print(i, l) for i, l in enumerate(la)]
    print(f'--- {b}'); [print(i, l) for i, l in enumerate(lb)]
else:
    print(f'compactc {len(la)} instructions, damp {len(lb)}')
    for l in difflib.unified_diff(la, lb, 'compactc', 'damp', lineterm='', n=1): print(l)
