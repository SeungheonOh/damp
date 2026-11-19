"""How much is left to remove from a ZKIR circuit that an optimizer could remove?

usage: python3 -I bench/headroom.py ROOT VARIANT [--json FILE]

For each circuit under ROOT/VARIANT/*/zkir (VARIANT: compact, opt, o2, noopt) apply, one at a
time and then all together, rewrites that a sound optimizer could perform, write the result to a
scratch file and measure the circuit again (instructions, and rows from `zkir-v3 mock-compile`):

  dead      pure instructions whose results nothing uses
  cse       a pure instruction repeating an earlier one (same operation, same operands)
  fold      arithmetic on constants, `x + 0`, `x * 1`, `x * 0`, `cond_select` with a constant
            selector or equal branches, `test_eq x x`, `copy`
  bits      `constrain_bits` / `constrain_to_boolean` of a value already known to fit (a comparison
            result, a constant, a value already constrained to as many bits)
  hashes    `persistent_hash` / `transient_hash` / `div_mod_power_of_two` whose inputs are all constants
            (the value could be computed when the circuit is built; here the output is replaced by
            some constant, which leaves the row count unchanged)
  reads     a ledger read (a `public_input` and the `impact` instructions that check it) repeating an
            earlier read of the same path under the same guard, with no other `impact` between
  merge     adjacent `impact` instructions with the same guard joined into one
            (instructions only: it should not change the rows)

The rewrites are applied to the circuit as a graph; nothing is run, so "could" means "if the
rewrite is sound for that circuit". Soundness is the optimizer's job (Damp/Optimize/*).
"""
import glob, json, os, re, subprocess, sys, tempfile
from concurrent.futures import ThreadPoolExecutor

R = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
root, variant = sys.argv[1], sys.argv[2]
out_json = sys.argv[sys.argv.index('--json') + 1] if '--json' in sys.argv else None
tmp = tempfile.mkdtemp()

PURE = {'add', 'mul', 'neg', 'test_eq', 'less_than', 'cond_select', 'copy', 'transient_hash',
        'persistent_hash', 'div_mod_power_of_two', 'bytes_into_natives'}

def isvar(v): return isinstance(v, str) and v.startswith('%')
def isconst(v): return isinstance(v, str) and v.startswith('0x')
def cval(v): return int.from_bytes(bytes.fromhex(v[2:]), 'little') % R
def cstr(n):
    n %= R
    b = n.to_bytes((n.bit_length() + 7) // 8 or 1, 'little')
    return '0x' + b.hex()

def outs(i): return [i['output']] if 'output' in i else i.get('outputs', [])
def operands(i):
    r = []
    for k, v in i.items():
        if k in ('op', 'output', 'outputs', 'type', 'bits', 'alignment'): continue
        r += [x for x in (v if isinstance(v, list) else [v]) if isvar(x)]
    return r

def substitute(ins, ren):
    sub = lambda v: ren.get(v, v) if isinstance(v, str) else [sub(x) for x in v] if isinstance(v, list) else v
    return {k: sub(v) for k, v in ins.items()}

def dead(d):
    ins = list(d['instructions'])
    while True:
        used = set(x for i in ins for x in operands(i)) | set(x for o in d.get('outputs', []) for x in [o] if isvar(x))
        keep = [i for i in ins if not (i['op'] in PURE and outs(i) and all(o not in used for o in outs(i)))]
        if len(keep) == len(ins): return {**d, 'instructions': keep}
        ins = keep

def cse(d):
    ren, seen, out = {}, {}, []
    for i in d['instructions']:
        i = substitute(i, ren)
        if i['op'] in PURE:
            body = {k: v for k, v in i.items() if k not in ('output', 'outputs')}
            if i['op'] in ('add', 'mul', 'test_eq'): body['ab'] = sorted([str(body.pop('a')), str(body.pop('b'))])
            key = json.dumps(body, sort_keys=True)
            if key in seen:
                for a, b in zip(outs(i), outs(seen[key])): ren[a] = b
                continue
            seen[key] = i
        out.append(i)
    return {**d, 'instructions': out, 'outputs': [ren.get(o, o) if isvar(o) else o for o in d.get('outputs', [])]}

def fold(d):
    ren, out = {}, []
    for i in d['instructions']:
        i = substitute(i, ren); op = i['op']; new = None
        if op == 'copy': new = i['val']
        elif op == 'add' and isconst(i['a']) and cval(i['a']) == 0: new = i['b']
        elif op == 'add' and isconst(i['b']) and cval(i['b']) == 0: new = i['a']
        elif op == 'mul' and ((isconst(i['a']) and cval(i['a']) == 1)): new = i['b']
        elif op == 'mul' and ((isconst(i['b']) and cval(i['b']) == 1)): new = i['a']
        elif op == 'mul' and any(isconst(i[k]) and cval(i[k]) == 0 for k in 'ab'): new = '0x00'
        elif op in ('add', 'mul') and isconst(i['a']) and isconst(i['b']):
            new = cstr(cval(i['a']) + cval(i['b']) if op == 'add' else cval(i['a']) * cval(i['b']))
        elif op == 'neg' and isconst(i['a']): new = cstr(-cval(i['a']))
        elif op == 'test_eq' and (i['a'] == i['b'] or (isconst(i['a']) and isconst(i['b']))):
            new = '0x01' if (i['a'] == i['b'] or cval(i['a']) == cval(i['b'])) else '0x00'
        elif op == 'less_than' and isconst(i['a']) and isconst(i['b']): new = '0x01' if cval(i['a']) < cval(i['b']) else '0x00'
        elif op == 'cond_select':
            if isconst(i['bit']): new = i['a'] if cval(i['bit']) else i['b']
            elif i['a'] == i['b']: new = i['a']
        if new is None: out.append(i)
        else: ren[i['output']] = new
    return {**d, 'instructions': out, 'outputs': [ren.get(o, o) if isvar(o) else o for o in d.get('outputs', [])]}

def bits(d):
    """Remove range checks of values that already fit."""
    known, out = {}, []     # variable -> number of bits it is known to fit in (1 for booleans)
    for i in d['instructions']:
        op = i['op']
        if op in ('test_eq', 'less_than'): known[i['output']] = 1
        elif op == 'cond_select' and all(isconst(i[k]) and cval(i[k]) <= 1 or known.get(i[k], 99) <= 1 for k in 'ab'):
            known[i['output']] = 1
        if op in ('constrain_bits', 'constrain_to_boolean'):
            n = i['bits'] if op == 'constrain_bits' else 1; v = i['val']
            have = 1 if isconst(v) and cval(v) <= 1 else known.get(v, 999)
            if isconst(v) and cval(v).bit_length() <= n: continue
            if have <= n: continue
            known[v] = min(known.get(v, 999), n)
        out.append(i)
    return {**d, 'instructions': out}

def merge(d):
    out = []
    for i in d['instructions']:
        if out and i['op'] == 'impact' and out[-1]['op'] == 'impact' and out[-1].get('guard') == i.get('guard'):
            out[-1] = {**out[-1], 'inputs': out[-1]['inputs'] + i['inputs']}
        else: out.append(dict(i))
    return {**d, 'instructions': out}

def hashes(d):
    ren, out, cbytes = {}, [], set()
    for i in d['instructions']:
        i = substitute(i, ren); op = i['op']
        if op in ('persistent_hash', 'transient_hash') and all(isconst(x) for x in i['inputs']):
            if op == 'transient_hash': ren[i['output']] = '0x01'
            else: cbytes.add(i['output'])
            continue
        if op == 'bytes_into_natives' and i['bytes'] in cbytes:
            for o in i['outputs']: ren[o] = '0x01'
            continue
        if op == 'div_mod_power_of_two' and isconst(i['val']):
            v = cval(i['val']); ren[i['outputs'][0]] = cstr(v >> i['bits']); ren[i['outputs'][1]] = cstr(v & ((1 << i['bits']) - 1))
            continue
        out.append(i)
    return {**d, 'instructions': out, 'outputs': [ren.get(o, o) if isvar(o) else o for o in d.get('outputs', [])]}

def reads(d):
    ins, out, seen, ren, i = d['instructions'], [], {}, {}, 0
    sub = lambda v: ren.get(v, v) if isinstance(v, str) else [sub(x) for x in v] if isinstance(v, list) else v
    while i < len(ins):
        x = {k: sub(v) for k, v in ins[i].items()}
        if x['op'] == 'public_input':
            v = x['output']; j = i + 1; grp = []
            while j < len(ins) and ins[j]['op'] == 'impact':
                grp.append(ins[j]); j += 1
                if v in ins[j - 1]['inputs']: break
            if grp and v in grp[-1]['inputs']:
                key = json.dumps([x.get('guard'), [[('%' if a == v else a) for a in g['inputs']] + [g.get('guard')] for g in grp]])
                if key in seen: ren[v] = seen[key]
                else: seen[key] = v; out.append(x); out += [{k: sub(v2) for k, v2 in g.items()} for g in grp]
                i = j; continue
        if x['op'] == 'impact': seen.clear()
        out.append(x); i += 1
    return {**d, 'instructions': out}

TRANSFORMS = {'dead': dead, 'cse': cse, 'fold': fold, 'bits': bits, 'reads': reads, 'hashes': hashes, 'merge': merge}
def everything(d):
    for _ in range(3):
        for f in (fold, hashes, cse, bits, reads, dead): d = f(d)
    return merge(d)
TRANSFORMS['all'] = everything

def rows_of(d, name):
    p = os.path.join(tmp, name + '.zkir'); json.dump(d, open(p, 'w'))
    r = subprocess.run(['zkir-v3', 'mock-compile', p], capture_output=True, text=True)
    for b in glob.glob(os.path.join(tmp, name + '.bzkir')): os.remove(b)
    m = re.search(r'rows[^0-9]*([0-9]+)', r.stdout + r.stderr)
    return int(m.group(1)) if m else None

def job(args):
    key, path = args
    d = json.load(open(path))
    base = rows_of(d, key + '.base')
    res = {'instructions': len(d['instructions']), 'rows': base}
    for name, f in TRANSFORMS.items():
        e = f(d)
        res[name] = {'instructions': len(d['instructions']) - len(e['instructions']),
                     'rows': None if base is None else base - (rows_of(e, f'{key}.{name}') or base)}
    return key, res

files = [(os.path.relpath(p, os.path.join(root, variant)).replace('/zkir/', '.')[:-5], p)
         for p in sorted(glob.glob(os.path.join(root, variant, '*', 'zkir', '*.zkir')))]
with ThreadPoolExecutor(16) as ex: results = dict(ex.map(job, files))
if out_json: json.dump(results, open(out_json, 'w'), indent=1)

names = list(TRANSFORMS)
print(f"{variant}: instructions and rows an optimizer could still remove, per rewrite (each alone, then all); circuits where only `merge` applies are not listed\n")
print(f"{'circuit':<46}{'size':>8}{'rows':>9}  " + ''.join(f"{n:>13}" for n in names))
tot = {n: [0, 0] for n in names}; ti = tr = 0
for k, r in results.items():
    ti += r['instructions']; tr += r['rows'] or 0
    if any(r[n]['instructions'] or r[n]['rows'] for n in names if n not in ('merge', 'all')):
        print(f"{k:<46}{r['instructions']:>8}{r['rows']:>9}  " + ''.join(f"{r[n]['instructions']:>6}/{r[n]['rows'] or 0:<6}" for n in names))
    for n in names: tot[n][0] += r[n]['instructions']; tot[n][1] += r[n]['rows'] or 0
print(f"{'TOTAL':<46}{ti:>8}{tr:>9}  " + ''.join(f"{tot[n][0]:>6}/{tot[n][1]:<6}" for n in names))
