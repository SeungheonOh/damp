"""Rows of the proof system's table (zkir-v3 mock-compile), per kind of ZKIR instruction.

usage: python3 -I bench/costs.py
         rows each instruction adds: a circuit with 20 copies of one instruction against the
         same circuit with none
       python3 -I bench/costs.py --attribute ROOT VARIANT [--top N] [--json FILE]
         for each circuit under ROOT/VARIANT/*/zkir (VARIANT: compact, opt, o2, o3, noopt), the
         rows attributable to each kind of instruction: every instruction of that kind is
         replaced by `private_input`s for its outputs (a `persistent_hash` together with the
         `bytes_into_natives` that reads it; a `constrain_bits`/`assert` is dropped), and the
         circuit is measured again. The kinds overlap little, so the rest (`base`) is what the
         inputs, ledger instructions and arithmetic cost together. Prints the suite's totals per
         kind and the N circuits with the most rows, each with its kinds.
"""
import glob, json, os, re, subprocess, sys, tempfile
from concurrent.futures import ThreadPoolExecutor
tmp = tempfile.mkdtemp()
def rows(ins):
    d = {'version': {'major': 3, 'minor': 1}, 'do_communications_commitment': False, 'inputs': [
        {'name': '%a', 'type': 'Scalar<BLS12-381>'}, {'name': '%b', 'type': 'Scalar<BLS12-381>'}],
        'outputs': [], 'instructions': ins}
    p = os.path.join(tmp, 'c.zkir'); json.dump(d, open(p, 'w'))
    r = subprocess.run(['zkir-v3', 'mock-compile', p], capture_output=True, text=True)
    return int(re.search(r'rows[^0-9]*([0-9]+)', r.stdout + r.stderr).group(1))
B32 = {'tag': 'atom', 'value': {'tag': 'bytes', 'length': 32}}
def mk(op, i):
    o = f'%o{i}'
    return {
        'test_eq': {'op': 'test_eq', 'a': '%a', 'b': '%b', 'output': o},
        'cond_select': {'op': 'cond_select', 'bit': '%a', 'a': '%b', 'b': '0x01', 'output': o},
        'add': {'op': 'add', 'a': '%a', 'b': '%b', 'output': o},
        'mul': {'op': 'mul', 'a': '%a', 'b': '%b', 'output': o},
        'neg': {'op': 'neg', 'a': '%a', 'output': o},
        'less_than 64': {'op': 'less_than', 'a': '%a', 'b': '%b', 'bits': 64, 'output': o},
        'less_than 128': {'op': 'less_than', 'a': '%a', 'b': '%b', 'bits': 128, 'output': o},
        'constrain_bits 8': {'op': 'constrain_bits', 'val': '%a', 'bits': 8},
        'constrain_bits 64': {'op': 'constrain_bits', 'val': '%a', 'bits': 64},
        'constrain_bits 248': {'op': 'constrain_bits', 'val': '%a', 'bits': 248},
        'constrain_to_boolean': {'op': 'constrain_to_boolean', 'val': '%a'},
        'assert': {'op': 'assert', 'cond': '%a'},
        'private_input': {'op': 'private_input', 'type': 'Scalar<BLS12-381>', 'output': o, 'guard': None},
        'public_input': {'op': 'public_input', 'type': 'Scalar<BLS12-381>', 'output': o, 'guard': None},
        'copy': {'op': 'copy', 'val': '%a', 'output': o},
        'transient_hash (2 in)': {'op': 'transient_hash', 'inputs': ['%a', '%b'], 'output': o},
        'persistent_hash (2 x Bytes<32>)': {'op': 'persistent_hash', 'alignment': [B32, B32], 'inputs': ['%a', '%b', '%a', '%b'], 'output': o},
        'div_mod_power_of_two 16': {'op': 'div_mod_power_of_two', 'val': '%a', 'bits': 16, 'outputs': [o, o + 'r']},
        'div_mod_power_of_two 248': {'op': 'div_mod_power_of_two', 'val': '%a', 'bits': 248, 'outputs': [o, o + 'r']},
        'bytes_into_natives (Bytes<32>)': None,
    }[op]
def rows_of(d, name):
    p = os.path.join(tmp, name + '.zkir'); json.dump(d, open(p, 'w'))
    r = subprocess.run(['zkir-v3', 'mock-compile', p], capture_output=True, text=True)
    for b in glob.glob(os.path.join(tmp, name + '.bzkir')): os.remove(b)
    m = re.search(r'rows[^0-9]*([0-9]+)', r.stdout + r.stderr)
    return int(m.group(1)) if m else None

def kind(i):
    op = i['op']
    if op == 'constrain_bits': return f"constrain_bits {i['bits']}"
    if op == 'less_than': return f"less_than {i['bits']}"
    if op == 'div_mod_power_of_two': return f"div_mod {i['bits']}"
    return op

COSTLY = ('persistent_hash', 'transient_hash', 'div_mod', 'constrain_bits', 'less_than', 'constrain_to_boolean',
          'test_eq', 'cond_select', 'ec_', 'hash_to_curve', 'bytes_into_natives', 'assert')

def without(d, k):
    """The circuit with every instruction of kind `k` replaced by private inputs for its outputs."""
    out, hashed = [], set()
    pi = lambda o: {'op': 'private_input', 'type': 'Scalar<BLS12-381>', 'output': o, 'guard': None}
    for i in d['instructions']:
        if kind(i) == k or (k == 'persistent_hash' and i['op'] == 'bytes_into_natives' and i['bytes'] in hashed):
            if i['op'] == 'persistent_hash': hashed.add(i['output']); continue
            os_ = [i['output']] if 'output' in i else i.get('outputs', [])
            out += [pi(o) for o in os_]
            continue
        out.append(i)
    return {**d, 'instructions': out}

def attribute(path, key):
    d = json.load(open(path))
    base = rows_of(d, key)
    kinds = sorted({kind(i) for i in d['instructions'] if kind(i).startswith(COSTLY)} - {'bytes_into_natives'})
    res = {}
    for k in kinds:
        r = rows_of(without(d, k), f'{key}.{k}')
        if r is not None: res[k] = {'n': sum(kind(i) == k for i in d['instructions']), 'rows': base - r}
    return {'rows': base, 'instructions': len(d['instructions']), 'kinds': res}

if '--attribute' in sys.argv:
    a = sys.argv.index('--attribute'); root, variant = sys.argv[a + 1], sys.argv[a + 2]
    top = int(sys.argv[sys.argv.index('--top') + 1]) if '--top' in sys.argv else 10
    files = [(os.path.relpath(p, os.path.join(root, variant)).replace('/zkir/', '.')[:-5], p)
             for p in sorted(glob.glob(os.path.join(root, variant, '*', 'zkir', '*.zkir')))]
    with ThreadPoolExecutor(16) as ex: res = dict(zip([k for k, _ in files], ex.map(lambda f: attribute(f[1], f[0]), files)))
    if '--json' in sys.argv: json.dump(res, open(sys.argv[sys.argv.index('--json') + 1], 'w'), indent=1)
    total = sum(r['rows'] or 0 for r in res.values())
    per = {}
    for r in res.values():
        for k, x in r['kinds'].items():
            p = per.setdefault(k, [0, 0]); p[0] += x['n']; p[1] += x['rows']
    print(f"{variant}: {len(res)} circuits, {total} rows. Rows attributable to each kind of instruction (summed over circuits):")
    print(f"  {'kind':<28}{'count':>7}{'rows':>10}{'share':>8}")
    for k, (n, r) in sorted(per.items(), key=lambda x: -x[1][1]):
        print(f"  {k:<28}{n:>7}{r:>10}{100 * r / total:>7.1f}%")
    print(f"\nThe {top} circuits with the most rows:")
    for key, r in sorted(res.items(), key=lambda x: -(x[1]['rows'] or 0))[:top]:
        ks = ', '.join(f"{k} x{x['n']}: {x['rows']}" for k, x in sorted(r['kinds'].items(), key=lambda x: -x[1]['rows']) if x['rows'])
        print(f"  {key:<40}{r['rows']:>8}  {ks}")
    sys.exit(0)

base = rows([{'op': 'test_eq', 'a': '%a', 'b': '%b', 'output': '%z'}])
print(f'{"instruction":<34}rows each')
for op in ['test_eq', 'cond_select', 'add', 'mul', 'neg', 'copy', 'assert', 'constrain_to_boolean', 'constrain_bits 8', 'constrain_bits 64',
           'constrain_bits 248', 'less_than 64', 'less_than 128', 'div_mod_power_of_two 16', 'div_mod_power_of_two 248', 'private_input',
           'public_input', 'transient_hash (2 in)', 'persistent_hash (2 x Bytes<32>)']:
    n = 20
    r = rows([{'op': 'test_eq', 'a': '%a', 'b': '%b', 'output': '%z'}] + [mk(op, i) for i in range(n)])
    print(f'{op:<34}{(r - base) / n:g}')
