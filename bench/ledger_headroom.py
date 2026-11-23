"""Ledger-level rewrites left in a build: how many, and what they would save.

usage: python3 -I bench/ledger_headroom.py BUILD_DIR [--rows] [--json FILE]
       python3 -I bench/ledger_headroom.py BUILD_DIR --classes [--rows] [--sim OUT] [--no-dead] [--no-reads] [--sound]
       python3 -I bench/ledger_headroom.py BUILD_DIR --merge OUT [all|simple|nocache|seq|seqgap]

`--classes` (for a `--ledger-opt` build: what the passes still leave) replays the extended
`ledgerReuse`/`ledgerDeadStore` on each circuit with the frame analysis of
Damp/Optimize/LedgerFrame.lean (ported: `frame_keeps`) and counts, per class, the reads that a fact
would answer and the writes that a later write overwrites:

  R:read[+frame]            a repeated read (`+frame`: across writes the frame analysis allows)
  R:cellwrite[+frame]       a read of a cell after a cell write of it
  R:mapinsert[...]          a lookup (two `idx`) after a map insert of the same key
  R:...+BIG / +MULTILIMB    the same, blocked by the operand size cap / a byte string over 31 bytes
  D:dead[+guard|+constvalue|+multiatom][+across-reads|+across-other|+across-root-writes]
                            a cell write overwritten by a later one of the same key; what lies between
  blocked.*                 writes whose fact is blocked (multi-limb, operand size)

With `--rows` the rewrites are applied to the ZKIR (reads renamed, dropped statements' impacts and
public inputs removed) and measured with `zkir-v3 mock-compile`; with `--sim OUT` the rewritten
contract.json and ZKIR are written to OUT (a build directory `executor/test/ledger-opt.mjs` can run
against, for gas: give it a directory holding `o2` = the input build and `lo` = OUT).

`--merge OUT` writes to OUT a copy of the build whose adjacent ledger statements with the same guard
are merged into one program (when the second does not use what the first reads): `all`, or only
plain reads and cell writes (`simple`), or only programs without cached instructions, branches or
swaps (`nocache`), or the class `Circuit.ledgerMerge` proves sound (`seq`: the analysis `mcheck` of
Damp/Optimize/LedgerMerge.lean ported; `seqgap`: also across statements that are not ledger
statements and commute with the second, which is what the pass does). The ZKIR is unchanged, so only
gas differs (`LO_ALL=1 node test/ledger-opt.mjs DIR` counts every call, DIR holding `o2` = the input
build and `lo` = OUT).

BUILD_DIR is a `damp-bench` output directory (one sub-directory per contract, each with
`contract.json` and `zkir/`). For every circuit the ledger statements of `contract.json` are
scanned in order and the following opportunities counted:

  a   repeated read: a reading statement (`dup 0; idx ...; ...; popeq`, or a call-context read
      `dup 2; idx ...; popeq`) whose instructions, operands included, equal an earlier reading
      statement's, with no statement between that may write the same top-level field.
      `a.same` the guards are the same expression; `a.dom` the earlier guard is the constant 1.
      `a.strict`: `a.same` with no ledger statement at all between that is not itself a read.
  b   read after write: a cell read of a field (or a map lookup of a key) whose last write in
      the circuit is a cell write of that field (a map insert of that key, the same key
      expression), same alignment, nothing between that may write it.
  c   dead store: a cell write overwritten by a later cell write of the same field, no read of
      it (and no statement that may read it) between.
  d   adjacent ledger statements with the same guard and nothing between (could be one program).
  e   `member` of a key followed, nothing writing the map between, by a `lookup` of that key.

Field of a statement: the first key of the first path (`idx`/pushed key); statements reading the
call context (`dup 2`) touch field `ctx`, which no query changes; statements beginning with
`swap 0` write the effects (`eff`). Anything else that writes is assumed to touch every field.

With `--rows`, the `a.same` and `b` rewrites are applied to the emitted ZKIR (the impacts and
public inputs of the removed statement dropped, its reads renamed to the earlier read / the
written operand) and measured with `zkir-v3 mock-compile`.
"""
import collections, copy, glob, json, os, re, shutil, subprocess, sys, tempfile

root = sys.argv[1]
want_rows = '--rows' in sys.argv
out_json = sys.argv[sys.argv.index('--json') + 1] if '--json' in sys.argv else None
tmp = tempfile.mkdtemp()

def canon(x): return json.dumps(x, sort_keys=True)

def blank(op):
    return {**op, 'result': []} if op['kind'] == 'popeq' else op

def kinds(ops): return [o['kind'] for o in ops]

def is_read(s):
    ops = s['ops']
    return (len(ops) >= 3 and ops[0]['kind'] == 'dup' and ops[0]['n'] in (0, 2)
            and ops[1]['kind'] == 'idx' and not ops[1]['pushPath'] and ops[-1]['kind'] == 'popeq'
            and all(o['kind'] in ('idx', 'push', 'size', 'member', 'eq', 'lt', 'neg', 'type', 'root', 'popeq')
                    and not o.get('pushPath') for o in ops[1:])
            and sum(o['kind'] == 'popeq' for o in ops) == 1)

def read_field(s):
    ops = s['ops']
    if ops[0]['n'] == 2: return 'ctx'
    return canon(ops[1]['path'][0])

def write_field(s):
    ops = s['ops']
    if not ops: return None
    if ops[0]['kind'] == 'swap': return 'eff'
    if ops[0]['kind'] == 'idx' and ops[0]['pushPath']: return canon(ops[0]['path'][0])
    if ops[0]['kind'] == 'push' and len(ops) >= 3 and ops[-1]['kind'] == 'ins' and not any(
            o['kind'] in ('dup', 'swap') for o in ops):
        return canon(ops[0]['value'])
    return '*'

def cell_write(s):
    """(field, value aligned) of `push key; push value; ins 1`."""
    ops = s['ops']
    if kinds(ops) == ['push', 'push', 'ins'] and ops[2]['n'] == 1 and not ops[2]['cached']:
        return canon(ops[0]['value']), ops[1]['value']
    return None

def map_insert(s):
    """(path, key, value) of `idx P path; push key; push value; ins 1; ins 1` (plain value)."""
    ops = s['ops']
    if kinds(ops) == ['idx', 'push', 'push', 'ins', 'ins'] and ops[0]['pushPath'] and len(ops[0]['path']) == 1:
        return canon(ops[0]['path']), canon(ops[1]['value']), ops[2]['value']
    return None

def cell_read(s):
    ops = s['ops']
    if kinds(ops) == ['dup', 'idx', 'popeq'] and ops[0]['n'] == 0 and len(ops[1]['path']) == 1:
        return canon(ops[1]['path'][0]), ops[2]['align']
    return None

def map_lookup(s):
    ops = s['ops']
    if kinds(ops) == ['dup', 'idx', 'idx', 'popeq'] and ops[0]['n'] == 0 and len(ops[1]['path']) == 1 \
            and len(ops[2]['path']) == 1:
        return canon(ops[1]['path']), canon(ops[2]['path'][0]), ops[3]['align']
    return None

def map_member(s):
    ops = s['ops']
    if kinds(ops) == ['dup', 'idx', 'push', 'member', 'popeq'] and len(ops[1]['path']) == 1:
        return canon(ops[1]['path']), canon(ops[2]['value'])
    return None

ONE = canon({'kind': 'const', 'value': '1'})

def analyse(c):
    res = {k: 0 for k in ('ledger', 'reads', 'a.same', 'a.dom', 'a.strict', 'b', 'c', 'd', 'e')}
    a_pairs, b_pairs = [], []        # (removed statement index, earlier statement index / value)
    avail = {}                        # key -> (stmt index, guard, field, clean)
    last_write = {}                   # field -> (stmt index, guard, value aligned) for cell writes
    last_ins = {}                     # (path, key) -> (stmt index, guard, value)
    pending_store = {}                # field -> (stmt index, guard)
    members = {}                      # (path, key) -> stmt index
    prev_ledger = None                # (index into body, guard) of the previous statement if it was a ledger one
    body = c['body']
    li = -1
    for bi, s in enumerate(body):
        if s['kind'] != 'ledger':
            prev_ledger = None
            continue
        if not s['ops']:
            continue
        li += 1
        res['ledger'] += 1
        g = canon(s['guard'])
        if prev_ledger is not None and prev_ledger[1] == g:
            res['d'] += 1
        prev_ledger = (bi, g)
        if is_read(s):
            res['reads'] += 1
            f = read_field(s)
            key = canon([blank(o) for o in s['ops']])
            hit = avail.get(key)
            if hit is not None:
                if hit[1] == g:
                    res['a.same'] += 1; a_pairs.append((li, hit[0]))
                    if hit[3]: res['a.strict'] += 1
                elif hit[1] == ONE:
                    res['a.dom'] += 1
            else:
                avail[key] = (li, g, f, True)
            cr = cell_read(s)
            if cr and cr[0] in last_write and (last_write[cr[0]][1] == g or last_write[cr[0]][1] == ONE) \
                    and last_write[cr[0]][2]['align'] == cr[1]:
                res['b'] += 1; b_pairs.append((li, last_write[cr[0]][0], len(last_write[cr[0]][2]['vals'])))
            ml = map_lookup(s)
            if ml and (ml[0], ml[1]) in last_ins and last_ins[(ml[0], ml[1])][2]['align'] == ml[2] \
                    and last_ins[(ml[0], ml[1])][1] in (g, ONE):
                res['b'] += 1
            if ml and (ml[0], ml[1]) in members:
                res['e'] += 1
            mm = map_member(s)
            if mm: members[mm] = li
            pending_store.pop(f, None)
            continue
        # a statement that may write
        f = write_field(s)
        for k in list(avail):
            i, gg, ff, clean = avail[k]
            if f == '*' or ff == f: del avail[k]
            else: avail[k] = (i, gg, ff, False)
        for d_ in (last_write, pending_store):
            for k in list(d_):
                if f == '*' or k == f: del d_[k]
        for k in list(last_ins):
            if f == '*' or json.loads(k[0])[0] == json.loads(f if f not in ('*', 'eff', 'ctx') else 'null'): del last_ins[k]
        for k in list(members):
            if f == '*' or json.loads(k[0])[0] == json.loads(f if f not in ('*', 'eff', 'ctx') else 'null'): del members[k]
        cw = cell_write(s)
        if cw:
            last_write[cw[0]] = (li, g, cw[1])
        mi = map_insert(s)
        if mi: last_ins[(mi[0], mi[1])] = (li, g, mi[2])
    return res, a_pairs, b_pairs

def analyse_c(c):
    """Dead stores, separately: a cell write overwritten before any statement that may read it."""
    n = 0
    open_ = {}
    for s in c['body']:
        if s['kind'] != 'ledger' or not s['ops']: continue
        g = canon(s['guard'])
        cw = cell_write(s)
        if cw:
            if cw[0] in open_ and (open_[cw[0]] == g or g == ONE): n += 1
            open_[cw[0]] = g
            continue
        if is_read(s):
            f = read_field(s); open_.pop(f, None); continue
        f = write_field(s)
        if f == '*': open_.clear()
        else: open_.pop(f, None)   # a write through a longer path reads the field first
    return n

# ---------------------------------------------------------------- ZKIR rewriting for rows

def zkir_blocks(z, c):
    """The ZKIR instructions of each non-empty ledger statement: (impact indices, public_input indices)."""
    ins = z['instructions']
    imp = [i for i, x in enumerate(ins) if x['op'] == 'impact']
    blocks, k = [], 0
    for s in c['body']:
        if s['kind'] != 'ledger' or not s['ops']: continue
        idxs = imp[k:k + len(s['ops'])]; k += len(s['ops'])
        outs = set(a for j in idxs for a in ins[j]['inputs'] if isinstance(a, str) and a.startswith('%'))
        pis = [i for i, x in enumerate(ins) if x['op'] == 'public_input' and x['output'] in outs]
        reads = [a for a in ins[idxs[-1]]['inputs'] if isinstance(a, str) and a.startswith('%') and
                 any(ins[p]['output'] == a for p in pis)] if idxs else []
        blocks.append((idxs, pis, reads))
    assert k == len(imp), (k, len(imp))
    return blocks

def rewrite(z, blocks, removals):
    """removals: statement index -> list of replacement names for its reads (or None to keep names)."""
    ins = z['instructions']
    drop, ren = set(), {}
    for li, repl in removals.items():
        idxs, pis, reads = blocks[li]
        drop |= set(idxs) | set(pis)
        if repl is not None:
            for a, b in zip(reads, repl): ren[a] = b
    def sub(v):
        if isinstance(v, str): return ren.get(v, v)
        if isinstance(v, list): return [sub(x) for x in v]
        return v
    out = [{k: sub(v) for k, v in x.items()} for i, x in enumerate(ins) if i not in drop]
    return {**z, 'instructions': out}

def rows_of(d, name):
    p = os.path.join(tmp, name + '.zkir'); json.dump(d, open(p, 'w'))
    r = subprocess.run(['zkir-v3', 'mock-compile', p], capture_output=True, text=True)
    for b in glob.glob(os.path.join(tmp, name + '.bzkir')): os.remove(b)
    m = re.search(r'rows[^0-9]*([0-9]+)', r.stdout + r.stderr)
    return int(m.group(1)) if m else None

def main():
    tot = {}
    per = []
    for cj in sorted(glob.glob(os.path.join(root, '*', 'contract.json'))):
        cname = os.path.basename(os.path.dirname(cj))
        d = json.load(open(cj))
        for c in d['circuits']:
            res, a_pairs, b_pairs = analyse(c)
            res['c'] = analyse_c(c)
            row = {'circuit': f'{cname}.{c["name"]}', **res}
            zp = os.path.join(os.path.dirname(cj), 'zkir', c['name'] + '.zkir')
            if want_rows and os.path.exists(zp) and (a_pairs or b_pairs):
                z = json.load(open(zp))
                blocks = zkir_blocks(z, c)
                base = rows_of(z, 'base')
                row['rows'] = base
                if a_pairs:
                    rem = {li: blocks[e][2] for li, e in a_pairs}
                    row['rows.a'] = base - rows_of(rewrite(z, blocks, rem), 'a')
                    row['instr.a'] = len(z['instructions']) - len(rewrite(z, blocks, rem)['instructions'])
                if b_pairs:
                    remb = {li: [z['instructions'][blocks[w][0][1]]['inputs'][-n:] for _ in [0]][0] for li, w, n in b_pairs}
                    zb = rewrite(z, blocks, remb)
                    row['rows.b'] = base - rows_of(zb, 'b')
                    row['instr.b'] = len(z['instructions']) - len(zb['instructions'])
                    remab = {**remb, **{li: blocks[e][2] for li, e in a_pairs if li not in remb}}
                    row['rows.ab'] = base - rows_of(rewrite(z, blocks, remab), 'ab')
            per.append(row)
            for k, v in res.items(): tot[k] = tot.get(k, 0) + v
            for k in ('rows.a', 'instr.a', 'rows.b', 'instr.b', 'rows.ab'):
                if k in row: tot[k] = tot.get(k, 0) + row[k]
    for r in per:
        if any(r[k] for k in ('a.same', 'a.dom', 'b', 'c', 'e')):
            print(r)
    print('circuits', len(per))
    print('total', tot)
    if out_json: json.dump({'circuits': per, 'total': tot}, open(out_json, 'w'), indent=1)


# ================================================================== --classes
P = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
sim_out = sys.argv[sys.argv.index('--sim') + 1] if '--sim' in sys.argv else None
only = sys.argv[sys.argv.index('--only') + 1].split(',') if '--only' in sys.argv else None

def expr_vars(e, acc):
    if isinstance(e, dict):
        if e.get('kind') == 'var': acc.add(e['var'])
        for k, v in e.items():
            if k != 'kind': expr_vars(v, acc)
    elif isinstance(e, list):
        for x in e: expr_vars(x, acc)
    return acc

def esize(e):
    if isinstance(e, dict):
        return 1 + sum(esize(v) for k, v in e.items() if isinstance(v, (dict, list)))
    if isinstance(e, list): return sum(esize(x) for x in e)
    return 0

def single_limb(al): return all(a['kind'] != 'bytes' or a['length'] <= 31 for a in al)

def const_key(a):
    """AV atoms of a constant single-limb aligned key, or None."""
    if len(a['vals']) != len(a['align']) or not single_limb(a['align']): return None
    if not all(v['kind'] == 'const' for v in a['vals']): return None
    return (canon(a['align']), tuple(int(v['value']) % P for v in a['vals']))

def same_key(k1, k2): return k1 == k2
def distinct_key(k1, k2): return k1[1] != k2[1]

# ------------------------------------------------------------------ the frame checker
def frame_keeps(pi, ops, strict=False):
    """pi: list of const keys (AV-level). True if a successful run of ops leaves svWalk state pi unchanged."""
    m = len(pi)
    def keytag(a):
        k = const_key(a)
        return ('key', k) if k else ('oth',)
    def step(t, kt):
        if t[0] == 'pre' and kt[0] == 'key' and same_key(kt[1], pi[t[1]]) and t[1] + 1 < m:
            return ('pre', t[1] + 1)
        return ('oth',)
    budget = [0]
    def run(i, ts):
        budget[0] += 1
        if budget[0] > 4096: return False
        while i < len(ops):
            o = ops[i]; k = o['kind']; i += 1
            if k == 'dup':
                if o['n'] >= len(ts): return False
                ts = [ts[o['n']]] + ts
            elif k == 'swap':
                n = o['n'] + 1
                if n >= len(ts): return False
                ts = list(ts); ts[0], ts[n] = ts[n], ts[0]
            elif k in ('idx', 'idxStack'):
                path = o['path']
                keys = [keytag(a) for a in path]
                if k == 'idxStack':
                    if not ts: return False
                    keys.append(ts[0]); ts = ts[1:]
                if not ts: return False
                curr, ts = ts[0], ts[1:]
                push = k == 'idx' and o['pushPath']
                for kt in keys:
                    if push: ts = [kt, curr] + ts
                    curr = step(curr, kt)
                ts = [curr] + ts
            elif k == 'ins':
                if len(ts) < 2 * o['n'] + 1: return False
                curr, ts = ts[0], ts[1:]
                for _ in range(o['n']):
                    key, cont, ts = ts[0], ts[1], ts[2:]
                    if cont[0] == 'pre':
                        if strict: return False
                        d = cont[1]
                        if key[0] != 'key': return False
                        if same_key(key[1], pi[d]):
                            if curr != ('pre', d + 1): return False
                        elif not distinct_key(key[1], pi[d]): return False
                        curr = cont
                    else:
                        curr = ('oth',)
                ts = [curr] + ts
            elif k == 'rem':
                if len(ts) < 2: return False
                key, cont, ts = ts[0], ts[1], ts[2:]
                if cont[0] == 'pre':
                    if strict: return False
                    if key[0] != 'key' or not distinct_key(key[1], pi[cont[1]]): return False
                    ts = [cont] + ts
                else: ts = [('oth',)] + ts
            elif k == 'push':
                ts = [keytag(o['value'])] + ts
            elif k in ('pushNull', 'pushState'):
                ts = [('oth',)] + ts
            elif k == 'branch':
                if not ts: return False
                ts = ts[1:]
                if not run(i + o['skip'], ts): return False
            elif k == 'jmp':
                i += o['skip']
            elif k in ('popeq', 'pop', 'log'):
                if not ts: return False
                ts = ts[1:]
            elif k in ('lt', 'eq', 'and', 'or', 'add', 'sub', 'concat', 'concatCached', 'member'):
                if len(ts) < 2: return False
                ts = [('oth',)] + ts[2:]
            elif k in ('type', 'size', 'neg', 'root', 'addi', 'subi'):
                if not ts: return False
                ts = [('oth',)] + ts[1:]
            elif k == 'ckpt':
                pass
            else:
                return False
        return len(ts) > 0 and ts[0] == ('pre', 0)
    return run(0, [('pre', 0), ('oth',), ('oth',)])

def touches_root(ops):
    """Does the program ins/rem into the contract-state root at all? (frame with an impossible key)"""
    return not frame_keeps([('X', ('never',))], ops, strict=True)

# ------------------------------------------------------------------ shapes
def plain_read(s):
    ops = s['ops']; rs = s['reads']
    if len(ops) < 3 or ops[0]['kind'] != 'dup' or ops[0]['n'] > 2 or ops[-1]['kind'] != 'popeq': return None
    n = ops[0]['n']
    mids = ops[1:-1]
    if not all(o['kind'] == 'idx' and not o['pushPath'] and (not o['cached'] or n >= 1) for o in mids): return None
    if len(mids) > 1 and n != 0: pass
    pop = ops[-1]
    if not rs or [r.get('var') for r in pop['result']] != rs or len(set(rs)) != len(rs): return None
    path = [a for o in mids for a in o['path']]
    if expr_vars(path, set()) & set(rs): return None
    return n, path, len(mids), pop['align']

def cell_write2(s):
    ops = s['ops']
    if [o['kind'] for o in ops] == ['push', 'push', 'ins'] and not ops[0]['storage'] and ops[1]['storage'] \
            and ops[2]['n'] == 1 and not ops[2]['cached']:
        return ops[0]['value'], ops[1]['value']
    return None

def map_insert2(s):
    ops = s['ops']
    if [o['kind'] for o in ops] == ['idx', 'push', 'push', 'ins', 'ins'] and ops[0]['pushPath'] and not ops[0]['cached'] \
            and len(ops[0]['path']) == 1 and not ops[1]['storage'] and ops[2]['storage'] \
            and ops[3]['n'] == 1 and not ops[3]['cached'] and ops[4]['n'] == 1 and ops[4]['cached']:
        return ops[0]['path'][0], ops[1]['value'], ops[2]['value']
    return None

def counter_incr(s):
    ops = s['ops']
    if [o['kind'] for o in ops] == ['idx', 'addi', 'ins'] and ops[0]['pushPath'] and len(ops[0]['path']) == 1:
        return ops[0]['path'][0], ops[1]['immediate'], +1
    if [o['kind'] for o in ops] == ['idx', 'subi', 'ins'] and ops[0]['pushPath'] and len(ops[0]['path']) == 1:
        return ops[0]['path'][0], ops[1]['immediate'], -1
    return None

def const_prefix(path):
    out = []
    for a in path:
        k = const_key(a)
        if k is None: break
        out.append(k)
    return out[:3]

# ------------------------------------------------------------------ reuse simulation
def sim_reuse(c, cname):
    """Returns removals: list of (body index, class, replacement exprs or var list, source)."""
    facts = []   # dict(guard, n, path(canon), align(canon), vals(list expr), origin, crossed, pi, src)
    rem = []
    blocked = {'size': 0, 'multilimb': 0}
    def forget(vs):
        nonlocal facts
        facts = [f for f in facts if not (f['vars'] & vs)]
    def add(f):
        f['vars'] = expr_vars([f['guard'], f['pathx'], f['vals']], set())
        facts.insert(0, f)
        del facts[32:]
    for bi, s in enumerate(c['body']):
        k = s['kind']
        if k == 'bind': forget({s['var']}); continue
        if k == 'witness':
            forget({o['var'] for o in s['outs']}); continue
        if k != 'ledger' or (not s['ops'] and not s['reads']): continue
        g = canon(s['guard'])
        pr = plain_read(s)
        if pr:
            n, path, nidx, al = pr
            hit = None
            for f in facts:
                if f['guard'] == g and f['n'] == n and f['path'] == canon(path) and f['align'] == canon(al) \
                        and len(f['vals']) == len(s['reads']) and not (expr_vars(f['vals'], set()) & set(s['reads'])):
                    hit = f; break
            if hit:
                cls = hit['origin'] + ('+frame' if hit['crossed'] else '') + ('+multi-idx' if nidx > 1 else '')
                rem.append((bi, cls, hit['vals'], hit.get('src')))
                forget(set(s['reads']))
            else:
                forget(set(s['reads']))
                if not (expr_vars(s['guard'], set()) & set(s['reads'])):
                    add({'guard': g, 'n': n, 'path': canon(path), 'pathx': path, 'align': canon(al),
                         'vals': [{'kind': 'var', 'var': r} for r in s['reads']], 'origin': 'read', 'crossed': False,
                         'pi': const_prefix(path), 'src': ('read', bi)})
            continue
        # other statement: frame
        keep = []
        for f in facts:
            if f['n'] == 2: keep.append(f); continue
            if f['n'] == 0 and f['pi'] and frame_keeps(f['pi'], s['ops']):
                f2 = dict(f); f2['crossed'] = True; keep.append(f2)
        facts = keep
        forget(set(s['reads']))
        if s['reads']: continue
        cw = cell_write2(s)
        mi = map_insert2(s)
        cn = counter_incr(s)
        if cw or mi:
            path = [cw[0]] if cw else [mi[0], mi[1]]
            v = cw[1] if cw else mi[2]
            vidx = 1 if cw else 2
            ml = not single_limb(v['align'])
            if ml: blocked['multilimb'] += 1
            big = any(esize(e) > 16 for e in v['vals'])
            if big: blocked['size'] += 1
            vals = v['vals'] if g == ONE else [{'kind': 'select', 'cond': s['guard'], 'a': e, 'b': {'kind': 'const', 'value': '0'}} for e in v['vals']]
            add({'guard': g, 'n': 0, 'path': canon(path), 'pathx': path, 'align': canon(v['align']), 'vals': vals,
                 'origin': ('cellwrite' if cw else 'mapinsert') + ('+MULTILIMB' if ml else '') + ('+BIG' if big else ''), 'crossed': False, 'pi': const_prefix(path),
                 'src': ('write', bi, vidx, len(v['vals'])), 'big': any(esize(e) > 16 for e in v['vals'])})
        elif cn:
            key, imm, sign = cn
            for f in facts:
                if f['n'] == 0 and f['path'] == canon([key]) and f['guard'] == g and len(f['vals']) == 1:
                    add({'guard': g, 'n': 0, 'path': canon([key]), 'pathx': [key], 'align': f['align'],
                         'vals': [{'kind': 'add', 'a': f['vals'][0], 'b': imm}], 'origin': 'counter', 'crossed': False,
                         'pi': const_prefix([key]), 'src': None})
                    break
    return rem, blocked

# ------------------------------------------------------------------ dead stores
def total(e):
    k = e['kind']
    return k in ('var', 'const') or (k in ('add', 'mul', 'neg') and all(total(v) for kk, v in e.items() if isinstance(v, dict)))

def fits_const(v):
    """A constant value fitting its alignment (single atom, single limb)."""
    if len(v['vals']) != 1 or len(v['align']) != 1: return False
    a = v['align'][0]; e = v['vals'][0]
    if e['kind'] != 'const': return False
    x = int(e['value']) % P
    if a['kind'] == 'bytes': return a['length'] <= 31 and x < 2 ** (8 * a['length'])
    return True

def sim_dead(c):
    body = c['body']
    rem = []
    for bi, s in enumerate(body):
        if s['kind'] != 'ledger' or s['reads']: continue
        cw = cell_write2(s)
        if not cw: continue
        key, v = cw
        kc = const_key(key)
        if not kc: continue
        field_ok = len(v['vals']) == len(v['align']) and all(a == {'kind': 'field'} for a in v['align']) and all(total(e) for e in v['vals'])
        multi = len(v['vals']) > 1
        const_ok = fits_const(v)
        if not (field_ok or const_ok): continue
        g = canon(s['guard'])
        cls = []
        for bj in range(bi + 1, min(len(body), bi + 65)):
            t = body[bj]
            if t['kind'] != 'ledger' or (not t['ops'] and not t['reads']): continue
            tg = canon(t['guard'])
            cw2 = cell_write2(t)
            if cw2 and not t['reads'] and const_key(cw2[0]) == kc and canon(cw2[0]) == canon(key) and tg == g:
                base = 'dead' if g == ONE else 'dead+guard'
                if not field_ok: base += '+constvalue'
                if multi: base += '+multiatom'
                if cls: base += '+' + '+'.join(sorted(set(cls)))
                rem.append((bi, base)); break
            # intermediate
            if not frame_keeps([kc], t['ops']): break
            pr = plain_read(t)
            if pr and const_prefix(pr[1])[:1] == [kc]: break
            if touches_root(t['ops']): cls.append('across-root-writes')
            elif not pr: cls.append('across-other')
            else: cls.append('across-reads')
    return rem

# ------------------------------------------------------------------ ZKIR (rows) and contract.json (gas) rewriting
def zkir_blocks2(z, c):
    ins = z['instructions']
    imp = [i for i, x in enumerate(ins) if x['op'] == 'impact']
    blocks, k = {}, 0
    for bi, s in enumerate(c['body']):
        if s['kind'] != 'ledger' or not s['ops']: continue
        idxs = imp[k:k + len(s['ops'])]; k += len(s['ops'])
        outs = set(a for j in idxs for a in ins[j]['inputs'] if isinstance(a, str) and a.startswith('%'))
        pis = [i for i, x in enumerate(ins) if x['op'] == 'public_input' and x['output'] in outs]
        reads = [a for a in ins[idxs[-1]]['inputs'] if isinstance(a, str) and a.startswith('%') and
                 any(ins[p]['output'] == a for p in pis)] if idxs else []
        blocks[bi] = (idxs, pis, reads)
    assert k == len(imp), (k, len(imp))
    return blocks

def rewrite_zkir(z, blocks, drops, renames):
    ins = z['instructions']
    drop = set()
    for bi in drops:
        idxs, pis, _ = blocks[bi]; drop |= set(idxs) | set(pis)
    def sub(v):
        if isinstance(v, str): return renames.get(v, v)
        if isinstance(v, list): return [sub(x) for x in v]
        return v
    return {**z, 'instructions': [{k: sub(v) for k, v in x.items()} for i, x in enumerate(ins) if i not in drop]}

def rows_of2(d, name):
    p = os.path.join(tmp, name + '.zkir'); json.dump(d, open(p, 'w'))
    r = subprocess.run(['zkir-v3', 'mock-compile', p], capture_output=True, text=True)
    for b in glob.glob(os.path.join(tmp, name + '.bzkir')): os.remove(b)
    m = re.search(r'rows[^0-9]*([0-9]+)', r.stdout + r.stderr)
    return int(m.group(1)) if m else None

def main_classes():
    tot = {}
    per = []
    for cj in sorted(glob.glob(os.path.join(root, '*', 'contract.json'))):
        cname = os.path.basename(os.path.dirname(cj))
        d = json.load(open(cj))
        dsim = copy.deepcopy(d)
        changed_any = False
        for ci, c in enumerate(d['circuits']):
            rr, blocked = sim_reuse(c, cname)
            rset = {r[0] for r in rr}
            c2 = dict(c); c2['body'] = [({'kind': 'bind', 'var': -1} if bi in rset else s) for bi, s in enumerate(c['body'])]
            dd = sim_dead(c2)
            if '--no-dead' in sys.argv: dd = []
            if '--no-reads' in sys.argv: rr = []
            rr = [r for r in rr if 'BIG' not in r[1] and 'MULTILIMB' not in r[1]] if '--sound' in sys.argv else rr
            if only:
                rr = [r for r in rr if any(r[1].startswith(o) or o in r[1] for o in only)]
                dd = [x for x in dd if any(o in x[1] for o in only)]
            for k in ('size', 'multilimb'):
                if blocked[k]: tot['blocked.' + k] = tot.get('blocked.' + k, 0) + blocked[k]
            if not rr and not dd: continue
            row = {'circuit': f'{cname}.{c["name"]}', 'reads': [r[1] for r in rr], 'dead': [x[1] for x in dd]}
            for r in rr: tot['R:' + r[1]] = tot.get('R:' + r[1], 0) + 1
            for x in dd: tot['D:' + x[1]] = tot.get('D:' + x[1], 0) + 1
            zp = os.path.join(os.path.dirname(cj), 'zkir', c['name'] + '.zkir')
            drops = [r[0] for r in rr] + [x[0] for x in dd]
            if (want_rows or sim_out) and os.path.exists(zp):
                z = json.load(open(zp))
                blocks = zkir_blocks2(z, c)
                ren = {}
                for bi, cls, vals, src in rr:
                    reads = blocks[bi][2]
                    if src and src[0] == 'read':
                        for a, b in zip(reads, blocks[src[1]][2]): ren[a] = b
                    elif src and src[0] == 'write':
                        _, wbi, vidx, nv = src
                        names = z['instructions'][blocks[wbi][0][vidx]]['inputs'][-nv:]
                        for a, b in zip(reads, names): ren[a] = b
                # chains
                for a in list(ren):
                    while ren[a] in ren: ren[a] = ren[ren[a]]
                z2 = rewrite_zkir(z, blocks, drops, ren)
                if want_rows:
                    base = rows_of2(z, 'base'); after = rows_of2(z2, 'after')
                    row['rows'] = (base, after); row['instr'] = (len(z['instructions']), len(z2['instructions']))
                    tot['rows.saved'] = tot.get('rows.saved', 0) + base - after
                    tot['instr.saved'] = tot.get('instr.saved', 0) + len(z['instructions']) - len(z2['instructions'])
                if sim_out:
                    od = os.path.join(sim_out, cname, 'zkir'); os.makedirs(od, exist_ok=True)
                    json.dump(z2, open(os.path.join(od, c['name'] + '.zkir'), 'w'))
            # contract.json rewrite
            body = []
            rmap = {r[0]: r for r in rr}
            dset = {x[0] for x in dd}
            for bi, s in enumerate(c['body']):
                if bi in dset: continue
                if bi in rmap:
                    _, _, vals, _ = rmap[bi]
                    for v, e in zip(s['reads'], vals):
                        body.append({'kind': 'bind', 'var': v, 'hint': 'ledger', 'expr': e})
                    continue
                body.append(s)
            dsim['circuits'][ci]['body'] = body
            changed_any = True
            per.append(row)
        if sim_out:
            od = os.path.join(sim_out, cname); os.makedirs(os.path.join(od, 'zkir'), exist_ok=True)
            for f in glob.glob(os.path.join(os.path.dirname(cj), 'zkir', '*')):
                t = os.path.join(od, 'zkir', os.path.basename(f))
                if not os.path.exists(t): shutil.copy(f, t)
            for f in glob.glob(os.path.join(os.path.dirname(cj), '*')):
                if os.path.isfile(f) and os.path.basename(f) != 'contract.json': shutil.copy(f, od)
            json.dump(dsim, open(os.path.join(od, 'contract.json'), 'w'))
    for r in per: print(r)
    print('total', json.dumps(tot, indent=1, sort_keys=True))
    if out_json: json.dump({'circuits': per, 'total': tot}, open(out_json, 'w'), indent=1)


# ================================================================== --merge
def simple(ops):
    k = [o['kind'] for o in ops]
    if k == ['push', 'push', 'ins'] and not ops[2]['cached']: return True
    if k[0] == 'dup' and k[-1] == 'popeq' and all(x == 'idx' and not o['cached'] and not o['pushPath'] for x, o in zip(k[1:-1], ops[1:-1])): return True
    return False
def nocache(ops):
    return not any(o.get('cached') for o in ops) and not any(o['kind'] in ('idxStack', 'concatCached', 'branch', 'jmp', 'swap') for o in ops)



# The analysis of Damp/Optimize/LedgerMerge.lean (`mcheck`, `mboundary`), ported: a tag per stack entry
# (value: ('o', i) initial value i / ('k', key) a constant cell / ('x',); strength True/False/None; fully
# cached; constant keys visited).
INIT = [(('o', 2), True, False, frozenset()), (('o', 1), False, True, frozenset()), (('o', 0), False, True, frozenset())]
def band(a, b):
    if a is False or b is False: return False
    if a is True and b is True: return True
    return None
NEW = (('x',), True, True, frozenset())
def hit(cont, key):
    return cont[2] or (key[0][0] == 'k' and key[0][1] in cont[3])
class Fail(Exception): pass

def mkey(v):
    # `mkeyVal`: a key is known only when every operand is a constant
    return ('k', canon(v)) if all(x.get('kind') == 'const' for x in v['vals']) else ('x',)

def step(op, ts, check):
    k = op['kind']
    ts = list(ts)
    def pop():
        if not ts: raise Fail('empty')
        return ts.pop(0)
    if k == 'dup':
        if op['n'] >= len(ts): raise Fail('dup')
        ts.insert(0, ts[op['n']])
    elif k == 'swap':
        n = op['n'] + 1
        if n >= len(ts): raise Fail('swap')
        ts[0], ts[n] = ts[n], ts[0]
    elif k in ('idx', 'idxStack'):
        if k == 'idxStack':
            sk = pop(); keys = [mkey(p) for p in op['path']] + [sk[0]]; cached = True; pp = False
        else:
            keys = [mkey(p) for p in op['path']]; cached = op['cached']; pp = op['pushPath']
        curr = pop()
        for kk in keys:
            if cached and check and not (curr[2] or (kk[0] == 'k' and kk[1] in curr[3])): raise Fail('idx miss')
            if pp:
                ts.insert(0, (curr[0], curr[1], curr[2], curr[3] | {kk[1]} if kk[0] == 'k' else curr[3]))
                ts.insert(0, (kk, False, True, frozenset()))
            curr = (('x',), curr[1], curr[2], frozenset())
        ts.insert(0, curr)
    elif k == 'ins':
        curr = pop(); s = curr[1]; fc = curr[2]
        for _ in range(op['n']):
            key = pop(); cont = pop()
            if op['cached'] and check and not hit(cont, key): raise Fail('ins miss')
            s = band(s, cont[1]); fc = fc and cont[2]
        ts.insert(0, (('x',), s, fc, frozenset()))
    elif k == 'rem':
        key = pop(); cont = pop()
        if op['cached'] and check and not hit(cont, key): raise Fail('rem miss')
        ts.insert(0, (('x',), cont[1], cont[2], cont[3]))
    elif k == 'push':
        ts.insert(0, (mkey(op['value']), op['storage'], True, frozenset()))
    elif k in ('pushNull', 'pushState'):
        ts.insert(0, (('x',), op['storage'], True, frozenset()))
    elif k in ('popeq', 'pop', 'log'):
        pop()
    elif k in ('lt', 'eq', 'and', 'or', 'add', 'sub', 'member', 'concat', 'concatCached'):
        pop(); pop(); ts.insert(0, NEW)
    elif k in ('type', 'size', 'neg', 'root', 'addi', 'subi'):
        pop(); ts.insert(0, NEW)
    elif k == 'ckpt':
        pass
    else:
        raise Fail('op ' + k)
    return ts
def run(ops, ts, check, fuel=None):
    """All paths: list of final tag stacks; raises Fail."""
    if fuel is None: fuel = len(ops) + 1
    if fuel == 0: raise Fail('fuel')
    if not ops: return [ts]
    op, rest = ops[0], ops[1:]
    if op['kind'] == 'branch':
        if op['skip'] > len(rest): raise Fail('jump past end')
        if not ts: raise Fail('empty')
        return run(rest, ts[1:], check, fuel - 1) + run(rest[op['skip']:], ts[1:], check, fuel - 1)
    if op['kind'] == 'jmp':
        if op['skip'] > len(rest): raise Fail('jump past end')
        return run(rest[op['skip']:], ts, check, fuel - 1)
    return run(rest, step(op, ts, check), check, fuel - 1)
def boundary(ts):
    return (len(ts) == 3 and ts[0][1] is True and ts[1][0] == ('o', 1) and ts[1][1] is False and ts[1][2]
            and ts[2][0] == ('o', 0) and ts[2][1] is False and ts[2][2])
def why_not(p1, p2):
    try:
        ends = run(p1, INIT, False)
    except Fail as e:
        return 'p1:' + str(e)
    for t in ends:
        if not boundary(t):
            if len(t) != 3: return 'p1-height'
            if t[0][1] is not True: return 'p1-weakstate'
            if t[1][0] != ('o', 1): return 'p1-effects'
            return 'p1-other'
    try:
        run(p2, INIT, True)
    except Fail as e:
        return 'p2:' + str(e)
    return None

def vars_of(x, acc=None):
    if acc is None: acc = set()
    if isinstance(x, dict):
        if x.get('kind') == 'var' and 'var' in x: acc.add(x['var'])
        for v in x.values(): vars_of(v, acc)
    elif isinstance(x, list):
        for v in x: vars_of(v, acc)
    return acc
def binds(s):
    if s['kind'] == 'bind': return {s['var']}
    if s['kind'] == 'witness': return {o['var'] for o in s['outs']}
    if s['kind'] == 'ledger': return set(s['reads'])
    return set()
def uses(s):
    if s['kind'] == 'bind': return vars_of(s['expr'])
    if s['kind'] == 'witness': return vars_of(s['guard']) | vars_of(s['args'])
    if s['kind'] == 'ledger': return vars_of(s['guard']) | vars_of([{**o, 'result': []} if o['kind'] == 'popeq' else o for o in s['ops']])
    if s['kind'] == 'assert': return vars_of(s['cond'])
    if s['kind'] == 'constrain': return vars_of(s['expr'])
    return vars_of(s)

def m_binds(s):
    if s['kind'] == 'bind': return {s['var']}
    if s['kind'] == 'witness': return {o['var'] for o in s['outs']}
    if s['kind'] == 'ledger': return set(s['reads'])
    return set()

def m_vars(x, acc=None):
    if acc is None: acc = set()
    if isinstance(x, dict):
        if x.get('kind') == 'var' and 'var' in x: acc.add(x['var'])
        for v in x.values(): m_vars(v, acc)
    elif isinstance(x, list):
        for v in x: m_vars(v, acc)
    return acc

def m_uses(s):
    return m_vars({k: v for k, v in s.items() if k not in ('reads', 'outs', 'var')})


def main_merge(src, dst, mode):
    """Merge ledger statements with the same guard, the second not using what the first reads, under
    `mode`: all / simple / nocache (adjacent only), seq (adjacent, `mergeable` and the other conditions
    of `mergeInto`), seqgap (seq, also across statements that are not ledger statements and commute
    with the second, as `Circuit.ledgerMerge` does)."""
    stats = collections.Counter()
    def ok(a, b):
        if canon(a['guard']) != canon(b['guard']): stats['guard'] += 1; return False
        if m_uses(b) & set(a['reads']): stats['dep'] += 1; return False
        if mode == 'all': return True
        if mode == 'simple': return simple(a['ops']) and simple(b['ops'])
        if mode == 'nocache': return nocache(a['ops']) and nocache(b['ops'])
        if set(a['reads']) & set(b['reads']) or m_vars(a['ops']) & set(b['reads']): stats['dep'] += 1; return False
        if len(a['ops']) + len(b['ops']) > 160: stats['size'] += 1; return False
        w = why_not(a['ops'], b['ops'])
        if w: stats[w] += 1; return False
        return True
    gap_ok = mode == 'seqgap'
    n = 0
    for d in sorted(glob.glob(os.path.join(src, '*'))):
        name = os.path.basename(d)
        od = os.path.join(dst, name)
        shutil.copytree(d, od, dirs_exist_ok=True)
        c = json.load(open(os.path.join(d, 'contract.json')))
        for circ in c['circuits']:
            out = []
            for s in circ['body']:
                if s['kind'] == 'ledger' and s['ops']:
                    j = len(out) - 1; between = []
                    while j >= 0 and out[j]['kind'] != 'ledger':
                        between.append(out[j]); j -= 1
                    if j >= 0 and out[j]['ops'] and (gap_ok or not between) and len(between) <= 64 and all(
                            not (m_uses(s) & m_binds(g)) and not (m_binds(s) & (m_uses(g) | m_binds(g)))
                            for g in between) and ok(out[j], s):
                        out[j] = {**out[j], 'reads': out[j]['reads'] + s['reads'], 'ops': out[j]['ops'] + s['ops']}
                        n += 1
                        continue
                out.append(s)
            circ['body'] = out
        json.dump(c, open(os.path.join(od, 'contract.json'), 'w'))
    print('merged', n, dict(stats))


if '--classes' in sys.argv:
    main_classes()
elif '--merge' in sys.argv:
    i = sys.argv.index('--merge')
    main_merge(root, sys.argv[i + 1], sys.argv[i + 2] if len(sys.argv) > i + 2 else 'all')
else:
    main()
