"""Ledger-level rewrites left in a build: how many, and what they would save.

usage: python3 -I bench/ledger_headroom.py BUILD_DIR [--rows] [--json FILE]

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
import glob, json, os, re, subprocess, sys, tempfile

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

main()
