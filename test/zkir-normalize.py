"""Rewrite a compactc ZKIR file into the form Damp emits for the same circuit,
undoing the two differences documented in docs/tokens.md ("Differences"):

1. compactc computes a persistent hash again each time the source asks for it;
   Damp shares a hash of the same inputs. A `persistent_hash` whose alignment
   and inputs equal an earlier one is dropped, with its `bytes_into_natives`,
   and later uses refer to the earlier results.
2. compactc writes some constants through `copy` (the zero top byte of
   `upgradeFromTransient`), and then selects between that copy and the same
   constant; Damp uses the constant and folds the select. A `copy` of a
   constant is dropped and replaced by the constant; a `cond_select` whose two
   branches are then the same constant is replaced by it.
3. compactc's coin commitment inside `writeCoin`/`insertCoin`/`pushFrontCoin`
   (its built-in `rt-coin-commit`, not the library's `coinCommitment`) selects
   the recipient's bytes with a `cond_select` even when the selector is a
   constant (`right(kernel.self())`: bit 0); Damp folds it. A `cond_select`
   with a constant bit is replaced by the branch it picks.

Usage: python3 -I test/zkir-normalize.py IN.zkir OUT.zkir
Used by test/oracle.sh only for circuits listed in test/oracle/known-differences.
"""
import json, sys

src = json.load(open(sys.argv[1]))
ren, hashes, natives, out = {}, {}, {}, []

def sub(v):
    if isinstance(v, str): return ren.get(v, v)
    if isinstance(v, list): return [sub(x) for x in v]
    return v

def is_const(v): return isinstance(v, str) and v.startswith(('0x', '-0x'))

for ins in src['instructions']:
    i = {k: sub(v) for k, v in ins.items()}
    op = i['op']
    if op == 'copy' and is_const(i['val']):
        ren[i['output']] = i['val']; continue
    if op == 'cond_select' and is_const(i['a']) and i['a'] == i['b']:
        ren[i['output']] = i['a']; continue
    if op == 'cond_select' and i['bit'] in ('0x00', '0x01'):
        ren[i['output']] = i['a'] if i['bit'] == '0x01' else i['b']; continue
    if op == 'persistent_hash':
        key = json.dumps([i['alignment'], i['inputs']])
        if key in hashes:
            ren[i['output']] = hashes[key]; continue
        hashes[key] = i['output']
    if op == 'bytes_into_natives':
        if i['bytes'] in natives:
            for a, b in zip(i['outputs'], natives[i['bytes']]): ren[a] = b
            continue
        natives[i['bytes']] = i['outputs']
    out.append(i)

src['instructions'] = out
json.dump(src, open(sys.argv[2], 'w'), indent=2)
