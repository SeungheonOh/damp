"""Compare Damp's reading of each .zkir file with what Midnight's loader read.

usage: python3 -I test/loader.py DUMP

DUMP has one line per file: `<path>\t<json>`, where <json> is the circuit Damp's
reader (`Zkir.IrSource.parse`) returned, printed back with `IrSource.toJson`
(which `IrSource.ofJson_toJson` proves Damp reads as the same circuit), or
`<path>\tFAIL <message>` when Damp's reader refused the file.

`zkir-v3 mock-compile F.zkir` loads F.zkir with Midnight's Rust loader and
writes F.bzkir: the loaded circuit in the tool's binary format. This script
encodes Damp's reading in that format and requires the bytes to be identical,
so the loader and Damp's reader agree on every field of every instruction:
register names, immediates (as field elements: the loader re-prints them as
minimal little-endian hex of the value modulo p), types, guards, bit widths,
alignments, and the order and number of inputs, outputs and instructions.

The format was read off the tool's output; only what Damp emits is covered
(instructions Damp never emits raise an error here rather than being guessed).
"""
import json, os, sys

P = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
HEADER = b'midnight:ir-source[v3-generic]:\x01'
TYPES = {'Scalar<BLS12-381>': 0}


def compact(n):
    if n < 64: return bytes([n << 2])
    if n < 1 << 14: return ((n << 2) | 1).to_bytes(2, 'little')
    if n < 1 << 30: return ((n << 2) | 2).to_bytes(4, 'little')
    b = n.to_bytes((n.bit_length() + 7) // 8, 'little')
    return bytes([((len(b) - 4) << 2) | 3]) + b


def string(x):
    b = x.encode()
    return compact(len(b)) + b


def imm_value(t):
    neg = t.startswith('-')
    v = int.from_bytes(bytes.fromhex(t[3:] if neg else t[2:]), 'little')
    return -v if neg else v


def operand(o):
    if o.startswith('%'): return b'\x00' + string(o)
    b = (imm_value(o) % P).to_bytes(32, 'little').rstrip(b'\0') or b'\0'
    return b'\x01' + string('0x' + b.hex())


def ty(t):
    if t not in TYPES: raise ValueError(f'type {t} not covered')
    return bytes([TYPES[t]])


def operands(l): return compact(len(l)) + b''.join(operand(x) for x in l)
def idents(l): return compact(len(l)) + b''.join(string(x) for x in l)
def opt_guard(g): return b'\x00' if g is None else b'\x01' + operand(g)


def atom(a):
    v = a['value']
    if v['tag'] == 'field': return b'\x41'
    if v['tag'] == 'bytes':
        n = v['length']
        if n < 32: return bytes([n])
        if n < 32 * 128: return bytes([0x20 | (n & 0x1f), n >> 5])
    raise ValueError(f'alignment atom {a} not covered')


def alignment(al):
    if len(al) == 1: return atom(al[0])
    if len(al) >= 32: raise ValueError('alignment of 32 or more atoms not covered')
    return bytes([0xc0 | len(al)]) + b''.join(atom(a) for a in al)


# op: (tag, fields in the order the binary format lists them)
LAYOUT = {
    'assert': (0x01, [('cond', operand)]),
    'cond_select': (0x02, [('bit', operand), ('a', operand), ('b', operand), ('output', string)]),
    'constrain_bits': (0x03, [('val', operand), ('bits', compact)]),
    'constrain_to_boolean': (0x05, [('val', operand)]),
    'copy': (0x06, [('val', operand), ('output', string)]),
    'impact': (0x07, [('guard', operand), ('inputs', operands)]),
    'div_mod_power_of_two': (0x12, [('val', operand), ('bits', compact), ('outputs', idents)]),
    'transient_hash': (0x14, [('inputs', operands), ('output', string)]),
    'persistent_hash': (0x15, [('alignment', alignment), ('inputs', operands), ('output', string)]),
    'test_eq': (0x17, [('a', operand), ('b', operand), ('output', string)]),
    'add': (0x18, [('a', operand), ('b', operand), ('output', string)]),
    'mul': (0x19, [('a', operand), ('b', operand), ('output', string)]),
    'neg': (0x1a, [('a', operand), ('output', string)]),
    'less_than': (0x1d, [('a', operand), ('b', operand), ('bits', compact), ('output', string)]),
    'public_input': (0x1f, [('guard', opt_guard), ('type', ty), ('output', string)]),
    'private_input': (0x20, [('guard', opt_guard), ('type', ty), ('output', string)]),
    'output': (0x21, [('vals', operands)]),
    'bytes_into_natives': (0x2d, [('bytes', operand), ('outputs', idents)]),
}


def encode(d):
    out = bytearray(HEADER)
    out += compact(len(d['inputs']))
    for i in d['inputs']: out += string(i['name']) + ty(i['type'])
    out += compact(len(d['outputs'])) + b''.join(ty(t) for t in d['outputs'])
    out += b'\x01' if d['do_communications_commitment'] else b'\x00'
    out += compact(len(d['instructions']))
    for i in d['instructions']:
        if i['op'] not in LAYOUT: raise ValueError(f"instruction {i['op']} not covered")
        tag, fields = LAYOUT[i['op']]
        out.append(tag)
        for k, f in fields: out += f(i.get(k))
    return bytes(out)


def main():
    ok = bad = 0
    ninstr = 0
    for line in open(sys.argv[1]):
        path, _, js = line.rstrip('\n').partition('\t')
        if js.startswith('FAIL'):
            print(f'FAIL {path}: Damp reader: {js}'); bad += 1; continue
        bz = path[:-5] + '.bzkir'
        if not os.path.exists(bz):
            print(f'FAIL {path}: zkir-v3 did not load it'); bad += 1; continue
        d = json.loads(js)
        try:
            mine = encode(d)
        except ValueError as e:
            print(f'FAIL {path}: {e}'); bad += 1; continue
        theirs = open(bz, 'rb').read()
        if mine != theirs:
            k = next((i for i in range(min(len(mine), len(theirs))) if mine[i] != theirs[i]), min(len(mine), len(theirs)))
            print(f'FAIL {path}: loader read differs at byte {k}: Damp {mine[k:k+24].hex(" ")} / zkir-v3 {theirs[k:k+24].hex(" ")}')
            bad += 1
        else:
            ok += 1; ninstr += len(d['instructions'])
    print(f'{ok} circuits ({ninstr} instructions) read identically by zkir-v3 and Damp, {bad} failures')
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
