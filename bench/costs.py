"""Rows (zkir-v3 mock-compile) each ZKIR instruction adds: a circuit with 20 copies of one
instruction against the same circuit with none. usage: python3 -I bench/costs.py"""
import json, os, re, subprocess, tempfile
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
base = rows([{'op': 'test_eq', 'a': '%a', 'b': '%b', 'output': '%z'}])
print(f'{"instruction":<34}rows each')
for op in ['test_eq', 'cond_select', 'add', 'mul', 'neg', 'copy', 'assert', 'constrain_to_boolean', 'constrain_bits 8', 'constrain_bits 64',
           'constrain_bits 248', 'less_than 64', 'less_than 128', 'div_mod_power_of_two 16', 'div_mod_power_of_two 248', 'private_input',
           'public_input', 'transient_hash (2 in)', 'persistent_hash (2 x Bytes<32>)']:
    n = 20
    r = rows([{'op': 'test_eq', 'a': '%a', 'b': '%b', 'output': '%z'}] + [mk(op, i) for i in range(n)])
    print(f'{op:<34}{(r - base) / n:g}')
