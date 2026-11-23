// Audit (docs/audit.md, edge "IrSource.run vs zkir-v3"): synthetic circuits for operator edge
// cases that test/semantics.sh does not cover (cond_select / assert / not on non-boolean
// conditions, less_than at 0, 1, 248, 253 bits, field wrap-around of add / mul / neg, constrain_bits
// at 0 and 248 bits, div_mod_power_of_two at 1 and 247 bits of p-1, test_eq of -1 and p-1).
// Each value is tested by constraining the result to the expected immediate and to that +1; the
// real checker (`check` of @midnightntwrk/zkir-v3, via semantics-check.mjs) decides, and the Lean
// port must agree: run `damp-semantics-test <out>/vectors.json --other <out>/synthetic/*.zkir`.
//
// Usage: node test/audit-zkir-edges.mjs <out dir>
import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { serializePreimage } from './preimage.mjs';

const here = path.dirname(fileURLToPath(import.meta.url));
const outDir = path.resolve(process.argv[2]);
fs.mkdirSync(path.join(outDir, 'synthetic'), { recursive: true });
const P = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001n;
const N = 'Scalar<BLS12-381>';
const imm = (x) => {
  const v = ((BigInt(x) % P) + P) % P;
  let h = '';
  for (let y = v; ; y >>= 8n) { h += (y & 0xffn).toString(16).padStart(2, '0'); if (y < 256n) break; }
  return '0x' + h;
};
const vectors = [];
let n = 0;
const circuit = (instructions, inputs) => {
  const name = `audit${n++}`;
  const p = path.join(outDir, 'synthetic', `${name}.zkir`);
  fs.writeFileSync(p, JSON.stringify({
    version: { major: 3, minor: 1 }, do_communications_commitment: false,
    inputs: inputs.map((_, i) => ({ name: `%i.${i}`, type: N })), outputs: [],
    instructions: [...instructions, { op: 'output', vals: [] }],
  }, null, 1));
  return { p, name };
};
const add = (group, kind, instrs, inputs) => {
  const { p, name } = circuit(instrs, inputs);
  vectors.push({
    id: `A${String(vectors.length).padStart(3, '0')}`, group, kind, zkir: p,
    pre: { inputs, privateTranscript: [], publicTranscriptInputs: [], publicTranscriptOutputs: [], bindingInput: 0n, commitment: null, keyLocation: name },
  });
};
/** `op` computes %r.9 from inputs; check it equals `expect` (and that expect+1 is refused). */
const value = (group, kind, op, inputs, expect) => {
  add(group, `${kind} = ${expect}`, [op, { op: 'constrain_eq', a: '%r.9', b: imm(expect) }], inputs);
  add(group, `${kind} = ${expect}+1`, [op, { op: 'constrain_eq', a: '%r.9', b: imm(BigInt(expect) + 1n) }], inputs);
};
const B = [0n, 1n, 2n, P - 1n];
for (const bit of B) {
  value('cond_select', `select(${bit}, 5, 9)`, { op: 'cond_select', output: '%r.9', bit: '%i.0', a: '%i.1', b: '%i.2' }, [bit, 5n, 9n], bit === 1n ? 5n : 9n);
  add('assert', `assert ${bit}`, [{ op: 'assert', cond: '%i.0' }], [bit]);
  add('constrain_to_boolean', `${bit}`, [{ op: 'constrain_to_boolean', val: '%i.0' }], [bit]);
  value('not', `not ${bit}`, { op: 'not', output: '%r.9', a: '%i.0' }, [bit], bit === 0n ? 1n : 0n);
}
for (const [bits, xs] of [[0, [0n, 1n]], [1, [0n, 1n, 2n]], [248, [0n, (1n << 248n) - 1n, 1n << 248n]], [253, [(1n << 253n) - 1n, 1n << 253n, P - 1n]]]) {
  for (const a of xs) for (const b of xs) {
    value(`less_than ${bits}`, `${a} < ${b}`, { op: 'less_than', output: '%r.9', a: '%i.0', b: '%i.1', bits }, [a, b], a < b ? 1n : 0n);
  }
  for (const a of xs) add(`constrain_bits ${bits}`, `${a}`, [{ op: 'constrain_bits', val: '%i.0', bits }], [a]);
}
value('add', '(p-1)+1', { op: 'add', output: '%r.9', a: '%i.0', b: '%i.1' }, [P - 1n, 1n], 0n);
value('add', '(p-1)+(p-1)', { op: 'add', output: '%r.9', a: '%i.0', b: '%i.1' }, [P - 1n, P - 1n], P - 2n);
value('mul', '(p-1)*(p-1)', { op: 'mul', output: '%r.9', a: '%i.0', b: '%i.1' }, [P - 1n, P - 1n], 1n);
value('mul', '2^200*2^200', { op: 'mul', output: '%r.9', a: '%i.0', b: '%i.1' }, [1n << 200n, 1n << 200n], (1n << 400n) % P);
value('neg', 'neg 0', { op: 'neg', output: '%r.9', a: '%i.0' }, [0n], 0n);
value('neg', 'neg 1', { op: 'neg', output: '%r.9', a: '%i.0' }, [1n], P - 1n);
value('add', 'immediate -1', { op: 'add', output: '%r.9', a: '%i.0', b: '-0x01' }, [0n], P - 1n);
value('test_eq', '-1 == p-1', { op: 'test_eq', output: '%r.9', a: '-0x01', b: '%i.0' }, [P - 1n], 1n);
for (const bits of [1, 247]) {
  const x = P - 1n;
  add(`div_mod ${bits}`, `p-1 quotient`, [{ op: 'div_mod_power_of_two', outputs: ['%r.9', '%s.8'], val: '%i.0', bits }, { op: 'constrain_eq', a: '%r.9', b: imm(x >> BigInt(bits)) }, { op: 'constrain_eq', a: '%s.8', b: imm(x & ((1n << BigInt(bits)) - 1n)) }], [x]);
}

const hex = (b) => Buffer.from(b).toString('hex');
const jobs = vectors.map((v) => ({ zkir: v.zkir, preimage: hex(serializePreimage(v.pre)) }));
const jobsFile = path.join(outDir, 'jobs.json');
fs.writeFileSync(jobsFile, JSON.stringify(jobs));
const results = new Array(jobs.length);
let start = 0;
while (start < jobs.length) {
  const r = spawnSync(process.execPath, [path.join(here, 'semantics-check.mjs'), jobsFile, String(start)], { maxBuffer: 1 << 30, encoding: 'utf-8' });
  let last = start - 1;
  for (const line of r.stdout.split('\n')) { if (!line) continue; const res = JSON.parse(line); results[res.i] = res; last = res.i; }
  if (last === jobs.length - 1) break;
  results[last + 1] = { i: last + 1, ok: false, error: 'crashed', crashed: true };
  start = last + 2;
}
const classify = (res) => {
  if (res.ok) return 'accept';
  const e = res.error;
  if (res.crashed) return 'premise';
  if (/Public transcript input mismatch/.test(e)) return 'pt-mismatch';
  if (/Transcripts not fully consumed/.test(e)) return 'unconsumed';
  if (/Communications commitment mismatch|Expected communications/.test(e)) return 'commitment';
  if (/raw inputs/.test(e)) return 'inputs';
  return 'premise';
};
const dec = (xs) => xs.map(String);
const out = vectors.map((v, i) => ({
  id: v.id, group: v.group, kind: v.kind, zkir: v.zkir,
  inputs: dec(v.pre.inputs), priv: [], ptOut: [], ptIn: [], commitment: null, expectOutputs: null,
  real: { ok: results[i].ok, reason: classify(results[i]), error: results[i].error ?? null, skips: results[i].skips ?? null },
}));
fs.writeFileSync(path.join(outDir, 'vectors.json'), JSON.stringify({ vectors: out, crypto: {}, reader: [] }, null, 1));
console.log(`${out.length} audit vectors, ${out.filter((v) => v.real.ok).length} accepted by the real checker`);
