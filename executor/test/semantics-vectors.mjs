// Test vectors for the differential test of Damp/Zkir/Semantics.lean against
// Midnight's real ZKIR evaluator (see docs/zkir-semantics.md, test/semantics.sh).
//
// 1. Runs real calls of every example contract through the generic executor
//    and serializes each call's proof data with the runtime's own
//    `proofDataIntoSerializedPreimage`. Parsing that preimage (preimage.mjs)
//    gives exactly the field elements the real checker consumes: the inputs,
//    the private transcript, the public transcript's outputs (ledger reads),
//    the public transcript's inputs (the runtime's field encoding of the
//    on-chain instructions that ran), and the communications commitment with
//    its opening. Damp's own encoder (Damp/IR/Impact.lean) is not involved.
// 2. Derives tampered preimages from each one, and dishonest claims for calls
//    that fail in JS (their arguments substituted into a neighbouring call's
//    proof data).
// 3. Adds synthetic circuits for the instructions the examples do not emit
//    (copy, not, constrain_eq) and for the hashes, with expected values from
//    the runtime.
// 4. Runs every preimage through the real `check` (semantics-check.mjs, in a
//    child process that may crash on a wasm panic) and records what it did.
// 5. Writes vectors.json (for the Lean executable `damp-semantics-test`) and
//    the cryptography cases.
//
// Usage: node test/semantics-vectors.mjs <oracle build dir> <out dir>

import fs from 'node:fs';
import path from 'node:path';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import * as rt from '@midnight-ntwrk/compact-runtime';
import * as ocrt from '@midnightntwrk/onchain-runtime-v4';
import { makeContract } from '../src/executor.mjs';
import { proofDataOf, toJson } from '../harness/json.mjs';
import { parsePreimage, serializePreimage, frToHex, frFromHex } from './preimage.mjs';

const here = path.dirname(fileURLToPath(import.meta.url));
const root = path.resolve(process.argv[2] ?? path.join(here, '..', '..', 'build', 'oracle-vec'));
const outDir = path.resolve(process.argv[3] ?? path.join(here, '..', '..', 'build', 'semantics'));
fs.mkdirSync(path.join(outDir, 'synthetic'), { recursive: true });

const P = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001n;
const COIN_PK = '0'.repeat(64);
const EMPTY = { value: [], alignment: [] };

// ---------------------------------------------------------------- field view via the runtime

/** The runtime's field encoding of an AlignedValue: serialize it as a preimage's input. */
const fieldsOf = (av) => parsePreimage(rt.proofDataIntoSerializedPreimage(av, EMPTY, [], [], 'x')).inputs;

const preimageOf = (pd, key) =>
  parsePreimage(rt.proofDataIntoSerializedPreimage(pd.input, pd.output, pd.publicTranscript, pd.privateTranscriptOutputs, key));

// ---------------------------------------------------------------- contract calls (as test/run.mjs)

const bytes = (n, first, last) => { const b = new Uint8Array(n); b[0] = first; b[n - 1] = last; return b; };
const admin = new Uint8Array(32); admin.set(new TextEncoder().encode('admin'));
const vaultKey = bytes(32, 21, 22);

const witnesses = {
  hint: ({ privateState }) => [privateState, 7n],
  delta: ({ privateState }) => [privateState, 3n],
  pick: ({ privateState }) => [privateState, { x: 1000n, y: 9n }],
  secret: ({ privateState }) => [privateState, bytes(32, 7, 250)],
  nonce: ({ privateState }) => [privateState, bytes(32, 11, 12)],
  key: ({ privateState }) => [privateState, vaultKey],
};
const constructorArgs = { vault: [rt.persistentHash(new rt.CompactTypeBytes(32), vaultKey), 40n] };

const rootOf = (field) => (c) => c.mod.ledger(c.state ?? c.init.currentContractState.data)[field].root();
const rootIn = (field, k) => (c) => c.mod.ledger(c.state ?? c.init.currentContractState.data)[field].lookup(k).root();

// [contract, circuit, args]. Whether a call succeeds is observed, not assumed.
const calls = [
  ['step', 'step', [5n, true, 42n]],
  ['step', 'step', [5n, false, 42n]],
  ['step', 'step', [5n, true, 5000n]],
  ['counter', 'bump', [12n, true, false]],
  ['counter', 'bump', [12n, true, true]],
  ['counter', 'bump', [12n, false, false]],
  ['counter', 'bump', [600n, true, false]],
  ['counter', 'arith', [9n, 4n, 100n]],
  ['counter', 'arith', [4n, 4n, 100n]],
  ['counter', 'arith', [3n, 4n, 100n]],
  ['shapes', 'move', [{ x: 5n, y: 2n }, [1n, 2n, 3n], true, true]],
  ['shapes', 'move', [{ x: 5n, y: 2n }, [1n, 2n, 3n], true, false]],
  ['shapes', 'move', [{ x: 5n, y: 2n }, [1n, 2n, 3n], false, true]],
  ['shapes', 'move', [{ x: 5n, y: 300n }, [1n, 2n, 3n], true, true]],
  ['shapes', 'pay', [77n, 10n, 3n, 2n]],
  ['shapes', 'pay', [77n, 5n, 2n, 2n]],
  ['shapes', 'pay', [78n, 1n, 7n, 9n]],
  ['shapes', 'pay', [77n, 1n, 7n, 9n]],
  ['loops', 'tally', [[1n, 2n, 3n, 4n], [true, false, true, true], 3n]],
  ['loops', 'tally', [[1n, 2n, 3n, 4n], [false, true, false, false], 200n]],
  ['bytes', 'claim', [bytes(32, 1, 2), bytes(8, 3, 4), true]],
  ['bytes', 'claim', [admin, bytes(8, 3, 4), true]],
  ['bytes', 'claim', [admin, bytes(8, 5, 6), false]],
  ['bytes', 'store', [bytes(64, 9, 200), 12345n]],
  ['extras', 'advance', [0, bytes(32, 1, 1), { is_some: true, value: 500n }, 42n]],
  ['extras', 'advance', [1, bytes(32, 1, 1), { is_some: true, value: 500n }, 42n]],
  ['extras', 'advance', [1, bytes(32, 2, 2), { is_some: true, value: 50n }, 43n]],
  ['extras', 'advance', [2, bytes(32, 3, 3), { is_some: false, value: 0n }, 44n]],
  ['extras', 'advance', [0, bytes(32, 4, 4), { is_some: false, value: 0n }, 45n]],
  ['vault', 'spend', [30n]],
  ['vault', 'spend', [5n]],
  ['vault', 'spend', [6n]],
  ['structures', 'tick', [5n, 10n, false]],
  ['structures', 'tick', [3n, 2n, false]],
  ['structures', 'tick', [1n, 100n, true]],
  ['structures', 'tick', [0n, 1n, false]],
  ['structures', 'books', [7n, false]],
  ['structures', 'books', [8n, false]],
  ['structures', 'books', [9n, true]],
  ['structures', 'dequeue', []],
  ['structures', 'enqueue', [11n]],
  ['structures', 'enqueue', [0n]],
  ['structures', 'dequeue', []],
  ['structures', 'enqueue', [5n]],
  ['structures', 'enqueue', [6n]],
  ['structures', 'dequeue', []],
  ['structures', 'plant', [1n, 2n, 3n, bytes(32, 4, 5)]],
  ['structures', 'plant', [6n, 7n, 16n, bytes(32, 8, 9)]],
  ['structures', 'check', (c) => [rootOf('tree')(c), false]],
  ['structures', 'check', [{ field: 123n }, true]],
  ['structures', 'record', (c) => [bytes(32, 1, 2), bytes(32, 3, 4), bytes(32, 5, 6), 2n, rootOf('hist')(c), 0n]],
  ['structures', 'record', (c) => [bytes(32, 7, 8), bytes(32, 9, 10), bytes(32, 11, 12), 5n, rootOf('hist')(c), 1n]],
  ['structures', 'record', [bytes(32, 1, 2), bytes(32, 3, 4), bytes(32, 5, 6), 2n, { field: 99n }, 2n]],
  ['structures', 'stamp', [0n]],
  ['structures', 'stamp', [5n]],
  ['structures_nested', 'vote', [1n, 5n]],
  ['structures_nested', 'vote', [1n, 2n]],
  ['structures_nested', 'vote', [2n, 0n]],
  ['structures_nested', 'group', [7n, 1n, 5n, false]],
  ['structures_nested', 'group', [7n, 1n, 5n, false]],
  ['structures_nested', 'group', [7n, 2n, 100n, false]],
  ['structures_nested', 'group', [7n, 1n, 100n, true]],
  ['structures_nested', 'group', [7n, 2n, 100n, true]],
  ['structures_nested', 'join', [1n, 10n, false]],
  ['structures_nested', 'join', [1n, 11n, false]],
  ['structures_nested', 'join', [2n, 12n, true]],
  ['structures_nested', 'enqueue', [1n, 10n]],
  ['structures_nested', 'enqueue', [1n, 11n]],
  ['structures_nested', 'enqueue', [1n, 12n]],
  ['structures_nested', 'enqueue', [2n, 13n]],
  ['structures_nested', 'grow', [1n, 10n, 5n, { field: 0n }, false]],
  ['structures_nested', 'grow', (c) => [1n, 20n, 6n, rootIn('trees', 1n)(c), false]],
  ['structures_nested', 'grow', [1n, 30n, 7n, { field: 0n }, true]],
  ['structures_nested', 'grow', [1n, 30n, 16n, { field: 0n }, false]],
  ['structures_nested', 'hgrow', [1n, 10n, 5n, { field: 0n }, 0n]],
  ['structures_nested', 'hgrow', (c) => [1n, 20n, 6n, rootIn('hists', 1n)(c), 0n]],
  ['structures_nested', 'hgrow', (c) => [1n, 30n, 7n, rootIn('hists', 1n)(c), 1n]],
  ['structures_nested', 'hgrow', [1n, 40n, 8n, { field: 0n }, 2n]],
  ['tuned', 'settle', [[1n, 2n, 3n, 4n], true]],
  ['tuned', 'settle', [[100n, 2000n, 30n, 4n], false]],
  ['tuned', 'settle', [[65535n, 65535n, 65535n, 65535n], true]],
];

// The input AlignedValue of a call, built with the runtime's type descriptors in
// the order the executor flattens arguments. Used only for calls that fail in JS
// and so have no proof data of their own.
const bitLen = (n) => (n === 0n ? 0 : n.toString(2).length);
const descriptor = (ty) => {
  switch (ty.kind) {
    case 'field': return rt.CompactTypeField;
    case 'bool': return rt.CompactTypeBoolean;
    case 'uint': { const max = BigInt(ty.max); return new rt.CompactTypeUnsignedInteger(max, Math.ceil(bitLen(max) / 8)); }
    case 'bytes': return new rt.CompactTypeBytes(ty.length);
    case 'enum': return new rt.CompactTypeEnum(ty.max, Math.max(1, Math.ceil(bitLen(BigInt(ty.max)) / 8)));
    default: throw new Error(`unknown type ${ty.kind}`);
  }
};
function flatten(shape, v, out = []) {
  switch (shape.kind) {
    case 'struct': shape.fields.forEach((f, i) => flatten(f, v[shape.fieldNames[i]], out)); break;
    case 'tuple': shape.elems.forEach((e, i) => flatten(e, v[i], out)); break;
    case 'vector': for (let i = 0; i < shape.length; i++) flatten(shape.elem, v[i], out); break;
    default: out.push({ ty: shape, val: v });
  }
  return out;
}
/** Like the descriptor's `toValue`, but without its range check, so out-of-range claims can be made. */
const leafValue = (ty, val) => {
  if (ty.kind === 'uint' || ty.kind === 'field') return rt.bigIntToValue(BigInt(val));
  if (ty.kind === 'enum') return rt.bigIntToValue(BigInt(val));
  if (ty.kind === 'bool') return rt.bigIntToValue(val ? 1n : 0n);
  return descriptor(ty).toValue(val);
};
// Numbers (Uint, enum, Boolean) are given a field alignment: their field form is
// the same as under their byte alignment, and an out-of-range claim stays encodable.
const leafAlign = (ty) => (ty.kind === 'bytes' ? descriptor(ty).alignment() : [{ tag: 'atom', value: { tag: 'field' } }]);
const inputAligned = (circuit, args) => {
  const leaves = circuit.args.flatMap((a, k) => flatten(a.shape, args[k]));
  return { value: leaves.flatMap((l) => leafValue(l.ty, l.val)), alignment: leaves.flatMap((l) => leafAlign(l.ty)) };
};

const show = (x) => toJson(x, 0).replaceAll('"', '');
const loaded = new Map();
async function load(name) {
  if (!loaded.has(name)) {
    const dir = path.join(root, 'lean', name);
    const spec = JSON.parse(fs.readFileSync(path.join(dir, 'contract.json'), 'utf-8'));
    const contract = makeContract(spec, witnesses);
    const modPath = path.join(root, 'compact', name, 'contract', 'index.js');
    const mod = fs.existsSync(modPath) ? await import(modPath) : null;
    const init = await contract.initialState(rt.createConstructorContext({}, COIN_PK), ...(constructorArgs[name] ?? []));
    // compactc's module for the equivalent Compact source, run alongside to show
    // that the transcript is the one Midnight's own compiler would record.
    const theirs = mod ? new mod.Contract(witnesses) : null;
    const theirsInit = theirs ? await theirs.initialState(rt.createConstructorContext({}, COIN_PK), ...(constructorArgs[name] ?? [])) : null;
    loaded.set(name, { dir, spec, contract, mod, init, state: undefined, theirs, theirsInit, theirsState: undefined });
  }
  return loaded.get(name);
}

const calls_ = [];   // { label, contract, circuit, zkir, honest?: preimage, expectOutputs, pd, error?, args }
for (const [name, circuit, argsOf] of calls) {
  const c = await load(name);
  const args = typeof argsOf === 'function' ? argsOf(c) : argsOf;
  const label = `${name}.${circuit}(${args.map(show).join(', ')})`;
  const zkir = path.join(c.dir, 'zkir', `${circuit}.zkir`);
  const spec = c.spec.circuits.find((x) => x.name === circuit);
  const ctx = rt.createCircuitContext({
    circuitId: circuit, contractAddress: rt.dummyContractAddress(),
    coinPublicKeyOrZswapState: c.init.currentZswapLocalState.coinPublicKey,
    contractState: c.state ?? c.init.currentContractState, privateState: c.init.currentPrivateState, time: 0,
  });
  let run, theirsRun;
  try { run = await c.contract.circuits[circuit](ctx, ...args); } catch (e) {
    calls_.push({ label, contract: name, circuit, zkir, spec, args, error: e instanceof Error ? e.message : String(e) });
    continue;
  }
  if (c.theirs) {
    try {
      theirsRun = await c.theirs.circuits[circuit](rt.createCircuitContext({
        circuitId: circuit, contractAddress: rt.dummyContractAddress(),
        coinPublicKeyOrZswapState: c.theirsInit.currentZswapLocalState.coinPublicKey,
        contractState: c.theirsState ?? c.theirsInit.currentContractState, privateState: c.theirsInit.currentPrivateState, time: 0,
      }), ...args);
      c.theirsState = theirsRun.context.callContext.currentQueryContext.state;
    } catch { theirsRun = undefined; }
  }
  c.state = run.context.callContext.currentQueryContext.state;
  const pd = proofDataOf(run.context.callProofDataTrace.at(-1));
  const theirsPd = theirsRun?.context.callProofDataTrace.at(-1);
  const compactcAgrees = c.theirs ? !!theirsPd && toJson(proofDataOf(theirsPd), 0) === toJson(pd, 0) : null;
  if (compactcAgrees === false) console.error(`warning: compactc's module records different proof data for ${label}`);
  const compactcZkir = path.join(root, 'compact', name, 'zkir', `${circuit}.zkir`);
  calls_.push({ label, contract: name, circuit, zkir, spec, args, pd, pre: preimageOf(pd, circuit), expectOutputs: fieldsOf(pd.output),
    compactcAgrees, compactcZkir: fs.existsSync(compactcZkir) ? compactcZkir : null });
}

// ---------------------------------------------------------------- vectors

const vectors = [];
const dec = (xs) => xs.map(String);
function addVector(v) {
  vectors.push({
    id: `${String(vectors.length).padStart(4, '0')}`, ...v,
    inputs: dec(v.pre.inputs), priv: dec(v.pre.privateTranscript),
    ptOut: dec(v.pre.publicTranscriptOutputs), ptIn: dec(v.pre.publicTranscriptInputs),
    commitment: v.pre.commitment ? dec(v.pre.commitment) : null,
    expectOutputs: v.expectOutputs ? dec(v.expectOutputs) : null,
  });
}

const STREAMS = [
  ['inputs', 'inputs'], ['priv', 'privateTranscript'], ['ptOut', 'publicTranscriptOutputs'], ['ptIn', 'publicTranscriptInputs'],
];
const spread = (n, k) => (n <= k ? [...Array(n).keys()] : [...new Set(Array.from({ length: k }, (_, j) => Math.round((j * (n - 1)) / (k - 1))))]);

function tampers(call) {
  const out = [];
  const add = (kind, f) => { const q = structuredClone(call.pre); f(q); out.push({ kind, pre: q }); };
  for (const [short, key] of STREAMS) {
    const n = call.pre[key].length;
    for (const i of spread(n, short === 'inputs' ? 12 : 5)) {
      add(`${short}[${i}]+1`, (q) => { q[key][i] = (q[key][i] + 1n) % P; });
      if (short !== 'ptIn') {
        add(`${short}[${i}]=2`, (q) => { q[key][i] = 2n; });
        add(`${short}[${i}]=p-1`, (q) => { q[key][i] = P - 1n; });
      }
    }
    if (n > 0) add(`${short} drop last`, (q) => { q[key].pop(); });
    if (n > 1) add(`${short} drop first`, (q) => { q[key].shift(); });
    add(`${short} append 0`, (q) => { q[key].push(0n); });
  }
  if (call.pd.output.value.length) {
    // The claimed output, changed in its lowest byte, serialized by the runtime
    // (which recomputes the commitment over it).
    const pd = structuredClone(call.pd);
    const atom = Uint8Array.from(pd.output.value[0].length ? pd.output.value[0] : [0]);
    atom[0] = atom[0] === 255 ? 254 : atom[0] + 1;
    pd.output.value[0] = atom;
    try { out.push({ kind: 'output changed', pre: preimageOf(pd, call.circuit) }); } catch { /* not encodable */ }
  }
  if (call.pre.commitment) add('opening+1', (q) => { q.commitment[1] += 1n; });
  return out;
}

const key = (pre) => toJson(pre, 0);
for (const call of calls_) {
  if (!call.pre) continue;
  const same = call.compactcAgrees ? ' (compactc\'s module records the same proof data)' : call.compactcAgrees === false ? ' (compactc\'s module DIFFERS)' : ' (no compactc counterpart)';
  addVector({ group: call.label, kind: `honest${same}`, zkir: call.zkir, pre: call.pre, expectOutputs: call.expectOutputs });
  if (call.compactcZkir) {
    addVector({ group: call.label, kind: 'honest, against the circuit compactc compiled', zkir: call.compactcZkir, pre: call.pre, expectOutputs: call.expectOutputs });
  }
  const seen = new Set([key(call.pre)]);
  for (const t of tampers(call)) {
    if (seen.has(key(t.pre))) continue;
    seen.add(key(t.pre));
    addVector({ group: call.label, kind: `tamper: ${t.kind}`, zkir: call.zkir, pre: t.pre });
  }
}

// Calls that fail in JS: claim them anyway, on the proof data of the nearest
// successful call of the same circuit, with the runtime recomputing the
// commitment for the new inputs.
for (const [k, call] of calls_.entries()) {
  if (call.pre) continue;
  const same = (c) => c.pre && c.contract === call.contract && c.circuit === call.circuit;
  const base = [...calls_.slice(0, k)].reverse().find(same) ?? calls_.slice(k).find(same);
  if (!base) { console.error(`no proof data to claim ${call.label} on`); continue; }
  const pd = { ...base.pd, input: inputAligned(call.spec, call.args) };
  let pre;
  try { pre = preimageOf(pd, call.circuit); } catch (e) { console.error(`cannot claim ${call.label}: ${e}`); continue; }
  addVector({ group: call.label, kind: `claim of a call that fails in JS (${call.error}), on the data of ${base.label}`, zkir: call.zkir, pre });
}

// ---------------------------------------------------------------- synthetic circuits

const imm = (x) => {
  const v = ((BigInt(x) % P) + P) % P;
  let h = '';
  for (let y = v; ; y >>= 8n) { h += (y & 0xffn).toString(16).padStart(2, '0'); if (y < 256n) break; }
  return '0x' + h;
};
const N = 'Scalar<BLS12-381>';
const atomJ = (a) => ({ tag: 'atom', value: a.kind === 'bytes' ? { tag: 'bytes', length: a.length } : { tag: a.kind } });
const fieldAV = (xs) => ({ value: xs.map((x) => rt.bigIntToValue(x)[0] ?? new Uint8Array(0)), alignment: xs.map(() => atomJ({ kind: 'field' })) });

function writeCircuit(name, src) {
  const p = path.join(outDir, 'synthetic', `${name}.zkir`);
  fs.writeFileSync(p, JSON.stringify({ version: { major: 3, minor: 1 }, ...src }, null, 1));
  return p;
}
/** A preimage for a synthetic circuit; with outputs, the runtime adds the commitment over them. */
function synPre(name, inputs, outputs) {
  if (outputs === undefined) {
    return { inputs, privateTranscript: [], publicTranscriptInputs: [], publicTranscriptOutputs: [], bindingInput: 0n, commitment: null, keyLocation: name };
  }
  return parsePreimage(rt.proofDataIntoSerializedPreimage(fieldAV(inputs), fieldAV(outputs), [], [], name));
}

// copy, not, constrain_eq (on native and byte values), negative immediates, test_eq.
{
  const zkir = writeCircuit('misc', {
    do_communications_commitment: true,
    inputs: [{ name: '%a.0', type: N }, { name: '%b.1', type: N }, { name: '%c.2', type: N }],
    outputs: [N, N, N],
    instructions: [
      { op: 'copy', output: '%x.3', val: '%a.0' },
      { op: 'copy', output: '%k.4', val: '-0x05' },
      { op: 'not', output: '%n.5', a: '%b.1' },
      { op: 'constrain_eq', a: '%x.3', b: '%a.0' },
      { op: 'add', output: '%s.6', a: '%c.2', b: '%k.4' },
      { op: 'constrain_eq', a: '%s.6', b: '0x00' },
      { op: 'persistent_hash', output: '%h.7', alignment: [atomJ({ kind: 'field' })], inputs: ['%a.0'] },
      { op: 'persistent_hash', output: '%h.8', alignment: [atomJ({ kind: 'field' })], inputs: ['%x.3'] },
      { op: 'constrain_eq', a: '%h.7', b: '%h.8' },
      { op: 'test_eq', output: '%t.9', a: '%a.0', b: '%c.2' },
      { op: 'output', vals: ['%x.3', '%n.5', '%t.9'] },
    ],
  });
  // [inputs, claimed outputs]
  for (const [ins, outs] of [
    [[7n, 1n, 5n], [7n, 0n, 0n]], [[5n, 0n, 5n], [5n, 1n, 1n]], [[0n, 1n, 5n], [0n, 0n, 0n]],
    [[7n, 2n, 5n], [7n, 0n, 0n]], [[7n, 1n, 6n], [7n, 0n, 0n]], [[7n, 1n, 5n], [7n, 1n, 0n]],
    [[P - 1n, 0n, 5n], [P - 1n, 1n, 0n]], [[7n, 1n], [7n, 0n, 0n]],
  ]) {
    addVector({ group: 'synthetic misc', kind: `inputs ${ins} claiming outputs ${outs}`, zkir, pre: synPre('misc', ins, outs), expectOutputs: outs });
  }
  // A byte value compared with a native one, and a byte value used where a native is expected.
  const zkir2 = writeCircuit('mixed', {
    do_communications_commitment: false,
    inputs: [{ name: '%a.0', type: N }], outputs: [],
    instructions: [
      { op: 'persistent_hash', output: '%h.1', alignment: [atomJ({ kind: 'field' })], inputs: ['%a.0'] },
      { op: 'constrain_eq', a: '%h.1', b: '%a.0' },
      { op: 'output', vals: [] },
    ],
  });
  addVector({ group: 'synthetic mixed', kind: 'constrain_eq of bytes and a native', zkir: zkir2, pre: synPre('mixed', [3n]) });
  const zkir3 = writeCircuit('mixed2', {
    do_communications_commitment: false,
    inputs: [{ name: '%a.0', type: N }], outputs: [],
    instructions: [
      { op: 'persistent_hash', output: '%h.1', alignment: [atomJ({ kind: 'field' })], inputs: ['%a.0'] },
      { op: 'add', output: '%s.2', a: '%h.1', b: '%a.0' },
      { op: 'output', vals: [] },
    ],
  });
  addVector({ group: 'synthetic mixed', kind: 'add on a byte value', zkir: zkir3, pre: synPre('mixed2', [3n]) });
}

// Bit bounds at the edges: constrain_bits and less_than at 8, 254 and 255 bits.
{
  const mk = (bits) => writeCircuit(`bits${bits}`, {
    do_communications_commitment: true,
    inputs: [{ name: '%a.0', type: N }, { name: '%b.1', type: N }], outputs: [N],
    instructions: [
      { op: 'constrain_bits', val: '%a.0', bits },
      { op: 'less_than', output: '%t.2', a: '%a.0', b: '%b.1', bits },
      { op: 'output', vals: ['%t.2'] },
    ],
  });
  for (const [bits, cases] of [
    [8, [[3n, 5n], [5n, 3n], [255n, 255n], [256n, 0n], [0n, 256n]]],
    [254, [[(1n << 254n) - 1n, 0n], [0n, (1n << 254n) - 1n], [1n << 254n, 0n], [P - 1n, 0n]]],
    [255, [[0n, 0n]]],
  ]) {
    const zkir = mk(bits);
    for (const [a, b] of cases) {
      const t = a < b ? 1n : 0n;
      addVector({ group: `synthetic bits${bits}`, kind: `a=${a} b=${b}`, zkir, pre: synPre(`bits${bits}`, [a, b], [t]), expectOutputs: [t] });
    }
  }
}

// Guards on witness reads and impacts, with the guard computed in the circuit.
{
  const zkir = writeCircuit('guards', {
    do_communications_commitment: true,
    inputs: [{ name: '%g.0', type: N }], outputs: [N, N],
    instructions: [
      { op: 'private_input', type: N, output: '%w.1', guard: '%g.0' },
      { op: 'public_input', type: N, output: '%r.2', guard: '%g.0' },
      { op: 'private_input', type: N, output: '%u.3', guard: null },
      { op: 'impact', guard: '%g.0', inputs: ['%w.1', '0x07'] },
      { op: 'impact', guard: '0x01', inputs: ['%r.2'] },
      { op: 'output', vals: ['%w.1', '%r.2'] },
    ],
  });
  const pre = (g, priv, ptOut, ptIn, outs) => ({ ...synPre('guards', [g], outs), privateTranscript: priv, publicTranscriptOutputs: ptOut, publicTranscriptInputs: ptIn });
  for (const [kind, p, outs] of [
    ['guard on', pre(1n, [4n, 9n], [6n], [4n, 7n, 6n], [4n, 6n]), [4n, 6n]],
    ['guard off', pre(0n, [9n], [], [0n], [0n, 0n]), [0n, 0n]],
    ['guard off, impact inputs supplied', pre(0n, [9n], [], [0n, 0n, 7n, 0n], [0n, 0n]), null],
    ['guard off, witness supplied', pre(0n, [4n, 9n], [], [0n], [0n, 0n]), null],
    ['guard 2', pre(2n, [4n, 9n], [6n], [4n, 7n, 6n], [4n, 6n]), null],
  ]) addVector({ group: 'synthetic guards', kind, zkir, pre: p, expectOutputs: outs });
}

// Outside what Damp emits: arities, declared output types, and byte values
// where the Lean model only takes native ones. These show where the model and
// the real evaluator part ways on circuits Damp does not produce.
{
  const ph = (out, inp) => ({ op: 'persistent_hash', output: out, alignment: [atomJ({ kind: 'field' })], inputs: [inp] });
  const edge = [
    ['output fewer than declared', [N, N], [{ op: 'output', vals: ['%a.0'] }]],
    ['output more than declared', [N], [{ op: 'output', vals: ['%a.0', '%a.0'] }]],
    ['output none, one declared', [N], [{ op: 'output', vals: [] }]],
    ['no output instruction, one declared', [N], []],
    ['two output instructions', [N], [{ op: 'output', vals: ['%a.0'] }, { op: 'output', vals: ['%a.0'] }]],
    ['output a native where Bytes<32> is declared', ['Bytes<32>'], [{ op: 'output', vals: ['%a.0'] }]],
    ['output a byte value where a native is declared', [N], [ph('%h.1', '%a.0'), { op: 'output', vals: ['%h.1'] }]],
    ['cond_select between byte values', [], [ph('%h.1', '%a.0'), ph('%k.2', '%a.0'), { op: 'cond_select', output: '%s.3', bit: '0x01', a: '%h.1', b: '%k.2' }, { op: 'output', vals: [] }]],
    ['cond_select between a byte value and a native', [], [ph('%h.1', '%a.0'), { op: 'cond_select', output: '%s.2', bit: '0x01', a: '%h.1', b: '%a.0' }, { op: 'output', vals: [] }]],
    ['test_eq between byte values', [], [ph('%h.1', '%a.0'), ph('%k.2', '%a.0'), { op: 'test_eq', output: '%t.3', a: '%h.1', b: '%k.2' }, { op: 'assert', cond: '%t.3' }, { op: 'output', vals: [] }]],
    ['test_eq between a byte value and a native', [], [ph('%h.1', '%a.0'), { op: 'test_eq', output: '%t.2', a: '%h.1', b: '%a.0' }, { op: 'output', vals: [] }]],
    ['copy of a byte value', [], [ph('%h.1', '%a.0'), { op: 'copy', output: '%c.2', val: '%h.1' }, ph('%k.3', '%a.0'), { op: 'constrain_eq', a: '%c.2', b: '%k.3' }, { op: 'output', vals: [] }]],
    ['impact on a byte value', [], [ph('%h.1', '%a.0'), { op: 'impact', guard: '0x01', inputs: ['%h.1'] }, { op: 'output', vals: [] }]],
    ['impact on a byte value, guard off', [], [ph('%h.1', '%a.0'), { op: 'impact', guard: '0x00', inputs: ['%h.1'] }, { op: 'output', vals: [] }]],
    ['transient_hash of a byte value', [], [ph('%h.1', '%a.0'), { op: 'transient_hash', output: '%t.2', inputs: ['%h.1'] }, { op: 'output', vals: [] }]],
    ['bytes_into_natives of a native', [], [{ op: 'bytes_into_natives', outputs: ['%l.1', '%u.2'], bytes: '%a.0' }, { op: 'output', vals: [] }]],
    ['bytes_into_natives with one output', [], [ph('%h.1', '%a.0'), { op: 'bytes_into_natives', outputs: ['%l.2'], bytes: '%h.1' }, { op: 'output', vals: [] }]],
    ['register read before it is bound', [], [{ op: 'add', output: '%s.1', a: '%z.9', b: '%a.0' }, { op: 'output', vals: [] }]],
    ['register bound twice', [], [{ op: 'add', output: '%s.1', a: '%a.0', b: '0x01' }, { op: 'add', output: '%s.1', a: '%a.0', b: '0x02' }, { op: 'constrain_eq', a: '%s.1', b: '0x05' }, { op: 'output', vals: [] }]],
  ];
  edge.forEach(([kind, outputs, instructions], k) => {
    const name = `edge${k}`;
    const zkir = writeCircuit(name, {
      do_communications_commitment: false,
      inputs: [{ name: '%a.0', type: N }], outputs, instructions,
    });
    addVector({ group: 'synthetic edge', kind, zkir, pre: synPre(name, [3n]) });
  });
}

// div_mod_power_of_two: quotient and remainder, at widths 0, 8, 248 and (illegal) 249.
{
  const mk = (bits) => writeCircuit(`divmod${bits}`, {
    do_communications_commitment: true,
    inputs: [{ name: '%a.0', type: N }], outputs: [N, N],
    instructions: [
      { op: 'div_mod_power_of_two', outputs: ['%q.1', '%r.2'], val: '%a.0', bits },
      { op: 'output', vals: ['%q.1', '%r.2'] },
    ],
  });
  for (const bits of [0, 8, 248, 249]) {
    const zkir = mk(bits);
    for (const x of [0n, 5n, 300n, (1n << 248n) + 7n, (1n << 248n) - 1n, P - 1n]) {
      const q = x >> BigInt(bits), r = x & ((1n << BigInt(bits)) - 1n);
      addVector({ group: `synthetic divmod${bits}`, kind: `a=${x}`, zkir, pre: synPre(`divmod${bits}`, [x], [q, r]), expectOutputs: [q, r] });
      addVector({ group: `synthetic divmod${bits}`, kind: `a=${x}, quotient and remainder swapped`, zkir, pre: synPre(`divmod${bits}`, [x], [r, (q + 1n) % P]) });
    }
  }
  // One output only is not a legal div_mod.
  const bad = writeCircuit('divmod_one', {
    do_communications_commitment: true, inputs: [{ name: '%a.0', type: N }], outputs: [N],
    instructions: [{ op: 'div_mod_power_of_two', outputs: ['%q.1'], val: '%a.0', bits: 8 }, { op: 'output', vals: ['%q.1'] }],
  });
  addVector({ group: 'synthetic divmod', kind: 'one output', zkir: bad, pre: synPre('divmod_one', [300n], [1n]) });
}

// ---------------------------------------------------------------- cryptography

const rand = (() => { let s = 0x2545f4914f6cdd1dn; return () => { s ^= s << 13n; s &= (1n << 64n) - 1n; s ^= s >> 7n; s ^= s << 17n; s &= (1n << 64n) - 1n; return s; }; })();
const randField = () => { let x = 0n; for (let i = 0; i < 4; i++) x = (x << 64n) | rand(); return x % P; };
const randBytes = (n) => Uint8Array.from({ length: n }, () => Number(rand() & 0xffn));
const hex = (b) => Buffer.from(b).toString('hex');

const crypto = { transientHash: [], transientCommit: [], persistentHash: [], sha256: [] };

// transient_hash on n field elements, through the runtime's API, and through
// the real ZKIR evaluator (a circuit that hashes its inputs and compares).
const thashCases = [[], [0n], [P - 1n], [1n, 2n], [0n, 0n, 0n], [P - 1n, P - 1n, P - 1n, P - 1n]];
for (const n of [1, 2, 3, 4, 5, 6, 7, 8, 9, 16, 17, 33]) thashCases.push(Array.from({ length: n }, randField));
for (const xs of thashCases) {
  const h = ocrt.valueToBigInt(ocrt.transientHash(fieldAV(xs).alignment, fieldAV(xs).value));
  crypto.transientHash.push({ inputs: dec(xs), expected: String(h) });
  const name = `thash${xs.length}`;
  const zkir = writeCircuit(name, {
    do_communications_commitment: false,
    inputs: [...xs.map((_, i) => ({ name: `%x.${i}`, type: N })), { name: `%e.${xs.length}`, type: N }], outputs: [],
    instructions: [
      { op: 'transient_hash', output: `%h.${xs.length + 1}`, inputs: xs.map((_, i) => `%x.${i}`) },
      { op: 'constrain_eq', a: `%h.${xs.length + 1}`, b: `%e.${xs.length}` },
      { op: 'output', vals: [] },
    ],
  });
  addVector({ group: 'synthetic transient_hash', kind: `${xs.length} inputs, runtime's hash`, zkir, pre: synPre(name, [...xs, h]) });
  addVector({ group: 'synthetic transient_hash', kind: `${xs.length} inputs, hash+1`, zkir, pre: synPre(name, [...xs, (h + 1n) % P]) });
}

// transient_commit, as the communications commitment: `communicationCommitment`
// of two AlignedValues is transient_commit(fields(input) ++ fields(output), rand).
for (const [ins, outs] of [[[], []], [[0n], []], [[], [P - 1n]], [[1n, 2n], [3n]], [Array.from({ length: 7 }, randField), [randField(), randField()]]]) {
  for (const r of [0n, 1n, randField()]) {
    const c = frFromHex(ocrt.communicationCommitment(fieldAV(ins), fieldAV(outs), frToHex(r)));
    crypto.transientCommit.push({ inputs: dec([...ins, ...outs]), opening: String(r), expected: String(c), note: 'communicationCommitment' });
  }
}

// persistent_hash: the runtime hashes an AlignedValue; the runtime also gives
// its field form. The Lean side must get the same digest from the field form.
const atoms = {
  f: { kind: 'field' }, c: { kind: 'compress' },
  ...Object.fromEntries([0, 1, 2, 8, 30, 31, 32, 33, 62, 63, 64, 100].map((n) => [`b${n}`, { kind: 'bytes', length: n }])),
};
const valueFor = (a, mode) => {
  if (a.kind === 'field') return mode === 'zero' ? 0n : mode === 'max' ? P - 1n : randField();
  const b = mode === 'zero' ? new Uint8Array(a.length) : mode === 'max' ? new Uint8Array(a.length).fill(255) : randBytes(a.length);
  return b;
};
const avOf = (al, vals) => ({
  value: al.map((a, i) => (a.kind === 'field' ? (rt.bigIntToValue(vals[i])[0] ?? new Uint8Array(0)) : (() => { let e = vals[i].length; while (e > 0 && vals[i][e - 1] === 0) e--; return vals[i].slice(0, e); })())),
  alignment: al.map(atomJ),
});
const phashAlignments = [
  ['f'], ['b1'], ['b2'], ['b8'], ['b30'], ['b31'], ['b32'], ['b33'], ['b62'], ['b63'], ['b64'], ['b100'],
  ['f', 'f'], ['b1', 'f', 'b32'], ['b32', 'b32', 'b32'], ['f', 'b33', 'b1', 'f'], ['b64', 'f', 'b31'], [], ['b0'], ['b0', 'f'],
];
let pk = 0;
for (const names of phashAlignments) {
  const al = names.map((n) => atoms[n]);
  for (const mode of ['zero', 'max', 'rand']) {
    const vals = al.map((a) => valueFor(a, mode));
    const av = avOf(al, vals);
    let digest, fields;
    try {
      digest = ocrt.persistentHash(av.alignment, av.value)[0];
      fields = fieldsOf(av);
    } catch (e) { console.error(`persistentHash ${names}: ${e}`); continue; }
    const d = new Uint8Array(32); d.set(digest);   // the runtime strips trailing zero bytes
    crypto.persistentHash.push({ alignment: al.map(atomJ), inputs: dec(fields), expected: hex(d), note: `${names.join(',')} ${mode}` });
    // Through the real evaluator: hash, split into two limbs, compare with the runtime's digest.
    const lo = BigInt('0x' + hex(d.slice(0, 31).reverse())), hi = BigInt(d[31]);
    const name = `phash${pk++}`;
    const nIn = fields.length;
    const zkir = writeCircuit(name, {
      do_communications_commitment: false,
      inputs: [...fields.map((_, i) => ({ name: `%x.${i}`, type: N })), { name: `%lo.${nIn}`, type: N }, { name: `%hi.${nIn + 1}`, type: N }], outputs: [],
      instructions: [
        { op: 'persistent_hash', output: `%h.${nIn + 2}`, alignment: al.map(atomJ), inputs: fields.map((_, i) => `%x.${i}`) },
        { op: 'bytes_into_natives', outputs: [`%l.${nIn + 3}`, `%u.${nIn + 4}`], bytes: `%h.${nIn + 2}` },
        { op: 'constrain_eq', a: `%l.${nIn + 3}`, b: `%lo.${nIn}` },
        { op: 'constrain_eq', a: `%u.${nIn + 4}`, b: `%hi.${nIn + 1}` },
        { op: 'output', vals: [] },
      ],
    });
    addVector({ group: 'synthetic persistent_hash', kind: `${names.join(',')} ${mode}: runtime's digest`, zkir, pre: synPre(name, [...fields, lo, hi]) });
    addVector({ group: 'synthetic persistent_hash', kind: `${names.join(',')} ${mode}: digest with low limb +1`, zkir, pre: synPre(name, [...fields, lo + 1n, hi]) });
  }
}
// Field elements that do not fit the alignment, and surplus elements.
const badPhash = [
  [['b1'], [256n]], [['b31'], [1n << 248n]], [['b32'], [256n, 0n]], [['b32'], [0n, 1n << 248n]], [['b33'], [0n]],
  [['b2'], [1n << 16n]], [['f', 'b1'], [5n]], [['c'], [0n]], [['f', 'c'], [1n, 0n]], [['b62'], [1n << 248n, 0n]],
  [['f'], [1n, 2n]], [['b1'], [7n, 8n, 9n]], [['b32'], [3n, 4n, 5n]], [[], [1n]],
];
for (const [names, fields] of badPhash) {
  const al = names.map((n) => atoms[n]);
  crypto.persistentHash.push({ alignment: al.map(atomJ), inputs: dec(fields), expected: null, note: `${names.join(',')} on ${fields}: decided by the real evaluator` });
  const name = `phash${pk++}`;
  const nIn = fields.length;
  const zkir = writeCircuit(name, {
    do_communications_commitment: true,
    inputs: fields.map((_, i) => ({ name: `%x.${i}`, type: N })), outputs: [N, N],
    instructions: [
      { op: 'persistent_hash', output: `%h.${nIn}`, alignment: al.map(atomJ), inputs: fields.map((_, i) => `%x.${i}`) },
      { op: 'bytes_into_natives', outputs: [`%l.${nIn + 1}`, `%u.${nIn + 2}`], bytes: `%h.${nIn}` },
      { op: 'output', vals: [`%l.${nIn + 1}`, `%u.${nIn + 2}`] },
    ],
  });
  // Outputs claimed from the digest of the parsed prefix where one exists (surplus cases).
  let outs = [0n, 0n];
  const prefix = { f: 1, b1: 1, b32: 2 }[names[0]];
  if (names.length === 1 && fields.length > prefix && fields.slice(0, prefix).every((x) => x < 1n << 248n)) {
    const pfx = fields.slice(0, prefix);
    const av = names[0] === 'f' ? fieldAV(pfx) : { value: [(() => { const b = new Uint8Array(names[0] === 'b1' ? 1 : 32); if (names[0] === 'b1') b[0] = Number(pfx[0]); else { const hiB = pfx[0], loB = pfx[1]; for (let i = 0; i < 31; i++) b[i] = Number((loB >> BigInt(8 * i)) & 0xffn); b[31] = Number(hiB); } let e = b.length; while (e > 0 && b[e - 1] === 0) e--; return b.slice(0, e); })()], alignment: al.map(atomJ) };
    const d = new Uint8Array(32); d.set(ocrt.persistentHash(av.alignment, av.value)[0]);
    outs = [BigInt('0x' + hex(d.slice(0, 31).reverse())), BigInt(d[31])];
  } else if (names.length === 0) {
    const d = new Uint8Array(32); d.set(ocrt.persistentHash([], [])[0]);
    outs = [BigInt('0x' + hex(d.slice(0, 31).reverse())), BigInt(d[31])];
  }
  addVector({ group: 'synthetic persistent_hash', kind: `${names.join(',')} on ${fields}`, zkir, pre: synPre(name, fields, outs), expectOutputs: outs });
}

// The JSON reader: operands the Rust loader (`jsonIrToBinary`) accepts or rejects.
const { jsonIrToBinary } = await import('@midnightntwrk/zkir-v3');
const reader = [];
{
  const leHex = (v) => { let h = ''; for (let y = v; ; y >>= 8n) { h += (y & 0xffn).toString(16).padStart(2, '0'); if (y < 256n) break; } return h; };
  const operands = [
    '0x05', '0X05', '-0x05', '0x0500', '0x' + '05' + '00'.repeat(31), '0x' + '05' + '00'.repeat(32), '0x' + leHex(P - 1n), '0x' + leHex(P),
    '-0x' + leHex(P - 1n), '0x' + leHex(1n << 255n), '0x', '0x5', '0xzz', '5', '-5', '%a.0', '%b.9', '-%a.0', '0x-05', '--0x05',
  ];
  for (const o of operands) {
    const text = JSON.stringify({
      version: { major: 3, minor: 1 }, do_communications_commitment: false,
      inputs: [{ name: '%a.0', type: N }], outputs: [],
      instructions: [{ op: 'constrain_eq', a: '%a.0', b: o }, { op: 'output', vals: [] }],
    });
    let ok;
    try { jsonIrToBinary(text); ok = true; } catch { ok = false; }
    reader.push({ operand: o, text, realAccepts: ok });
  }
}

// SHA-256 against Node's.
const { createHash } = await import('node:crypto');
for (const n of [0, 1, 3, 31, 32, 33, 55, 56, 57, 63, 64, 65, 100, 119, 120, 128, 200, 1000]) {
  const b = randBytes(n);
  crypto.sha256.push({ bytes: hex(b), expected: createHash('sha256').update(b).digest('hex') });
}

// ---------------------------------------------------------------- run the real checker

const jobs = vectors.map((v) => ({ zkir: v.zkir, preimage: hex(serializePreimage({ ...v.pre, keyLocation: v.pre.keyLocation })) }));
// The codec must reproduce the runtime's bytes exactly.
for (const call of calls_) {
  if (!call.pre) continue;
  const raw = rt.proofDataIntoSerializedPreimage(call.pd.input, call.pd.output, call.pd.publicTranscript, call.pd.privateTranscriptOutputs, call.circuit);
  if (Buffer.compare(Buffer.from(serializePreimage(call.pre)), Buffer.from(raw)) !== 0) throw new Error(`preimage codec does not round-trip for ${call.label}`);
}
const jobsFile = path.join(outDir, 'jobs.json');
fs.writeFileSync(jobsFile, JSON.stringify(jobs));
const results = new Array(jobs.length);
let start = 0;
while (start < jobs.length) {
  const r = spawnSync(process.execPath, [path.join(here, 'semantics-check.mjs'), jobsFile, String(start)], { maxBuffer: 1 << 30, encoding: 'utf-8' });
  let last = start - 1;
  for (const line of r.stdout.split('\n')) {
    if (!line) continue;
    const res = JSON.parse(line);
    results[res.i] = res;
    last = res.i;
  }
  if (last === jobs.length - 1) break;
  // The child died on job last+1.
  const err = (r.stderr.match(/^(\w*Error: .*)$/m) ?? [r.stderr.trim().split('\n').at(-1)])[0];
  results[last + 1] = { i: last + 1, ok: false, error: `crashed: ${err}`, crashed: true };
  start = last + 2;
}

const classify = (res) => {
  if (res.ok) return 'accept';
  const e = res.error;
  if (res.crashed) return 'premise';   // a transcript read past its end: an instruction that cannot run
  if (/Public transcript input mismatch/.test(e)) return 'pt-mismatch';
  if (/Transcripts not fully consumed/.test(e)) return 'unconsumed';
  if (/Communications commitment mismatch|Expected communications/.test(e)) return 'commitment';
  if (/raw inputs/.test(e)) return 'inputs';
  return 'premise';
};
vectors.forEach((v, i) => {
  const res = results[i];
  v.real = { ok: res.ok, reason: classify(res), error: res.error ?? null, skips: res.skips ?? null };
  delete v.pre;
});

fs.writeFileSync(path.join(outDir, 'vectors.json'), JSON.stringify({ vectors, crypto, reader }, null, 1));
const count = (f) => vectors.filter(f).length;
console.log(`${vectors.length} vectors (${count((v) => v.real.ok)} accepted by the real checker, ${count((v) => !v.real.ok)} rejected); ` +
  `${calls_.filter((c) => c.pre).length} calls ran, ${calls_.filter((c) => !c.pre).length} failed in JS; crypto cases: ` +
  Object.entries(crypto).map(([k, v]) => `${k} ${v.length}`).join(', '));
