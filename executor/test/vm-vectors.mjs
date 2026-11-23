// Test vectors for the differential test of Damp/Ledger/Vm.lean (the model of
// Midnight's on-chain VM) against the real VM (see docs/ledger-model.md,
// test/vm.sh).
//
// 1. Runs calls of every example contract through the generic executor, with
//    the runtime's `QueryContext.prototype.query` wrapped so that every program
//    the executor sends to the ledger is captured with the context it ran in:
//    the VM stack `[context, effects, state]` and the instructions. These are
//    exactly the instruction sequences Damp emits for each ledger operation,
//    with their operands evaluated.
// 2. Derives variants of each program (instructions dropped, swapped,
//    truncated; cached flags and pushPath flipped; immediates, stack offsets,
//    skips and counts changed; the state's fields replaced by values of other
//    shapes or by counters near 2^64), most of which fail, plus a few
//    synthetic programs for corners the examples do not reach.
// 3. Runs each through the real VM twice: `runProgram` (the bare VM: final
//    stack with strengths, and the values `popeq` read) and
//    `QueryContext.query` (what the executor calls: the new state, the
//    effects and the reads, or a rejection), recording the outcome.
// 4. Writes vectors.json for the Lean executable `damp-vm-test`, which runs the
//    model on the same inputs and compares.
//
// Instructions are written to the Lean side as Damp's own `Op Fr` (operands
// as field elements, converted from the runtime's atoms as the executor's
// `fieldsOfAligned` does), so the model's conversion back (`Op.toR`) is
// exercised too.
//
// Usage: node test/vm-vectors.mjs <dir of contract.json builds> <out dir>

import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import * as rt from '@midnight-ntwrk/compact-runtime';
import * as ocrt from '@midnightntwrk/onchain-runtime-v4';
import { makeContract } from '../src/executor.mjs';

const here = path.dirname(fileURLToPath(import.meta.url));
const root = path.resolve(process.argv[2] ?? path.join(here, '..', '..', 'build', 'vm-ledger', 'lean'));
const outDir = path.resolve(process.argv[3] ?? path.join(here, '..', '..', 'build', 'vm-ledger', 'vectors'));
fs.mkdirSync(outDir, { recursive: true });

const COIN_PK = '0'.repeat(64);
const costModel = ocrt.CostModel.initialCostModel();

// ---------------------------------------------------------------- capture

const captures = [];
let capturing = true;
const realQuery = ocrt.QueryContext.prototype.query;
ocrt.QueryContext.prototype.query = function (ops, cm, gasLimit) {
  if (capturing) captures.push({ qc: this, ops: structuredClone(ops) });
  return realQuery.call(this, ops, cm, gasLimit);
};

// ---------------------------------------------------------------- contract calls

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
  note: ({ privateState }) => [privateState, 5n],
};
const constructorArgs = { vault: [rt.persistentHash(new rt.CompactTypeBytes(32), vaultKey), 40n] };
const rootOf = (field) => (c) => c.contract.ledger(c.state ?? c.init.currentContractState.data)[field].root();
const rootIn = (field, k) => (c) => c.contract.ledger(c.state ?? c.init.currentContractState.data)[field].lookup(k).root();

// The calls of test/semantics-vectors.mjs, then every circuit of every
// example with zero arguments and with small non-zero ones.
const listed = [
  ['step', 'step', [5n, true, 42n]], ['step', 'step', [5n, false, 42n]], ['step', 'step', [5n, true, 5000n]],
  ['counter', 'bump', [12n, true, false]], ['counter', 'bump', [12n, true, true]], ['counter', 'bump', [12n, false, false]],
  ['counter', 'bump', [600n, true, false]], ['counter', 'arith', [9n, 4n, 100n]], ['counter', 'arith', [4n, 4n, 100n]],
  ['counter', 'arith', [3n, 4n, 100n]],
  ['shapes', 'move', [{ x: 5n, y: 2n }, [1n, 2n, 3n], true, true]], ['shapes', 'move', [{ x: 5n, y: 2n }, [1n, 2n, 3n], false, true]],
  ['shapes', 'pay', [77n, 10n, 3n, 2n]], ['shapes', 'pay', [77n, 5n, 2n, 2n]], ['shapes', 'pay', [78n, 1n, 7n, 9n]],
  ['loops', 'tally', [[1n, 2n, 3n, 4n], [true, false, true, true], 3n]],
  ['bytes', 'claim', [bytes(32, 1, 2), bytes(8, 3, 4), true]], ['bytes', 'claim', [admin, bytes(8, 3, 4), true]],
  ['bytes', 'store', [bytes(64, 9, 200), 12345n]],
  ['extras', 'advance', [0, bytes(32, 1, 1), { is_some: true, value: 500n }, 42n]],
  ['extras', 'advance', [1, bytes(32, 1, 1), { is_some: true, value: 500n }, 42n]],
  ['extras', 'advance', [2, bytes(32, 3, 3), { is_some: false, value: 0n }, 44n]],
  ['vault', 'spend', [30n]], ['vault', 'spend', [5n]], ['vault', 'spend', [6n]],
  ['structures', 'tick', [5n, 10n, false]], ['structures', 'tick', [3n, 2n, false]], ['structures', 'tick', [1n, 100n, true]],
  ['structures', 'books', [7n, false]], ['structures', 'books', [8n, false]], ['structures', 'books', [9n, true]],
  ['structures', 'dequeue', []], ['structures', 'enqueue', [11n]], ['structures', 'enqueue', [0n]], ['structures', 'dequeue', []],
  ['structures', 'enqueue', [5n]], ['structures', 'enqueue', [6n]], ['structures', 'dequeue', []],
  ['structures', 'plant', [1n, 2n, 3n, bytes(32, 4, 5)]], ['structures', 'plant', [6n, 7n, 16n, bytes(32, 8, 9)]],
  ['structures', 'check', (c) => [rootOf('tree')(c), false]], ['structures', 'check', [{ field: 123n }, true]],
  ['structures', 'record', (c) => [bytes(32, 1, 2), bytes(32, 3, 4), bytes(32, 5, 6), 2n, rootOf('hist')(c), 0n]],
  ['structures', 'record', (c) => [bytes(32, 7, 8), bytes(32, 9, 10), bytes(32, 11, 12), 5n, rootOf('hist')(c), 1n]],
  ['structures', 'record', [bytes(32, 1, 2), bytes(32, 3, 4), bytes(32, 5, 6), 2n, { field: 99n }, 2n]],
  ['structures', 'stamp', [0n]], ['structures', 'stamp', [5n]],
  ['structures_nested', 'vote', [1n, 5n]], ['structures_nested', 'vote', [1n, 2n]], ['structures_nested', 'vote', [2n, 0n]],
  ['structures_nested', 'group', [7n, 1n, 5n, false]], ['structures_nested', 'group', [7n, 2n, 100n, false]],
  ['structures_nested', 'group', [7n, 1n, 100n, true]],
  ['structures_nested', 'join', [1n, 10n, false]], ['structures_nested', 'join', [1n, 11n, false]], ['structures_nested', 'join', [2n, 12n, true]],
  ['structures_nested', 'enqueue', [1n, 10n]], ['structures_nested', 'enqueue', [1n, 11n]], ['structures_nested', 'enqueue', [2n, 13n]],
  ['structures_nested', 'grow', [1n, 10n, 5n, { field: 0n }, false]],
  ['structures_nested', 'grow', (c) => [1n, 20n, 6n, rootIn('trees', 1n)(c), false]],
  ['structures_nested', 'grow', [1n, 30n, 7n, { field: 0n }, true]],
  ['structures_nested', 'hgrow', [1n, 10n, 5n, { field: 0n }, 0n]],
  ['structures_nested', 'hgrow', (c) => [1n, 20n, 6n, rootIn('hists', 1n)(c), 0n]],
  ['structures_nested', 'hgrow', [1n, 40n, 8n, { field: 0n }, 2n]],
  ['tuned', 'settle', [[1n, 2n, 3n, 4n], true]], ['tuned', 'settle', [[65535n, 65535n, 65535n, 65535n], true]],
  // Unshielded spends (effects slot 8) and inputs/outputs (6, 7): an `Either` with one side set, and with
  // both (rejected by the runtime's typed decoding of the effects, executor/test/either-both.mjs).
  ['tokens', 'mintUTo', [5n, { is_left: false, left: { bytes: bytes(32, 0, 0) }, right: { bytes: bytes(32, 7, 7) } }]],
  ['tokens', 'mintUTo', [5n, { is_left: true, left: { bytes: bytes(32, 9, 9) }, right: { bytes: bytes(32, 0, 0) } }]],
  ['tokens', 'mintUTo', [5n, { is_left: false, left: { bytes: bytes(32, 9, 9) }, right: { bytes: bytes(32, 7, 7) } }]],
  ['tokens', 'mintUTo', [5n, { is_left: true, left: { bytes: bytes(32, 9, 9) }, right: { bytes: bytes(32, 7, 7) } }]],
  ['tokens', 'sendU', [5n, { is_left: false, left: { bytes: bytes(32, 0, 0) }, right: { bytes: bytes(32, 7, 7) } }]],
  ['tokens', 'sendU', [5n, { is_left: false, left: { bytes: bytes(32, 1, 0) }, right: { bytes: bytes(32, 7, 7) } }]],
];

/** A JS value of a shape: every leaf from `leaf(ty)`. */
function build(shape, leaf) {
  switch (shape.kind) {
    case 'struct': return Object.fromEntries(shape.fields.map((f, i) => [shape.fieldNames[i], build(f, leaf)]));
    case 'tuple': return shape.elems.map((e) => build(e, leaf));
    case 'vector': return Array.from({ length: shape.length }, () => build(shape.elem, leaf));
    default: return leaf(shape);
  }
}
const zeroLeaf = (ty) => (ty.kind === 'bool' ? false : ty.kind === 'bytes' ? new Uint8Array(ty.length) : ty.kind === 'enum' ? 0 : 0n);
const smallLeaf = (ty) => {
  switch (ty.kind) {
    case 'bool': return true;
    case 'bytes': return bytes(ty.length, 3, 4);
    case 'enum': return Math.min(1, Number(ty.max));
    case 'uint': return BigInt(ty.max) < 3n ? BigInt(ty.max) : 3n;
    default: return 3n;
  }
};

const contracts = fs.readdirSync(root).filter((d) => fs.existsSync(path.join(root, d, 'contract.json'))).sort();
const loaded = new Map();
async function load(name) {
  if (!loaded.has(name)) {
    const spec = JSON.parse(fs.readFileSync(path.join(root, name, 'contract.json'), 'utf-8'));
    const contract = makeContract(spec, witnesses);
    let init;
    try {
      init = await contract.initialState(rt.createConstructorContext({}, COIN_PK), ...(constructorArgs[name] ?? []));
    } catch (e) {
      // A constructor taking arguments: try zeros.
      const args = spec.constructor?.args?.map((a) => build(a.shape, zeroLeaf)) ?? [];
      init = await contract.initialState(rt.createConstructorContext({}, COIN_PK), ...args);
    }
    loaded.set(name, { spec, contract, init, state: undefined });
  }
  return loaded.get(name);
}

async function call(name, circuit, argsOf) {
  const c = await load(name);
  let args;
  try { args = typeof argsOf === 'function' ? argsOf(c) : argsOf; } catch { return; }
  const ctx = rt.createCircuitContext({
    circuitId: circuit, contractAddress: rt.dummyContractAddress(),
    coinPublicKeyOrZswapState: c.init.currentZswapLocalState.coinPublicKey,
    contractState: c.state ?? c.init.currentContractState, privateState: c.init.currentPrivateState, time: 0,
  });
  try {
    const run = await c.contract.circuits[circuit](ctx, ...args);
    c.state = run.context.callContext.currentQueryContext.state;
  } catch { /* a failing call still sent its earlier ledger statements */ }
}

for (const [name, circuit, args] of listed) if (contracts.includes(name)) await call(name, circuit, args);
for (const name of contracts) {
  const c = await load(name);
  for (const circ of c.spec.circuits) {
    await call(name, circ.name, circ.args.map((a) => build(a.shape, zeroLeaf)));
    await call(name, circ.name, circ.args.map((a) => build(a.shape, smallLeaf)));
  }
}
capturing = false;
console.error(`captured ${captures.length} ledger requests from ${contracts.length} contracts`);

// ---------------------------------------------------------------- encodings for Lean

const leNat = (bs) => { let x = 0n; for (let i = bs.length - 1; i >= 0; i--) x = (x << 8n) | BigInt(bs[i]); return x; };
const natLe = (x) => { const out = []; while (x > 0n) { out.push(Number(x & 0xffn)); x >>= 8n; } return Uint8Array.from(out); };
const atomStr = (a) => (a.value.tag === 'bytes' ? `b${a.value.length}` : a.value.tag === 'field' ? 'f' : 'c');
const avJ = (av) => ({ a: av.alignment.map(atomStr), x: av.value.map((bs) => leNat(bs).toString()) });

/** A runtime EncodedStateValue as the Lean side reads it. */
function svJ(e) {
  switch (e.tag) {
    case 'null': return { t: 'n' };
    case 'cell': return { t: 'c', v: avJ(e.content) };
    case 'map': return { t: 'm', e: [...e.content.entries()].map(([k, v]) => [avJ(k), svJ(v)]) };
    case 'array': return { t: 'a', e: e.content.map(svJ) };
    case 'boundedMerkleTree': {
      const [h, leaves] = e.content;
      return { t: 'b', h, l: [...leaves.entries()].map(([i, [hash]]) => [i.toString(), leNat(hash).toString()]) };
    }
    default: throw new Error(`unknown state value ${e.tag}`);
  }
}

// Field elements of an atom under its alignment (the executor's fieldsOfAligned).
const LIMB = 248n;
function limbsOf(bs, n) {
  let x = 0n;
  for (let i = Math.min(bs.length, n) - 1; i >= 0; i--) x = (x << 8n) | BigInt(bs[i]);
  const count = Math.ceil(n / 31);
  return Array.from({ length: count }, (_, j) => (x >> (LIMB * BigInt(count - 1 - j))) & ((1n << LIMB) - 1n));
}
const fieldsOfAtom = (a, bs) => (a.value.tag === 'bytes' && a.value.length > 31 ? limbsOf(bs, a.value.length) : [leNat(bs)]);
const alignedJ = (av) => ({ align: av.alignment.map(atomStr), vals: av.alignment.flatMap((a, i) => fieldsOfAtom(a, av.value[i])).map(String) });

/** A pushed state value as Damp's `StateLit` (only the forms Damp writes). */
function litJ(e) {
  switch (e.tag) {
    case 'null': return { t: 'n' };
    case 'cell': return { t: 'c', v: alignedJ(e.content) };
    case 'map': if (e.content.size === 0) return { t: 'm' }; break;
    case 'array': return { t: 'a', e: e.content.map(litJ) };
    case 'boundedMerkleTree': if (e.content[1].size === 0) return { t: 'b', h: e.content[0] }; break;
  }
  throw new Error('a state value Damp cannot write literally');
}

/** A runtime instruction as Damp's `Op Fr` (the inverse of the executor's `runtimeOp`). */
function opJ(op) {
  if (typeof op === 'string') return { o: op };
  const [k, v] = Object.entries(op)[0];
  switch (k) {
    case 'popeq': return { o: 'popeq', cached: v.cached };
    case 'addi': case 'subi': return { o: k, imm: String(v.immediate) };
    case 'push':
      if (v.value.tag === 'cell') return { o: 'push', storage: v.storage, v: alignedJ(v.value.content) };
      if (v.value.tag === 'null') return { o: 'pushNull', storage: v.storage };
      return { o: 'pushState', storage: v.storage, v: litJ(v.value) };
    case 'branch': case 'jmp': return { o: k, n: v.skip };
    case 'concat': return { o: v.cached ? 'concatCached' : 'concat', n: v.n };
    case 'rem': return { o: 'rem', cached: v.cached };
    case 'dup': case 'swap': return { o: k, n: v.n };
    case 'ins': return { o: 'ins', cached: v.cached, n: v.n };
    case 'idx': {
      const stackKeys = v.path.filter((p) => p.tag === 'stack').length;
      if (stackKeys === 0) return { o: 'idx', cached: v.cached, pushPath: v.pushPath, path: v.path.map((p) => alignedJ(p.value)) };
      if (stackKeys === 1 && v.path.at(-1).tag === 'stack' && v.cached && !v.pushPath) {
        return { o: 'idxStack', path: v.path.slice(0, -1).map((p) => alignedJ(p.value)) };
      }
      throw new Error('an idx Damp cannot write');
    }
    default: throw new Error(`unknown op ${k}`);
  }
}

// ---------------------------------------------------------------- running the real VM

const errText = (e) => (e instanceof Error ? e.message : String(e)).split('\n')[0].slice(0, 200);
const reads = (events) => events.filter((e) => e.tag === 'read').map((e) => avJ(e.content));

function stackJ(st) {
  const out = [];
  for (let i = 0; i < st.length(); i++) out.push({ v: svJ(st.get(i).encode()), s: st.isStrong(i) });
  return out;
}

function runVm(entries, ops) {
  const st = new ocrt.VmStack();
  for (const e of entries) st.push(e.value, e.strong);
  try {
    const r = ocrt.runProgram(st, ops, costModel);
    return { ok: true, stack: stackJ(r.stack), reads: reads(r.events) };
  } catch (e) { return { ok: false, err: errText(e) }; }
}

function runQuery(qc, ops) {
  try {
    const r = qc.query(ops, costModel);
    const st = r.context.toVmStack();
    return { ok: true, state: svJ(st.get(2).encode()), effects: svJ(st.get(1).encode()), reads: reads(r.events) };
  } catch (e) { return { ok: false, err: errText(e) }; }
}

// ---------------------------------------------------------------- variants

const clone = (ops) => structuredClone(ops);
const kindOf = (op) => (typeof op === 'string' ? op : Object.keys(op)[0]);

function programVariants(ops) {
  const out = [];
  const add = (kind, p) => out.push({ kind, ops: p });
  for (let i = 0; i < ops.length; i++) {
    const p = clone(ops); p.splice(i, 1); add(`drop ${i}`, p);
    if (i + 1 < ops.length) { const q = clone(ops); [q[i], q[i + 1]] = [q[i + 1], q[i]]; add(`swap ${i},${i + 1}`, q); }
    const k = kindOf(ops[i]);
    const v = typeof ops[i] === 'string' ? null : ops[i][k];
    const tweak = (label, f) => { const q = clone(ops); f(q[i][k]); add(`${label} at ${i}`, q); };
    if (['idx', 'ins', 'rem', 'popeq', 'concat'].includes(k)) tweak('flip cached', (o) => { o.cached = !o.cached; });
    if (k === 'idx') {
      tweak('flip pushPath', (o) => { o.pushPath = !o.pushPath; });
      if (v.path.length > 1) tweak('shorter path', (o) => { o.path.pop(); });
      if (v.path[0]?.tag === 'value' && v.path[0].value.alignment.length === 1 && v.path[0].value.alignment[0].value.tag === 'bytes'
          && v.path[0].value.alignment[0].value.length === 1) {
        tweak('key+1', (o) => { const x = leNat(o.path[0].value.value[0]) + 1n; o.path[0].value.value[0] = natLe(x % 256n); });
        tweak('key=200', (o) => { o.path[0].value.value[0] = natLe(200n); });
      }
    }
    if (k === 'addi' || k === 'subi') {
      // The VM's immediates are `u32`: 2^32 and above are rejected when the program is decoded.
      for (const n of [0, 1, 65535, 2 ** 32 - 1, 2 ** 32, 2 ** 32 + 1, 2 ** 53]) tweak(`imm=${n}`, (o) => { o.immediate = n; });
      const q = clone(ops); q[i] = { [k === 'addi' ? 'subi' : 'addi']: { immediate: v.immediate } }; add(`addi<->subi at ${i}`, q);
    }
    if (k === 'dup' || k === 'swap') { tweak('n+1', (o) => { o.n += 1; }); tweak('n+3', (o) => { o.n += 3; }); }
    if (k === 'branch' || k === 'jmp') { tweak('skip+1', (o) => { o.skip += 1; }); tweak('skip+9', (o) => { o.skip += 9; }); tweak('skip=0', (o) => { o.skip = 0; }); }
    if (k === 'ins') { tweak('n+1', (o) => { o.n += 1; }); if (v.n > 0) tweak('n-1', (o) => { o.n -= 1; }); }
    if (k === 'concat') { tweak('n=2', (o) => { o.n = 2; }); tweak('n=40000', (o) => { o.n = 40000; }); }
    if (k === 'push' && v.value.tag === 'cell' && v.value.content.alignment.length === 1) {
      tweak('push b1', (o) => { o.value.content.alignment = [{ tag: 'atom', value: { tag: 'bytes', length: 1 } }]; });
      tweak('push u64 max', (o) => { o.value.content = { value: [natLe((1n << 64n) - 1n)], alignment: [{ tag: 'atom', value: { tag: 'bytes', length: 8 } }] }; });
      tweak('push null', (o) => { o.value = { tag: 'null' }; });
    }
  }
  for (let n = 1; n < ops.length; n++) add(`first ${n}`, ops.slice(0, n));
  add('popeq appended', [...clone(ops), { dup: { n: 0 } }, { popeq: { cached: false, result: undefined } }]);
  add('pop appended', [...clone(ops), 'pop']);
  add('doubled', [...clone(ops), ...clone(ops)]);
  return out;
}

const cellJs = (alignLen, x) => ocrt.StateValue.newCell({ value: [natLe(x)], alignment: [{ tag: 'atom', value: { tag: 'bytes', length: alignLen } }] });
const fieldCell = (x) => ocrt.StateValue.newCell({ value: [natLe(x)], alignment: [{ tag: 'atom', value: { tag: 'field' } }] });

/** States with one field replaced: the field the program first indexes. */
function stateVariants(qc, ops) {
  const state = qc.toVmStack().get(2);
  const fields = state.asArray();
  if (!fields) return [];
  const first = ops.find((op) => kindOf(op) === 'idx' && op.idx.path[0]?.tag === 'value');
  if (!first) return [];
  const key = first.idx.path[0].value.value[0];
  const i = Number(leNat(key ?? new Uint8Array()));
  if (!(i < fields.length)) return [];
  const replacements = [
    ['null', ocrt.StateValue.newNull()],
    ['empty map', ocrt.StateValue.newMap(new ocrt.StateMap())],
    ['u64 max', cellJs(8, (1n << 64n) - 1n)],
    ['u64 max-1', cellJs(8, (1n << 64n) - 2n)],
    ['u64 2^32', cellJs(8, 1n << 32n)],
    ['u128 2^64', cellJs(16, 1n << 64n)],
    ['field 5', fieldCell(5n)],
    ['array of null', ocrt.StateValue.newArray().arrayPush(ocrt.StateValue.newNull())],
    ['tree of height 3', ocrt.StateValue.newBoundedMerkleTree(new ocrt.StateBoundedMerkleTree(3))],
  ];
  const cur = fields[i];
  if (cur.type() === 'map') {
    const m = cur.asMap();
    let m2 = m;
    m2 = m2.insert({ value: [natLe(7n)], alignment: [{ tag: 'atom', value: { tag: 'field' } }] }, cellJs(8, 9n));
    replacements.push(['map + entry', ocrt.StateValue.newMap(m2)]);
  }
  return replacements.map(([label, v]) => {
    let arr = ocrt.StateValue.newArray();
    fields.forEach((f, j) => { arr = arr.arrayPush(j === i ? v : f); });
    return { label: `field ${i} := ${label}`, qc: new ocrt.QueryContext(new ocrt.ChargedState(arr), ocrt.dummyContractAddress()) };
  });
}

// ---------------------------------------------------------------- vectors

const values = [];          // interned state values (JSON text -> index)
const valueIndex = new Map();
const intern = (v) => {
  const s = JSON.stringify(v);
  if (!valueIndex.has(s)) { valueIndex.set(s, values.length); values.push(v); }
  return valueIndex.get(s);
};
const internStack = (xs) => xs.map(({ v, s }) => ({ v: intern(v), s }));

const vectors = [];
const seen = new Set();
const hasRoot = (ops) => ops.some((op) => op === 'root');

function addVector(group, kind, qc, ops) {
  let lean;
  try { lean = ops.map(opJ); } catch { return; }
  const stack = qc.toVmStack();
  const init = stackJ(stack);
  const k = JSON.stringify([init, lean]);
  if (seen.has(k)) return;
  seen.add(k);
  const entries = [];
  for (let i = 0; i < stack.length(); i++) entries.push({ value: stack.get(i), strong: stack.isStrong(i) });
  const vm = runVm(entries, ops);
  const q = runQuery(qc, ops);
  vectors.push({
    id: vectors.length, group, kind, root: hasRoot(ops),
    init: internStack(init), ops: lean,
    vm: vm.ok ? { ok: true, stack: internStack(vm.stack), reads: vm.reads } : vm,
    query: q.ok ? { ok: true, state: intern(q.state), effects: intern(q.effects), reads: q.reads } : q,
  });
}

const progKey = (c) => JSON.stringify([stackJ(c.qc.toVmStack()), c.ops]);
const distinct = [];
{
  const ks = new Set();
  for (const c of captures) { const k = progKey(c); if (!ks.has(k)) { ks.add(k); distinct.push(c); } }
}
console.error(`${distinct.length} distinct (state, program) pairs`);

for (const [n, c] of distinct.entries()) {
  const group = `request ${n}: ${c.ops.map(kindOf).join(' ')}`;
  addVector(group, 'as emitted', c.qc, c.ops);
  for (const v of programVariants(c.ops)) addVector(group, v.kind, c.qc, v.ops);
  for (const s of stateVariants(c.qc, c.ops)) addVector(group, s.label, s.qc, c.ops);
}

// ---------------------------------------------------------------- synthetic programs

{
  const b = (n) => ({ tag: 'atom', value: { tag: 'bytes', length: n } });
  const f = { tag: 'atom', value: { tag: 'field' } };
  const av = (align, xs) => ({ value: xs.map(natLe), alignment: align });
  const cell = (align, xs) => ({ push: { storage: false, value: { tag: 'cell', content: av(align, xs) } } });
  const scell = (align, xs) => ({ push: { storage: true, value: { tag: 'cell', content: av(align, xs) } } });
  const st = (e) => ({ push: { storage: true, value: e } });
  const emptyState = ocrt.StateValue.newArray().arrayPush(ocrt.StateValue.newNull()).arrayPush(cellJs(8, 5n));
  const qc0 = new ocrt.QueryContext(new ocrt.ChargedState(emptyState), ocrt.dummyContractAddress());
  const long = Array.from({ length: 40 }, (_, i) => BigInt(i + 1));
  const progs = {
    'eq long long': [cell([b(255)], [1n << 2000n]), cell([b(255)], [1n << 2000n]), 'eq', 'pop'],
    'eq long short': [cell([b(255)], [1n << 2000n]), cell([b(1)], [1n]), 'eq', 'pop'],
    'eq many atoms': [cell(long.map(() => b(8)), long), cell(long.map(() => b(8)), long), 'eq', 'pop'],
    'eq same value other alignment': [cell([b(8)], [3n]), cell([b(1)], [3n]), 'eq', { popeq: { cached: false, result: undefined } }],
    'eq equal': [cell([f], [12345n]), cell([f], [12345n]), 'eq', { popeq: { cached: false, result: undefined } }],
    'concat fits': [cell([b(8)], [7n]), cell([f], [9n]), { concat: { cached: false, n: 6 } }, { popeq: { cached: false, result: undefined } }],
    'concat exact bound': [cell([b(8)], [7n]), cell([f], [9n]), { concat: { cached: false, n: 4 } }, 'pop'],
    'concat too small': [cell([b(8)], [7n]), cell([f], [9n]), { concat: { cached: false, n: 3 } }, 'pop'],
    'concat zero atoms': [cell([b(8)], [0n]), cell([b(8)], [300n]), { concat: { cached: true, n: 7 } }, { popeq: { cached: false, result: undefined } }],
    'type of everything': [st({ tag: 'null' }), 'type', { popeq: { cached: false, result: undefined } },
      st({ tag: 'map', content: new Map() }), 'type', { popeq: { cached: false, result: undefined } },
      cell([f], [1n]), 'type', { popeq: { cached: false, result: undefined } },
      { dup: { n: 0 } }, 'type', { popeq: { cached: false, result: undefined } }],
    'size of array': [{ dup: { n: 0 } }, 'size', { popeq: { cached: false, result: undefined } }],
    'size of cell': [cell([f], [1n]), 'size', 'pop'],
    'member of array': [{ dup: { n: 0 } }, cell([f], [1n]), 'member', 'pop'],
    'lt not u64': [cell([f], [1n << 70n]), cell([f], [1n]), 'lt', 'pop'],
    'lt u64': [cell([f], [3n]), cell([b(16)], [5n]), 'lt', { popeq: { cached: false, result: undefined } }],
    'add overflow': [cell([b(8)], [(1n << 64n) - 1n]), cell([b(8)], [1n]), 'add', 'pop'],
    'add/sub': [cell([b(8)], [10n]), cell([b(8)], [3n]), 'sub', { popeq: { cached: false, result: undefined } },
      cell([b(8)], [3n]), cell([b(8)], [10n]), 'sub', 'pop'],
    'and/or/neg': [cell([b(1)], [1n]), cell([b(1)], [0n]), 'and', { popeq: { cached: false, result: undefined } },
      cell([b(1)], [1n]), cell([b(1)], [0n]), 'or', 'neg', { popeq: { cached: false, result: undefined } }],
    'neg of 2': [cell([b(1)], [2n]), 'neg', 'pop'],
    'branch on 2': [cell([b(1)], [2n]), { branch: { skip: 1 } }, 'pop', { dup: { n: 0 } }, 'pop'],
    'branch on two atoms': [cell([b(1), b(1)], [0n, 0n]), { branch: { skip: 1 } }, { jmp: { skip: 0 } }],
    'branch on map': [st({ tag: 'map', content: new Map() }), { branch: { skip: 0 } }],
    'map ins/idx/rem': [{ dup: { n: 0 } }, cell([b(1)], [0n]), st({ tag: 'map', content: new Map() }), cell([f], [4n]), scell([b(8)], [9n]),
      { ins: { cached: false, n: 1 } }, { dup: { n: 0 } }, { idx: { cached: false, pushPath: false, path: [{ tag: 'value', value: av([f], [4n]) }] } },
      { popeq: { cached: false, result: undefined } }, cell([f], [4n]), { rem: { cached: true } }, 'size', { popeq: { cached: false, result: undefined } },
      'pop', 'pop'],
    'tree ins/idx/size/type': [st({ tag: 'boundedMerkleTree', content: [3, new Map()] }), cell([b(8)], [5n]), scell([b(32)], [77n]),
      { ins: { cached: false, n: 1 } }, { dup: { n: 0 } }, { idx: { cached: false, pushPath: false, path: [{ tag: 'value', value: av([b(8)], [5n]) }] } },
      { popeq: { cached: false, result: undefined } }, { dup: { n: 0 } }, { idx: { cached: false, pushPath: false, path: [{ tag: 'value', value: av([b(8)], [4n]) }] } },
      'type', { popeq: { cached: false, result: undefined } }, { dup: { n: 0 } }, 'size', { popeq: { cached: false, result: undefined } },
      'type', { popeq: { cached: false, result: undefined } }],
    'tree idx out of range': [st({ tag: 'boundedMerkleTree', content: [3, new Map()] }),
      { idx: { cached: false, pushPath: false, path: [{ tag: 'value', value: av([b(8)], [8n]) }] } }, 'pop'],
    'tree ins out of range': [st({ tag: 'boundedMerkleTree', content: [3, new Map()] }), cell([b(8)], [8n]), scell([b(32)], [77n]),
      { ins: { cached: false, n: 1 } }, 'pop'],
    'tree ins non-hash': [st({ tag: 'boundedMerkleTree', content: [3, new Map()] }), cell([b(8)], [1n]), scell([b(32), b(1)], [77n, 1n]),
      { ins: { cached: false, n: 1 } }, 'pop'],
    'array ins out of range': [{ dup: { n: 0 } }, cell([b(1)], [2n]), scell([f], [1n]), { ins: { cached: false, n: 1 } }, 'pop'],
    'idx cached on state': [{ dup: { n: 0 } }, { idx: { cached: true, pushPath: false, path: [{ tag: 'value', value: av([b(1)], [1n]) }] } }, 'pop'],
    'idx cached after visit': [{ dup: { n: 0 } }, { idx: { cached: false, pushPath: false, path: [{ tag: 'value', value: av([b(1)], [1n]) }] } }, 'pop',
      { dup: { n: 0 } }, { idx: { cached: true, pushPath: false, path: [{ tag: 'value', value: av([b(1)], [1n]) }] } }, 'pop'],
    'idx cached on context': [{ dup: { n: 2 } }, { idx: { cached: true, pushPath: false, path: [{ tag: 'value', value: av([b(1)], [2n]) }] } },
      { popeq: { cached: true, result: undefined } }],
    'idx stack key': [{ dup: { n: 2 } }, cell([b(1)], [2n]), { idx: { cached: true, pushPath: true, path: [{ tag: 'stack' }] } }, 'pop', 'pop', 'pop'],
    'weak state returned': [cell([b(1)], [1n]), { swap: { n: 0 } }, 'pop'],
    'stack too short': ['pop', 'pop', 'pop', 'pop'],
    'effects replaced': [{ swap: { n: 0 } }, 'pop', { push: { storage: false, value: { tag: 'null' } } }, { swap: { n: 0 } }],
    'effects map gets an array': [{ swap: { n: 0 } }, cell([b(1)], [0n]), st({ tag: 'array', content: [] }), { ins: { cached: true, n: 1 } }, { swap: { n: 0 } }],
    'type of long array': [st({ tag: 'array', content: Array.from({ length: 16 }, () => ({ tag: 'null' })) }), 'type', 'pop'],
  };
  for (const [name, ops] of Object.entries(progs)) addVector(`synthetic: ${name}`, 'synthetic', qc0, ops);

  // The typed decoding of the effects at the end of a query (`TryFrom<VmValue> for Effects`): an entry
  // written into effects slot `slot` with the key and the value given, well formed or not.
  const P = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001n;
  const h = 0x1234n, a = 0x5678n, u = 0x9abcn, H = (1n << 256n) - 1n;
  const T = [b(1), b(32), b(32)];
  const C = [b(8), b(32), b(32), f];
  const nul = { push: { storage: false, value: { tag: 'null' } } };
  const u128 = (x) => cell([b(16)], [x]);
  const put = (slot, key, val) => [{ swap: { n: 0 } },
    { idx: { cached: true, pushPath: true, path: [{ tag: 'value', value: av([b(1)], [BigInt(slot)]) }] } },
    cell(key[0], key[1]), val, { ins: { cached: true, n: 2 } }, { swap: { n: 0 } }];
  const effs = {
    // slot 3: claimed contract calls, (u64, ContractAddress, HashOutput, Fr) -> ()
    'call ok': [3, [C, [3n, h, h, 5n]], nul],
    'call ok, other alignment': [3, [[b(16), b(32), b(32), b(32)], [3n, h, h, 5n]], nul],
    'call ok, empty cell value': [3, [C, [0n, 0n, 0n, 0n]], cell([], [])],
    'call ok, Fr max': [3, [[b(8), b(32), b(32), b(32)], [3n, H, H, P - 1n]], nul],
    'call, Fr = modulus': [3, [[b(8), b(32), b(32), b(32)], [3n, h, h, P]], nul],
    'call, u64 overflow': [3, [[b(16), b(32), b(32), f], [1n << 64n, h, h, 5n]], nul],
    'call, three atoms': [3, [[b(8), b(32), b(32)], [3n, h, h]], nul],
    'call, five atoms': [3, [[...C, f], [3n, h, h, 5n, 1n]], nul],
    'call, cell value': [3, [C, [3n, h, h, 5n]], cell([b(1)], [1n])],
    // slots 6, 7: unshielded inputs and outputs, TokenType -> u128
    'token unshielded': [6, [T, [1n, h, 0n]], u128(5n)],
    'token shielded': [7, [T, [0n, 0n, h]], u128(5n)],
    'token dust': [6, [T, [2n, 0n, 0n]], nul],
    'token max hash, max u128': [7, [T, [1n, H, 0n]], u128((1n << 128n) - 1n)],
    'token, other alignment': [6, [[b(8), b(32), b(32)], [1n, h, 0n]], u128(5n)],
    'token unshielded both sides': [6, [T, [1n, h, h]], u128(5n)],
    'token shielded both sides': [7, [T, [0n, h, h]], u128(5n)],
    'token dust non-empty': [6, [T, [2n, 1n, 0n]], u128(5n)],
    'token tag 3': [7, [T, [3n, 0n, 0n]], u128(5n)],
    'token long hash': [6, [[b(1), b(33), b(32)], [1n, 1n << 256n, 0n]], u128(5n)],
    'token two atoms': [6, [[b(1), b(32)], [1n, h]], u128(5n)],
    'token, u128 overflow': [6, [T, [1n, h, 0n]], cell([b(17)], [1n << 128n])],
    'token, two-atom value': [7, [T, [1n, h, 0n]], cell([b(8), b(8)], [1n, 1n])],
    'token, empty cell value': [7, [T, [1n, h, 0n]], cell([], [])],
    'token, map value': [6, [T, [1n, h, 0n]], st({ tag: 'map', content: new Map() })],
    // slot 8: claimed unshielded spends, (TokenType, PublicAddress) -> u128
    'spend to contract': [8, [[...T, ...T], [1n, h, 0n, 1n, a, 0n]], u128(5n)],
    'spend to user': [8, [[...T, ...T], [1n, h, 0n, 0n, 0n, u]], u128(5n)],
    'spend, other alignment': [8, [[...T, b(8), b(32), b(32)], [0n, 0n, h, 0n, 0n, u]], nul],
    'spend to user, both sides set': [8, [[...T, ...T], [1n, h, 0n, 0n, a, u]], u128(5n)],
    'spend to contract, both sides set': [8, [[...T, ...T], [1n, h, 0n, 1n, a, u]], u128(5n)],
    'spend, address tag 2': [8, [[...T, ...T], [1n, h, 0n, 2n, 0n, u]], u128(5n)],
    'spend, token both sides set': [8, [[...T, ...T], [1n, h, h, 1n, a, 0n]], u128(5n)],
    'spend, five atoms': [8, [[...T, b(1), b(32)], [1n, h, 0n, 1n, a]], u128(5n)],
    'spend, seven atoms': [8, [[...T, ...T, b(1)], [1n, h, 0n, 1n, a, 0n, 0n]], u128(5n)],
  };
  for (const [name, [slot, key, val]] of Object.entries(effs)) addVector(`synthetic effects: ${name}`, 'synthetic', qc0, put(slot, key, val));
  // Several entries in one query, and one key written under two alignments (one entry after decoding).
  addVector('synthetic effects: all well formed', 'synthetic', qc0,
    Object.values(effs).slice(0, 4).concat(Object.values(effs).slice(9, 14), Object.values(effs).slice(24, 27))
      .flatMap(([slot, key, val]) => put(slot, key, val)));
  addVector('synthetic effects: one key, two alignments, same value', 'synthetic', qc0,
    [...put(6, [T, [1n, h, 0n]], u128(5n)), ...put(6, [[b(8), b(32), b(32)], [1n, h, 0n]], u128(5n))]);
  addVector('synthetic effects: one key, two alignments, other values', 'synthetic', qc0,
    [...put(6, [T, [1n, h, 0n]], u128(5n)), ...put(6, [[b(8), b(32), b(32)], [1n, h, 0n]], u128(6n))]);

  // The kernel's effect-writing operations exactly as Damp emits them
  // (Damp/Lang/Ledger.lean, `claimIn`, `addIn`, `claimContractCall`; their
  // theorems are in Damp/Proofs/Ledger/Effects.lean), run on effects that
  // already hold entries: a query context left by an earlier query, whose
  // effects are as the runtime re-encodes them. This reaches the `addIn`
  // branch that adds to an existing entry (u64 arithmetic, also for the u128
  // amounts of slots 6 to 8), claims repeated, and a call claimed after others.
  const claimIn = (slot, x) => put(slot, [[b(32)], [x]], nul);
  const addIn = (slot, key, w, amt) => [{ swap: { n: 0 } },
    { idx: { cached: true, pushPath: true, path: [{ tag: 'value', value: av([b(1)], [BigInt(slot)]) }] } },
    cell(key[0], key[1]), { dup: { n: 1 } }, { dup: { n: 1 } }, 'member', cell([b(w)], [amt]), { swap: { n: 0 } }, 'neg',
    { branch: { skip: 4 } }, { dup: { n: 2 } }, { dup: { n: 2 } }, { idx: { cached: true, pushPath: false, path: [{ tag: 'stack' }] } },
    'add', { ins: { cached: true, n: 2 } }, { swap: { n: 0 } }];
  const claimCall = (a, e, c) => [{ swap: { n: 0 } },
    { idx: { cached: true, pushPath: true, path: [{ tag: 'value', value: av([b(1)], [3n]) }] } },
    { dup: { n: 0 } }, 'size', cell([b(32), b(32), f], [a, e, c]), { concat: { cached: true, n: 160 } }, nul,
    { ins: { cached: true, n: 2 } }, { swap: { n: 0 } }];
  const after = (qc, ops) => qc.query(ops, costModel).context;
  const M64 = (1n << 64n) - 1n;
  const tok = [T, [1n, h, 0n]];
  const spendKey = [[...T, ...T], [1n, h, 0n, 1n, a, 0n]];
  const kernel = [];   // [name, starting query context, program]
  for (const slot of [0, 1, 2]) {
    const q1 = after(qc0, claimIn(slot, h));
    kernel.push([`claim slot ${slot}, fresh`, qc0, claimIn(slot, h)]);
    kernel.push([`claim slot ${slot}, again`, q1, claimIn(slot, h)]);
    kernel.push([`claim slot ${slot}, another`, q1, claimIn(slot, H)]);
  }
  {
    const q1 = after(qc0, claimCall(a, h, 5n));
    const q2 = after(q1, claimCall(a, h, 6n));
    kernel.push(['call claim, first', qc0, claimCall(a, h, 5n)]);
    kernel.push(['call claim, second', q1, claimCall(a, h, 6n)]);
    kernel.push(['call claim, third, max values', q2, claimCall(H, H, P - 1n)]);
    // An entry whose sequence number collides with the next claim's.
    const qx = after(qc0, put(3, [C, [1n, a, h, 7n]], nul));
    kernel.push(['call claim, sequence number taken', qx, claimCall(a, h, 7n)]);
  }
  for (const [slot, key, w] of [[4, [[b(32)], [h]], 8], [5, [[b(32)], [h]], 8], [6, tok, 16], [7, tok, 16], [8, spendKey, 16]]) {
    kernel.push([`add slot ${slot}, absent`, qc0, addIn(slot, key, w, 5n)]);
    kernel.push([`add slot ${slot}, absent, max`, qc0, addIn(slot, key, w, w === 8 ? M64 : (1n << 128n) - 1n)]);
    const q5 = after(qc0, addIn(slot, key, w, 5n));
    kernel.push([`add slot ${slot}, present`, q5, addIn(slot, key, w, 7n)]);
    kernel.push([`add slot ${slot}, present, sum 2^64-1`, q5, addIn(slot, key, w, M64 - 5n)]);
    kernel.push([`add slot ${slot}, present, sum 2^64`, q5, addIn(slot, key, w, M64 - 4n)]);
    kernel.push([`add slot ${slot}, present, other key`, q5, addIn(slot, slot <= 5 ? [[b(32)], [H]] : slot < 8 ? [T, [0n, 0n, h]] : [[...T, ...T], [1n, h, 0n, 0n, 0n, u]], w, 7n)]);
    kernel.push([`add slot ${slot}, twice in one query`, qc0, [...addIn(slot, key, w, 5n), ...addIn(slot, key, w, 6n)]]);
    if (w === 16) {
      const qBig = after(qc0, addIn(slot, key, w, 1n << 100n));
      kernel.push([`add slot ${slot}, present 2^100, add 1`, qBig, addIn(slot, key, w, 1n)]);
      kernel.push([`add slot ${slot}, present 5, add 2^64`, q5, addIn(slot, key, w, 1n << 64n)]);
      kernel.push([`add slot ${slot}, key with both sides set`, qc0, addIn(slot, slot < 8 ? [T, [1n, h, h]] : [[...T, ...T], [1n, h, 0n, 0n, a, u]], w, 5n)]);
    }
  }
  // All of them in one transaction's effects: every slot written, then each again.
  {
    let q = qc0;
    for (const [, , ops] of kernel.filter(([name]) => / absent$|fresh$|call claim, first/.test(name))) q = after(q, ops);
    kernel.push(['all slots, then a claim and an addition', q, [...claimIn(0, H), ...addIn(6, tok, 16, 9n)]]);
  }
  for (const [name, qc, ops] of kernel) addVector(`synthetic kernel effects: ${name}`, 'synthetic', qc, ops);
  console.error(`${kernel.length} kernel effect vectors`);
}

fs.writeFileSync(path.join(outDir, 'vectors.json'), JSON.stringify({ values, vectors }));
const n = (p) => vectors.filter(p).length;
console.error(`wrote ${vectors.length} vectors (${n((v) => v.vm.ok)} VM runs and ${n((v) => v.query.ok)} queries succeed in the runtime), `
  + `${values.length} distinct state values, to ${path.join(outDir, 'vectors.json')}`);
