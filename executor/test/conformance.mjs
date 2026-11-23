// Conformance of the executor to its definition (Damp/Executor/Spec.lean): the JS
// half of test/executor.sh.
//
// Runs, with the executor's trace hook on,
//   * every call of the shared call table (calls.mjs, the table test/run.mjs
//     uses) and of `extraCalls` below, on every example contract, chained as
//     test/run.mjs chains them, constructors included;
//   * every synthetic call of <dir>/synthetic.json (written by
//     `damp-executor-test export`), with the witness answers it scripts;
// on the contract.json files under <dir>/contracts (also written by the Lean
// side, from the same IR it replays), and writes <dir>/traces.json: for each
// call the trace record and, when the call completed, the field elements of
// its proof preimage as the runtime itself serializes it (parsed by
// preimage.mjs, independently of Damp's encoder) and the runtime's field
// encoding of the result. `damp-executor-test check <dir>` compares.
//
// Usage: node test/conformance.mjs <dir>

import fs from 'node:fs';
import path from 'node:path';
import * as rt from '@midnight-ntwrk/compact-runtime';
import { makeContract, contractModule } from '../src/executor.mjs';
import { parsePreimage } from './preimage.mjs';
import { witnesses, constructorArgs, calls, startState, addresses, strangers } from './calls.mjs';
import { World, expectedVkOf } from './world.mjs';

const dir = path.resolve(process.argv[2] ?? 'build/executor');
const COIN_PK = '3c'.repeat(32);   // the user's coin public key (what ownPublicKey returns)
const EMPTY = { value: [], alignment: [] };

// Calls on contracts the shared table does not exercise (as in semantics-vectors.mjs).
const extraCalls = [
  ['tuned', 'settle', [[1n, 2n, 3n, 4n], true]],
  ['tuned', 'settle', [[100n, 2000n, 30n, 4n], false]],
  ['tuned', 'settle', [[65535n, 65535n, 65535n, 65535n], true]],
];

// ---------------------------------------------------------------- the runtime's field view

/** The runtime's field encoding of an AlignedValue: serialize it as a preimage's input. */
const fieldsOf = (av) => parsePreimage(rt.proofDataIntoSerializedPreimage(av, EMPTY, [], [], 'x')).inputs;

const preimageOf = (pd, key) => {
  const p = parsePreimage(rt.proofDataIntoSerializedPreimage(pd.input, pd.output ?? EMPTY, pd.publicTranscript, pd.privateTranscriptOutputs, key));
  return { inputs: p.inputs, privateTranscript: p.privateTranscript, publicTranscriptInputs: p.publicTranscriptInputs, publicTranscriptOutputs: p.publicTranscriptOutputs };
};

const dec = (_k, v) => (typeof v === 'bigint' ? v.toString() : v);
const plain = (x) => JSON.parse(JSON.stringify(x, dec));

// ---------------------------------------------------------------- Merkle roots, through the runtime

const bitLen = (n) => (n === 0n ? 0 : n.toString(2).length);
const descriptor = (ty) => {
  switch (ty.kind) {
    case 'field': return rt.CompactTypeField;
    case 'bool': return rt.CompactTypeBoolean;
    case 'uint': { const max = BigInt(ty.max); return new rt.CompactTypeUnsignedInteger(max, Math.ceil(bitLen(max) / 8)); }
    case 'bytes': return new rt.CompactTypeBytes(ty.length);
    default: throw new Error(`no key descriptor for ${ty.kind}`);
  }
};
const digestOf = (sv) => {
  const v = sv.asArray()[0].asBoundedMerkleTree().rehash().root()?.value;
  return v ? rt.CompactTypeMerkleTreeDigest.fromValue([...v]) : undefined;
};

// ---------------------------------------------------------------- running

const results = [];
let pending = [];   // { rec, contract }: one per circuit run, callees' before their caller's
const traceOf = (contract) => (rec) => pending.push({ rec, contract });
const take = () => { const r = pending; pending = []; return r; };

// Cross-contract calls (docs/calls.md): the contracts of `addresses` are
// deployed in a simulated chain (world.mjs), every one the Damp build, so a
// call runs its callees through the executor too, each traced as a call of its
// own (labelled `… > callee.circuit`) and replayed through the definition as
// such. The verifier keys are stand-ins (the bytes of `contract.circuit`): the
// runtime's guard only compares their fingerprints with `expectedVk`.
const inWorld = (name) => Object.hasOwn(addresses, name);
const world = new World({ standInKeys: true });

function record(label, contract, circuit, rec) {
  const entry = { label, contract, circuit, record: plain({ ...rec, proofData: undefined }), preimage: null, outputFields: null };
  if (!rec.failure) {
    entry.preimage = plain(preimageOf(rec.proofData, circuit));
    entry.outputFields = plain(rec.proofData.output ? fieldsOf(rec.proofData.output) : []);
  }
  results.push(entry);
}

async function load(name, wits, ctorArgs) {
  const spec = JSON.parse(fs.readFileSync(path.join(dir, 'contracts', name, 'contract.json'), 'utf-8'));
  const contract = makeContract(spec, wits, { trace: traceOf(name) });
  const c = { spec, contract, init: null, state: undefined };
  const stateValue = () => {
    const s = c.state ?? c.init.currentContractState.data;
    return s instanceof rt.StateValue ? s : s.state;
  };
  const field = (n) => spec.ledger.find((f) => f.name === n);
  c.rootOf = (n) => digestOf(stateValue().asArray()[field(n).index]);
  c.rootIn = (n, k) => {
    const f = field(n);
    const d = descriptor(f.type.key);
    return digestOf(stateValue().asArray()[f.index].asMap().get({ value: d.toValue(k), alignment: d.alignment() }));
  };
  try {
    c.init = await contract.initialState(rt.createConstructorContext({}, COIN_PK), ...ctorArgs);
  } finally {
    for (const { rec } of take()) record(`${name}.constructor`, name, 'constructor', rec);
  }
  if (inWorld(name)) {
    const keys = Object.fromEntries(spec.circuits.filter((k) => k.proof).map((k) => [k.name, new TextEncoder().encode(`${name}.${k.name}`)]));
    const mod = contractModule(spec, expectedVkOf(keys), { trace: traceOf(name) });
    world.deploy(addresses[name], name, c.init.currentContractState.data, keys, mod);
    for (const s of Object.values(strangers)) {
      if (s.like !== name) continue;
      world.deploy(s.address, name, c.init.currentContractState.data, s.keys ? s.keys(keys) : keys, s.bound ? (s.wrap ? s.wrap(mod) : mod) : undefined);
    }
  }
  return c;
}

async function call(c, name, circuit, args, label) {
  const ctx = inWorld(name)
    ? world.context(addresses[name], circuit, c.init.currentPrivateState, c.init.currentZswapLocalState.coinPublicKey)
    : rt.createCircuitContext({
      circuitId: circuit, contractAddress: rt.dummyContractAddress(),
      coinPublicKeyOrZswapState: c.init.currentZswapLocalState.coinPublicKey,
      contractState: startState(name, c.state ?? c.init.currentContractState), privateState: c.init.currentPrivateState, time: 0,
    });
  let ok = false;
  try {
    const run = await c.contract.circuits[circuit](ctx, ...args);
    c.state = run.context.callContext.currentQueryContext.state;
    if (inWorld(name)) world.commit(run);
    ok = true;
  } catch { /* recorded by the trace */ }
  const recs = take();
  // The call's own record comes last; any before it are its callees' runs.
  if (recs.length < 1 || recs.at(-1).contract !== name || (!inWorld(name) && recs.length !== 1)) {
    throw new Error(`${label}: ${recs.length} trace records`);
  }
  recs.forEach(({ rec, contract }, i) => {
    const last = i === recs.length - 1;
    record(last ? label : `${label} > ${contract}.${rec.circuit} (run ${i + 1} of ${recs.length})`, contract, rec.circuit, rec);
  });
  return ok;
}

const show = (x) => JSON.stringify(x, (_k, v) => (typeof v === 'bigint' ? `${v}` : v instanceof Uint8Array ? `0x${Buffer.from(v).toString('hex')}` : v)).replaceAll('"', '');

// The example contracts. Those in the chain are deployed first, callees before callers.
const loaded = new Map();
let ran = 0, completed = 0;
if (calls.some(([name]) => inWorld(name))) {
  for (const name of Object.keys(addresses)) loaded.set(name, await load(name, witnesses, constructorArgs[name] ?? []));
}
for (const [name, circuit, argsOf] of [...calls, ...extraCalls]) {
  if (!loaded.has(name)) loaded.set(name, await load(name, witnesses, constructorArgs[name] ?? []));
  const c = loaded.get(name);
  let args;
  try {
    // In the chain, an argument list may depend on the implementation: here always Damp's.
    args = typeof argsOf === 'function' ? argsOf(inWorld(name) ? 'damp' : c) : argsOf;
  } catch (e) {
    // The arguments depend on the state earlier calls left (a Merkle root).
    results.push({ label: `${name}.${circuit}(...)`, contract: name, circuit, driverError: `cannot form the arguments: ${e.message}` });
    continue;
  }
  ran++;
  if (await call(c, name, circuit, args, `${name}.${circuit}(${args.map(show).join(', ')})`)) completed++;
}

// The synthetic contract.
const synthetic = JSON.parse(fs.readFileSync(path.join(dir, 'synthetic.json'), 'utf-8'));
let script = [];
// A case with `peek` answers every witness with the ledger cell it names, as the witness context
// shows it (the ledger as the ledger statements before the witness left it), as a user's witness
// reading the ledger does; the others answer from their script.
let peek = null;
const synWitnesses = new Proxy({}, {
  get: () => ({ privateState, ledger }) => {
    if (peek !== null) return [privateState, [BigInt(ledger[peek])]];
    if (script.length === 0) throw new Error('no scripted answer left');
    const a = script.shift();
    if (a === null) throw new Error('scripted refusal');
    return [privateState, a.map(BigInt)];
  },
});
// The synthetic contract as written, and its `levels` circuits as each optimization level ships them.
const synContracts = new Map();
for (const s of synthetic) {
  if (!synContracts.has(s.contract)) synContracts.set(s.contract, await load(s.contract, synWitnesses, []));
  script = s.witness.map((a) => (a === null ? null : [...a]));
  peek = s.peek ?? null;
  ran++;
  if (await call(synContracts.get(s.contract), s.contract, s.circuit, s.args.map(BigInt), s.label)) completed++;
}

fs.writeFileSync(path.join(dir, 'traces.json'), JSON.stringify({ calls: results }, null, 1));
console.log(`${results.length} trace records (${ran} calls, ${completed} completed; ${results.length - ran} constructor and nested callee runs) written to ${path.join(dir, 'traces.json')}`);
