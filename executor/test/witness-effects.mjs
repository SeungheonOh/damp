// What a witness can touch, on the runtime (docs/ledger-model.md, "What a witness can touch";
// Damp/Executor/Witnesses.lean, `WitnessesOK`). test/witness-effects.sh builds the contract.
//
// Every query (`QueryContext.prototype.query`) is logged with the VM stack it starts from and the
// one it leaves: the call context slot by slot, the effects and the contract state. Each circuit
// of `witness_effects` runs a ledger statement, a witness, and a ledger statement; the difference
// between the stack the first query left and the one the second starts from is all the witness
// did to the ledger state (no other code runs in between). The Zswap local state is compared
// before and after each call. Each row of the table in docs/ledger-model.md is checked here:
//
//   createZswapOutput  ledger: call-context slot 1 only (an entry commitment -> the Zswap local
//                      state's currentIndex); Zswap: currentIndex + 1, the output appended
//   createZswapInput   ledger: nothing; Zswap: the input appended
//   ownPublicKey       ledger: nothing; Zswap: nothing; answer: the coin public key, whatever
//                      the ledger state
//   user witness       ledger: nothing (an attempt to assign to the view throws, and the state is
//                      unchanged); sees: the contract state the statements before it left, and the
//                      contract's address; not the effects or the rest of the context
//
// Usage: node test/witness-effects.mjs <dir holding witness_effects/>

import path from 'node:path';
import fs from 'node:fs/promises';
import * as rt from '@midnight-ntwrk/compact-runtime';
import * as ocrt from '@midnightntwrk/onchain-runtime-v4';
import { makeContract } from '../src/executor.mjs';
import { toJson } from '../harness/json.mjs';

const root = path.resolve(process.argv[2]);
const COIN_PK = '3c'.repeat(32);
let failures = 0, checks = 0;
const report = (ok, what, detail = '') => {
  checks++;
  if (!ok) failures++;
  console.log(`${ok ? 'ok  ' : 'FAIL'}  ${what}${detail ? `  ${detail}` : ''}`);
};

// ---------------------------------------------------------------- the query log
function canon(x) {
  if (x instanceof Map) return { $map: [...x.entries()].map(([k, v]) => [canon(k), canon(v)]).sort((a, b) => (toJson(a, 0) < toJson(b, 0) ? -1 : 1)) };
  if (Array.isArray(x)) return x.map(canon);
  if (x instanceof Uint8Array || typeof x !== 'object' || x === null) return x;
  if (x.tag === 'map' && Array.isArray(x.content)) {
    return { tag: 'map', content: x.content.map(canon).sort((a, b) => (toJson(a, 0) < toJson(b, 0) ? -1 : 1)) };
  }
  return Object.fromEntries(Object.keys(x).sort().map((k) => [k, canon(x[k])]));
}
const sv = (v) => toJson(canon(v.encode()), 0);
function snapshot(qc) {
  const st = qc.toVmStack();
  const ctx = st.get(0);
  return { context: ctx.asArray().map(sv), effects: sv(st.get(1)), state: sv(st.get(2)) };
}
let log = [];
const realQuery = ocrt.QueryContext.prototype.query;
ocrt.QueryContext.prototype.query = function (ops, cm, gasLimit) {
  const entry = { before: snapshot(this) };
  const r = realQuery.call(this, ops, cm, gasLimit);
  entry.after = snapshot(r.context);
  log.push(entry);
  return r;
};

/** What changed between the stack one query left and the one the next starts from. */
function diff(a, b) {
  const out = [];
  const n = Math.max(a.context.length, b.context.length);
  for (let i = 0; i < n; i++) if (a.context[i] !== b.context[i]) out.push(`context[${i}]`);
  if (a.effects !== b.effects) out.push('effects');
  if (a.state !== b.state) out.push('state');
  return out;
}

// ---------------------------------------------------------------- the contract
let seen = null;
const witnesses = {
  peek: ({ ledger, privateState, contractAddress }) => {
    seen = { count: ledger.count, address: contractAddress, keys: Object.keys(ledger) };
    return [privateState, ledger.count];
  },
  tamper: ({ ledger, privateState }) => {
    let threw = false;
    try { ledger.count = 99n; } catch { threw = true; }
    seen = { threw, after: ledger.count };
    return [privateState, 0n];
  },
};
const spec = JSON.parse(await fs.readFile(path.join(root, 'witness_effects', 'contract.json'), 'utf-8'));
const contract = makeContract(spec, witnesses);
const init = await contract.initialState(rt.createConstructorContext({}, COIN_PK));
let state = init.currentContractState;
let zswap = init.currentZswapLocalState;
const ADDRESS = rt.dummyContractAddress();

async function run(circuit, args) {
  log = [];
  seen = null;
  const ctx = rt.createCircuitContext({
    circuitId: circuit, contractAddress: ADDRESS, coinPublicKeyOrZswapState: zswap,
    contractState: state, privateState: init.currentPrivateState, time: 0,
  });
  const zBefore = ctx.callContext.currentZswapLocalState;
  const r = await contract.circuits[circuit](ctx, ...args);
  state = r.context.callContext.currentQueryContext.state;
  const zAfter = r.context.callContext.currentZswapLocalState;
  const across = log.length >= 2 ? diff(log[0].after, log[1].before) : null;
  return { r, zBefore, zAfter, across, entries: log, qc: r.context.callContext.currentQueryContext };
}

const bytes = (n, a, b) => { const x = new Uint8Array(n); x[0] = a; x[n - 1] = b; return x; };
const coin = (n) => ({ nonce: bytes(32, n, n + 1), color: bytes(32, 0x52, 0x44), value: 5n });
const pk = { bytes: bytes(32, 0xaa, 0xbb) };
const same = (a, b) => toJson(a, 0) === toJson(b, 0);

// createZswapOutput
{
  const { r, zBefore, zAfter, across, entries } = await run('outC', [coin(1), pk]);
  report(r.result === 0n && entries.length === 2, 'createZswapOutput: the call completes, two queries');
  report(same(across, ['context[1]']), 'createZswapOutput: changes call-context slot 1 and nothing else in the ledger state',
    `changed: ${JSON.stringify(across)}`);
  const idx = r.context.callContext.currentQueryContext.comIndices;
  const vals = [...idx.values()];
  report(idx.size === 1 && BigInt(vals[0]) === BigInt(zBefore.currentIndex),
    'createZswapOutput: the entry it inserts is the Zswap local state\'s current index (its answer depends on no ledger state)',
    `comIndices ${toJson([...idx.entries()], 0)}, currentIndex before ${zBefore.currentIndex}`);
  report(BigInt(zAfter.currentIndex) === BigInt(zBefore.currentIndex) + 1n && zAfter.outputs.length === zBefore.outputs.length + 1 &&
    zAfter.inputs.length === zBefore.inputs.length,
    'createZswapOutput: Zswap local state: currentIndex + 1, the output appended');
  zswap = zAfter;
  // a second output: a second entry, at the next index
  const s2 = await run('outC', [coin(3), pk]);
  const idx2 = s2.r.context.callContext.currentQueryContext.comIndices;
  report(same(s2.across, ['context[1]']) && idx2.size === 1 && BigInt([...idx2.values()][0]) === BigInt(s2.zBefore.currentIndex),
    'createZswapOutput: again, slot 1 only, at the current index', `currentIndex ${s2.zBefore.currentIndex}`);
  zswap = s2.zAfter;
}
// createZswapInput
{
  const q = { ...coin(7), mt_index: 3n };
  const { r, zBefore, zAfter, across } = await run('inC', [q]);
  report(r.result === 0n && same(across, []), 'createZswapInput: changes nothing in the ledger state', `changed: ${JSON.stringify(across)}`);
  report(zAfter.inputs.length === zBefore.inputs.length + 1 && zAfter.outputs.length === zBefore.outputs.length &&
    BigInt(zAfter.currentIndex) === BigInt(zBefore.currentIndex),
    'createZswapInput: Zswap local state: the input appended, nothing else');
  zswap = zAfter;
}
// ownPublicKey
{
  const a = await run('pkC', []);
  report(same(a.across, []), 'ownPublicKey: changes nothing in the ledger state', `changed: ${JSON.stringify(a.across)}`);
  report(same(a.zAfter, a.zBefore), 'ownPublicKey: changes nothing in the Zswap local state');
  report(same(a.r.result, a.zBefore.coinPublicKey), 'ownPublicKey: answers the coin public key of the Zswap local state');
  // from another ledger state (count = 6 after userC below would do; here after a write), the same answer
  await run('userC', [41n]);
  const b = await run('pkC', []);
  report(same(b.r.result, a.r.result), 'ownPublicKey: the same answer from another ledger state');
}
// a user's witness
{
  const { r, across } = await run('userC', [17n]);
  report(same(across, []), 'user witness: changes nothing in the ledger state', `changed: ${JSON.stringify(across)}`);
  report(r.result === 17n && seen?.count === 17n,
    'user witness: sees the contract state the ledger statements before it left (its answer depends on it)', `saw ${seen?.count}`);
  report(seen?.address === ADDRESS, 'user witness: sees the contract\'s address (call-context slot 0)');
  report(same(seen?.keys, ['count']), 'user witness: the ledger view holds the contract state\'s fields, nothing of the effects or the call context',
    `keys ${JSON.stringify(seen?.keys)}`);
  const t = await run('tamperC', []);
  report(seen?.threw === true && seen?.after === 5n, 'user witness: assigning to the ledger view throws; the view is unchanged');
  report(same(t.across, []) && t.r.result === 5n, 'user witness: the ledger state after it is the one before it', `result ${t.r.result}`);
}

console.log(failures === 0 ? `witness-effects: ${checks} checks passed` : `witness-effects: ${failures} of ${checks} checks FAILED`);
process.exit(failures === 0 ? 0 : 1);
