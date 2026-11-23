// Audit finding F3: `--O3` folds hashes of constants with Damp's Lean implementations of Midnight's
// hash functions (`Damp.Crypto.prims`); this exercises a folded constant end to end. For the contract
// of test/O3Fold.lean built at --O2 and --O3: `store(42, pad(32, "damp"))` writes the persistent and
// transient hashes the circuit computes at run time; `check()` requires that the same hashes of
// literals (constants at --O3: its ZKIR has no hash instruction left) equal them, and returns them.
// Both calls must succeed through Damp's executor and the real runtime, `check`'s result must equal
// the runtime's own `persistentHash` / `transientHash` of the same values, every call's proof data
// must be accepted by Midnight's ZKIR checker, and a preimage with a changed ledger read refused.
//
// Usage: node test/o3-fold.mjs <dir holding o2/ and o3/>
import fs from 'node:fs/promises';
import path from 'node:path';
import * as rt from '@midnight-ntwrk/compact-runtime';
import { check, jsonIrToBinary } from '@midnightntwrk/zkir-v3';
import { makeContract } from '../src/executor.mjs';
import { parsePreimage, serializePreimage } from './preimage.mjs';

const root = path.resolve(process.argv[2]);
let failures = 0;
const report = (ok, label, detail = '') => { if (!ok) failures++; console.log(`${ok ? 'ok  ' : 'FAIL'} ${label}${detail ? '  ' + detail : ''}`); };
const hex = (b) => Buffer.from(b).toString('hex');
const flat = (x) => (Array.isArray(x) ? x.flatMap(flat) : [x]);   // (a, b, c) comes back as [a, [b, c]]
const show = (x) => JSON.stringify(x, (_k, v) => (typeof v === 'bigint' ? `${v}` : v instanceof Uint8Array ? hex(v) : v));

const pad = new Uint8Array(32); pad.set(new TextEncoder().encode('damp'));
const F = rt.CompactTypeField;
const expected = [
  rt.persistentHash(new rt.CompactTypeVector(2, F), [42n, 7n]),
  rt.transientHash(new rt.CompactTypeVector(2, F), [42n, 7n]),
  rt.persistentHash(new rt.CompactTypeBytes(32), pad),
];

const HASH_OPS = ['persistent_hash', 'transient_hash'];
for (const level of ['o2', 'o3']) {
  const dir = path.join(root, level, 'o3_fold');
  const spec = JSON.parse(await fs.readFile(path.join(dir, 'contract.json'), 'utf-8'));
  const zkirOf = async (c) => fs.readFile(path.join(dir, 'zkir', `${c}.zkir`), 'utf-8');
  const ops = JSON.parse(await zkirOf('check')).instructions.map((i) => i.op);
  const hashes = ops.filter((o) => HASH_OPS.includes(o)).length;
  report(level === 'o3' ? hashes === 0 : hashes === 3, `${level}: check.zkir has ${hashes} hash instruction(s)`,
    level === 'o3' ? '(all folded into constants)' : '(computed in the circuit)');

  const contract = makeContract(spec, {});
  const init = await contract.initialState(rt.createConstructorContext({}, '3c'.repeat(32)));
  let state = init.currentContractState;
  const run = async (circuit, ...args) => {
    const r = await contract.circuits[circuit](rt.createCircuitContext({
      circuitId: circuit, contractAddress: rt.dummyContractAddress(), coinPublicKeyOrZswapState: init.currentZswapLocalState.coinPublicKey,
      contractState: state, privateState: init.currentPrivateState, time: 0 }), ...args);
    state = r.context.callContext.currentQueryContext.state;
    const pd = r.proofData ?? r.context.callProofDataTrace.at(-1);
    return { result: r.result, pre: parsePreimage(rt.proofDataIntoSerializedPreimage(pd.input, pd.output, pd.publicTranscript, pd.privateTranscriptOutputs, circuit)) };
  };
  const verdict = async (circuit, pre) => {
    const ir = jsonIrToBinary(await zkirOf(circuit));
    const provider = { async lookupKey() { return { proverKey: new Uint8Array(0), verifierKey: new Uint8Array(0), ir }; }, async getParams() { throw new Error('no'); } };
    try { await check(Uint8Array.from(serializePreimage(pre)), provider); return 'accept'; } catch (e) { return 'reject: ' + String(e.message ?? e).slice(0, 80); }
  };
  let s, c;
  try { s = await run('store', 42n, pad); } catch (e) { report(false, `${level}: store(42, "damp") runs`, String(e.message ?? e)); continue; }
  report((await verdict('store', s.pre)) === 'accept', `${level}: the checker accepts store's proof data`);
  try { c = await run('check'); } catch (e) { report(false, `${level}: check() runs`, String(e.message ?? e)); continue; }
  report(true, `${level}: check() runs (the hashes of literals equal the run-time hashes in the ledger)`);
  report(show(flat(c.result)) === show(expected), `${level}: check() returns the runtime's own hashes`, show(c.result));
  report((await verdict('check', c.pre)) === 'accept', `${level}: the checker accepts check's proof data`);
  const forged = structuredClone(c.pre);
  const i = forged.publicTranscriptOutputs.findIndex((x) => x !== 0n && x !== 1n);
  forged.publicTranscriptOutputs[i] += 1n;
  const v = await verdict('check', forged);
  report(i >= 0 && v !== 'accept', `${level}: the checker refuses check's proof data with a ledger read changed`, v);
}
console.log(failures ? `o3-fold: ${failures} FAILED` : 'o3-fold: passed');
process.exit(failures ? 1 : 0);
