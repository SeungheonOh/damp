// Audit (docs/audit.md, F2): at --O3 a `Uint<0..256>` witness value is no longer range checked when
// it is hashed only by an unused binding. Runs test/audit/HashRange.lean's contract honestly (w = 200)
// at --O2 and --O3, then replaces w by 1000 in the private transcript and in the public transcript's
// encoding, and asks Midnight's real ZKIR checker. The --O2 circuit must refuse; so must --O3 for the
// optimizer to be sound. Failed at ccd590e; F2 is fixed, so this is now a regression that must pass.
// Usage: node test/audit-o3-range.mjs <dir holding o2/ and o3/>
import fs from 'node:fs/promises';
import path from 'node:path';
import * as rt from '@midnight-ntwrk/compact-runtime';
import { check, jsonIrToBinary } from '@midnightntwrk/zkir-v3';
import { makeContract } from '../src/executor.mjs';
import { parsePreimage, serializePreimage } from './preimage.mjs';

const root = path.resolve(process.argv[2]);
let failures = 0;
for (const level of ['o2', 'o3']) {
  const dir = path.join(root, level, 'audit_hash');
  const spec = JSON.parse(await fs.readFile(path.join(dir, 'contract.json'), 'utf-8'));
  const contract = makeContract(spec, { w: ({ privateState }) => [privateState, 200n] });
  const init = await contract.initialState(rt.createConstructorContext({}, '3c'.repeat(32)));
  const r = await contract.circuits.f(rt.createCircuitContext({
    circuitId: 'f', contractAddress: rt.dummyContractAddress(), coinPublicKeyOrZswapState: init.currentZswapLocalState.coinPublicKey,
    contractState: init.currentContractState, privateState: init.currentPrivateState, time: 0 }));
  const pd = r.proofData ?? r.context.callProofDataTrace.at(-1);
  const pre = parsePreimage(rt.proofDataIntoSerializedPreimage(pd.input, pd.output, pd.publicTranscript, pd.privateTranscriptOutputs, 'f'));
  const ir = jsonIrToBinary(await fs.readFile(path.join(dir, 'zkir', 'f.zkir'), 'utf-8'));
  const provider = { async lookupKey() { return { proverKey: new Uint8Array(0), verifierKey: new Uint8Array(0), ir }; }, async getParams() { throw new Error('no'); } };
  const verdict = async (p) => { try { await check(Uint8Array.from(serializePreimage(p)), provider); return 'accept'; } catch (e) { return 'reject: ' + String(e.message ?? e).slice(0, 80); } };
  const honest = await verdict(pre);
  const forged = structuredClone(pre);
  forged.privateTranscript = forged.privateTranscript.map((x) => (x === 200n ? 1000n : x));
  forged.publicTranscriptInputs = forged.publicTranscriptInputs.map((x) => (x === 200n ? 1000n : x));
  const bad = await verdict(forged);
  const ok = honest === 'accept' && bad !== 'accept';
  if (!ok) failures++;
  console.log(`${ok ? 'ok  ' : 'FAIL'} ${level}: honest w=200 ${honest}; forged w=1000 (not a Uint<0..256>) ${bad}`);
}
console.log(failures ? `audit-o3-range: ${failures} FAILED (expected: finding F2)` : 'audit-o3-range: passed');
process.exit(failures ? 1 : 0);
