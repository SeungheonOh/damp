// The shipped ZKIR rejects what the source rejects, at every level, under Midnight's own checker.
//
// Reads what test/PruneSound.lean writes (cases.json, the ZKIR of each case at --no-opt, default,
// --O2 and --O3, and a control emitted with the old pruning, which dropped every unused binding):
//   1. honest proof data: the shipped ZKIR accepts it at every level;
//   2. forged proof data (a = 1000, which makes an unused comparison or hash fail): the shipped ZKIR
//      refuses it at every level, in its body (not at the commitment, which the checker tests after
//      the body ran), and Damp's evaluator agrees;
//   3. the same forged data on the control: the real checker accepts exactly where Damp's evaluator
//      says the control does, which shows the forged data is otherwise valid and the test would
//      catch the old behaviour.
// Then the two contracts of Examples/PruneSound.lean, through the JS executor (executor.mjs) and the
// checker at every level: with the bad witness value the executor refuses the call; on the honest
// call's proof data with that value substituted, the checker refuses too; the honest call passes both.
// Usage: node test/prune-sound.mjs <dir written by test/PruneSound.lean>
import fs from 'node:fs/promises';
import path from 'node:path';
import * as rt from '@midnight-ntwrk/compact-runtime';
import { check, jsonIrToBinary } from '@midnightntwrk/zkir-v3';
import { makeContract } from '../src/executor.mjs';
import { parsePreimage, serializePreimage } from './preimage.mjs';

const root = path.resolve(process.argv[2]);
const P = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001n;
const fr = (x) => ((BigInt(x) % P) + P) % P;
let failures = 0;
const report = (ok, msg) => { if (!ok) failures++; console.log(`${ok ? 'ok  ' : 'FAIL'} ${msg}`); };

const verdict = async (zkirPath, pre) => {
  const ir = jsonIrToBinary(await fs.readFile(path.resolve(root, zkirPath), 'utf-8'));
  const provider = { async lookupKey() { return { proverKey: new Uint8Array(0), verifierKey: new Uint8Array(0), ir }; }, async getParams() { throw new Error('no'); } };
  try { await check(Uint8Array.from(serializePreimage(pre)), provider); return { ok: true, why: 'accept' }; } catch (e) {
    const m = String(e?.message ?? e);
    return { ok: false, why: m.slice(0, 90), commitment: /ommitment/.test(m) };
  }
};
const fieldAV = (xs) => ({ value: xs.map((x) => rt.bigIntToValue(fr(x))[0] ?? new Uint8Array(0)), alignment: xs.map(() => ({ tag: 'atom', value: { tag: 'field' } })) });
/** A preimage with the runtime's commitment over inputs and outputs, the given private transcript and
    active public inputs (computed by Damp's evaluator; no ledger reads). */
const preimage = (name, inputs, outputs, priv, ptIn) => {
  const pre = parsePreimage(rt.proofDataIntoSerializedPreimage(fieldAV(inputs), fieldAV(outputs), [], [], name));
  pre.privateTranscript = priv.map(fr);
  pre.publicTranscriptInputs = ptIn.map(fr);
  return pre;
};

// ---- 1-3: the IR cases
const cases = JSON.parse(await fs.readFile(path.join(root, 'cases.json'), 'utf-8'));
for (const c of cases) {
  const tag = `${c.case} ${c.level}`;
  if (c.honest && c.honest.outputs) {
    const v = await verdict(c.zkir, preimage(c.case, c.honest.inputs, c.honest.outputs, c.honest.priv, c.honest.ptIn));
    report(v.ok, `${tag}: honest ${JSON.stringify(c.honest.inputs)}/${JSON.stringify(c.honest.priv)} ${v.why}`);
  }
  const forged = preimage(c.case, c.forged.inputs, c.forged.outputs, c.forged.priv, c.forged.ptIn);
  const v = await verdict(c.zkir, forged);
  report(!v.ok && !v.commitment && !c.leanAccepts,
    `${tag}: forged ${JSON.stringify(c.forged.inputs)}/${JSON.stringify(c.forged.priv)} shipped: ${v.why}`);
  const w = await verdict(c.control, forged);
  report(w.ok === c.controlAccepts, `${tag}: same data on the old pruning: ${w.why} (Damp's evaluator: ${c.controlAccepts ? 'accept' : 'reject'})`);
}

// ---- 4: the contracts, through the executor
const run = async (dir, circuit, value) => {
  const spec = JSON.parse(await fs.readFile(path.join(dir, 'contract.json'), 'utf-8'));
  const contract = makeContract(spec, { w: ({ privateState }) => [privateState, value] });
  const init = await contract.initialState(rt.createConstructorContext({}, '3c'.repeat(32)));
  try {
    const r = await contract.circuits[circuit](rt.createCircuitContext({
      circuitId: circuit, contractAddress: rt.dummyContractAddress(), coinPublicKeyOrZswapState: init.currentZswapLocalState.coinPublicKey,
      contractState: init.currentContractState, privateState: init.currentPrivateState, time: 0 }));
    const pd = r.proofData ?? r.context.callProofDataTrace.at(-1);
    return { ok: true, pre: parsePreimage(rt.proofDataIntoSerializedPreimage(pd.input, pd.output, pd.publicTranscript, pd.privateTranscriptOutputs, circuit)) };
  } catch (e) { return { ok: false, why: String(e?.message ?? e).slice(0, 80) }; }
};
for (const [name, good] of [['prune_sound', 7n], ['prune_hash', 200n]]) {
  for (const level of ['noopt', 'default', 'o2', 'o3']) {
    const dir = path.join(root, 'contracts', level, name);
    const zkir = path.join(dir, 'zkir', 'f.zkir');
    const honest = await run(dir, 'f', good);
    if (!honest.ok) { report(false, `${name} ${level}: honest call refused by the executor: ${honest.why}`); continue; }
    const hv = await verdict(zkir, honest.pre);
    report(hv.ok, `${name} ${level}: executor completes w=${good}, checker ${hv.why}`);
    const bad = await run(dir, 'f', 1000n);
    report(!bad.ok, `${name} ${level}: executor on w=1000: ${bad.ok ? 'completes' : 'refuses (' + bad.why + ')'}`);
    const forged = structuredClone(honest.pre);
    forged.privateTranscript = forged.privateTranscript.map((x) => (x === good ? 1000n : x));
    forged.publicTranscriptInputs = forged.publicTranscriptInputs.map((x) => (x === good ? 1000n : x));
    const fv = await verdict(zkir, forged);
    report(!fv.ok && !fv.commitment, `${name} ${level}: checker on the honest data with w=1000: ${fv.why}`);
  }
}
console.log(failures ? `prune-sound: ${failures} FAILED` : 'prune-sound: passed');
process.exit(failures ? 1 : 0);
