#!/usr/bin/env node
// Drive compactc-generated contract modules, dump their proof data, and check it
// against the real ZKIR v3 checker (positive + tampered negative cases).
//
//   node harness/run-compactc-module.mjs            # all scenarios
//   node harness/run-compactc-module.mjs step       # just `step`
//   node harness/run-compactc-module.mjs inc
//   node harness/run-compactc-module.mjs manual     # step proof data built WITHOUT the compactc module
//   QUIET=1 node harness/run-compactc-module.mjs    # omit the proof-data JSON dumps
//
// Fixtures (compactc 0.36.1 output) live in ../fixtures/{step,inc}.

import path from 'node:path';
import { fileURLToPath } from 'node:url';
import * as rt from '@midnight-ntwrk/compact-runtime';
import { checkProofData } from './check.mjs';
import { toJson, proofDataOf } from './json.mjs';

const here = path.dirname(fileURLToPath(import.meta.url));
const fixtures = path.resolve(here, '..', 'fixtures');
const QUIET = !!process.env.QUIET;

let failures = 0;
const expect = (label, res, shouldPass) => {
  const good = res.ok === shouldPass;
  if (!good) failures++;
  const detail = res.ok ? `outputs=${toJson(res.outputs, 0)}` : `${res.stage}: ${res.error}`;
  console.log(`[${good ? 'OK  ' : 'FAIL'}] ${label}: check ${res.ok ? 'PASSED' : 'REJECTED'} (expected ${shouldPass ? 'pass' : 'reject'}) ${detail}`);
};
const clone = (pd) => structuredClone(pd); // Uint8Array/bigint-safe deep copy
const dump = (title, x) => { if (!QUIET) console.log(`--- ${title}\n${toJson(x)}`); };

const COIN_PK = '0'.repeat(64);

async function deploy(mod, witnesses, privateState) {
  const contract = new mod.Contract(witnesses);
  const cctx = rt.createConstructorContext(privateState, COIN_PK);
  const init = await contract.initialState(cctx); // async in 0.21
  return { contract, init };
}

function circuitCtx(circuitId, init, contractState) {
  return rt.createCircuitContext({
    circuitId,
    contractAddress: rt.sampleContractAddress(),
    coinPublicKeyOrZswapState: init.currentZswapLocalState.coinPublicKey,
    contractState: contractState ?? init.currentContractState,
    privateState: init.currentPrivateState,
  });
}

// ---------------------------------------------------------------- step
async function runStep() {
  console.log('\n===== step (fixtures/step, ex.compact) =====');
  const dir = path.join(fixtures, 'step');
  const mod = await import(path.join(dir, 'contract', 'index.js'));
  const witnesses = { hint: ({ privateState }) => [privateState, 7n] };
  const { contract, init } = await deploy(mod, witnesses, {});

  for (const [a, b, n] of [[5n, true, 42n], [5n, false, 42n]]) {
    const ctx = circuitCtx('step', init);
    const res = await contract.impureCircuits.step(ctx, a, b, n);
    const pd = proofDataOf(res.context.callProofDataTrace.at(-1));
    console.log(`step(${a}, ${b}, ${n}) -> result=${res.result}  ledger.total=${mod.ledger(res.context.callContext.currentQueryContext.state).total}`);
    dump(`proofData step(${a},${b},${n})`, pd);
    dump('gasCost', res.gasCost);
    expect(`step(${a},${b},${n}) honest`, await checkProofData({ compiledDir: dir, circuitId: 'step', proofData: pd }), true);
    if (b) {
      const pr = await checkProofData({ compiledDir: dir, circuitId: 'step', proofData: pd, prove: true });
      console.log(`[${pr.ok && pr.proof ? 'OK  ' : 'FAIL'}] step(${a},${b},${n}) real prove with keys/step.prover: ${pr.ok ? `proof ${pr.proof.length} bytes` : `${pr.stage}: ${pr.error}`}`);
      if (!(pr.ok && pr.proof)) failures++;
    }

    if (b) {
      const t1 = clone(pd); // witness output 7 -> 8
      t1.privateTranscriptOutputs[0].value = [new Uint8Array([8])];
      expect('tamper privateTranscriptOutputs[0] (hint 7->8)', await checkProofData({ compiledDir: dir, circuitId: 'step', proofData: t1 }), false);

      const t2 = clone(pd); // value written to ledger cell
      const cell = t2.publicTranscript[1].push.value; // {tag:'cell', content: AlignedValue}
      cell.content.value = rt.CompactTypeField.toValue(res.result + 1n);
      expect('tamper publicTranscript[1].push cell value (r -> r+1)', await checkProofData({ compiledDir: dir, circuitId: 'step', proofData: t2 }), false);

      const t3 = clone(pd); // circuit output
      t3.output.value = rt.CompactTypeField.toValue(res.result + 1n);
      expect('tamper output (r -> r+1)', await checkProofData({ compiledDir: dir, circuitId: 'step', proofData: t3 }), false);

      const t4 = clone(pd); // circuit input
      t4.input.value[0] = rt.CompactTypeField.toValue(a + 1n)[0];
      expect('tamper input a (5 -> 6)', await checkProofData({ compiledDir: dir, circuitId: 'step', proofData: t4 }), false);
    }
  }

  // assert failure path: n >= 1000 makes the JS module throw before any proof data exists
  try {
    await contract.impureCircuits.step(circuitCtx('step', init), 5n, true, 5000n);
    console.log('[FAIL] step(...,5000) unexpectedly succeeded'); failures++;
  } catch (e) {
    console.log(`[OK  ] step(5,true,5000) throws in JS: ${e.constructor.name}: ${e.message}`);
  }
}

// ---------------------------------------------------------------- inc
async function runInc() {
  console.log('\n===== inc (fixtures/inc, t.compact) =====');
  const dir = path.join(fixtures, 'inc');
  const mod = await import(path.join(dir, 'contract', 'index.js'));
  const SECRET = 1234567n;
  const witnesses = { secret: ({ privateState }) => [privateState, privateState.secret] };
  const { contract, init } = await deploy(mod, witnesses, { secret: SECRET });

  // The contract has no constructor that sets `owner` (ledger index 1), so it starts as
  // 32 zero bytes and `inc` would always fail its assert. Patch the ledger state with a
  // hand-written Impact program (same shape compactc uses for a Cell write).
  const ownerBytes = rt.persistentHash(rt.CompactTypeField, SECRET);
  const u8 = new rt.CompactTypeUnsignedInteger(255n, 1);
  const b32 = new rt.CompactTypeBytes(32);
  const setup = circuitCtx('setup', init);
  rt.queryLedgerState(setup, { input: { value: [], alignment: [] }, publicTranscript: [], privateTranscriptOutputs: [] }, [
    { push: { storage: false, value: rt.StateValue.newCell({ value: u8.toValue(1n), alignment: u8.alignment() }).encode() } },
    { push: { storage: true, value: rt.StateValue.newCell({ value: b32.toValue(ownerBytes), alignment: b32.alignment() }).encode() } },
    { ins: { cached: false, n: 1 } },
  ]);
  const patchedState = setup.callContext.currentQueryContext.state; // ChargedState
  console.log(`owner set to persistentHash(${SECRET}) = 0x${Buffer.from(ownerBytes).toString('hex')}`);

  const ctx = circuitCtx('inc', init, patchedState);
  const res = await contract.impureCircuits.inc(ctx, 3n, true);
  const pd = proofDataOf(res.context.callProofDataTrace.at(-1));
  console.log(`inc(3, true) -> counter=${mod.ledger(res.context.callContext.currentQueryContext.state).counter}`);
  dump('proofData inc(3,true)', pd);
  expect('inc(3,true) honest', await checkProofData({ compiledDir: dir, circuitId: 'inc', proofData: pd }), true);

  const t1 = clone(pd); // the popeq read result (owner bytes)
  const popeq = t1.publicTranscript.find((op) => typeof op === 'object' && 'popeq' in op).popeq;
  popeq.result.value[0][0] ^= 1;
  expect('tamper popeq.result (owner byte flipped)', await checkProofData({ compiledDir: dir, circuitId: 'inc', proofData: t1 }), false);

  const t2 = clone(pd); // the counter increment amount
  const addi = t2.publicTranscript.find((op) => typeof op === 'object' && 'addi' in op).addi;
  addi.immediate = 4;
  expect('tamper addi.immediate (3 -> 4)', await checkProofData({ compiledDir: dir, circuitId: 'inc', proofData: t2 }), false);

  const t3 = clone(pd); // witness value
  t3.privateTranscriptOutputs[0].value = rt.CompactTypeField.toValue(SECRET + 1n);
  expect('tamper privateTranscriptOutputs[0] (secret+1)', await checkProofData({ compiledDir: dir, circuitId: 'inc', proofData: t3 }), false);

  const res2 = await contract.impureCircuits.inc(circuitCtx('inc', init, patchedState), 3n, false);
  const pd2 = proofDataOf(res2.context.callProofDataTrace.at(-1));
  expect('inc(3,false) honest (no addi branch)', await checkProofData({ compiledDir: dir, circuitId: 'inc', proofData: pd2 }), true);
}

// ---------------------------------------------------------------- manual
// Build step's proof data WITHOUT the compactc module: only compact-runtime calls,
// i.e. what a generic executor must do. Initial state is also built by hand.
async function runManual() {
  console.log('\n===== manual: step proof data built without contract/index.js =====');
  const dir = path.join(fixtures, 'step');
  const F = rt.CompactTypeField, B = rt.CompactTypeBoolean;
  const U16 = new rt.CompactTypeUnsignedInteger(65535n, 2);
  const U8 = new rt.CompactTypeUnsignedInteger(255n, 1);
  const HINT = new rt.CompactTypeUnsignedInteger(9n, 1);
  const cell = (desc, v) => rt.StateValue.newCell({ value: desc.toValue(v), alignment: desc.alignment() }).encode();
  const writeCell = (idx, desc, v) => [
    { push: { storage: false, value: cell(U8, idx) } },
    { push: { storage: true, value: cell(desc, v) } },
    { ins: { cached: false, n: 1 } },
  ];

  // initial state: ledger = array [null], then constructor transcript writes total := 0
  const state = new rt.ContractState();
  state.data = new rt.ChargedState(rt.StateValue.newArray().arrayPush(rt.StateValue.newNull()));
  state.setOperation('step', new rt.ContractOperation());
  const cctx = rt.createCircuitContext({ circuitId: 'constructor', contractAddress: rt.dummyContractAddress(), coinPublicKeyOrZswapState: COIN_PK, contractState: state.data, privateState: undefined });
  rt.queryLedgerState(cctx, { input: { value: [], alignment: [] }, publicTranscript: [], privateTranscriptOutputs: [] }, writeCell(0n, F, 0n));
  state.data = new rt.ChargedState(cctx.callContext.currentQueryContext.state.state);

  // call step(a=5, b=true, n=42) with hint() = 7
  const [a, b, n, hint] = [5n, true, 42n, 7n];
  const ctx = rt.createCircuitContext({ circuitId: 'step', contractAddress: rt.sampleContractAddress(), coinPublicKeyOrZswapState: COIN_PK, contractState: state, privateState: undefined });
  const ppd = {
    input: { value: [...F.toValue(a), ...B.toValue(b), ...U16.toValue(n)], alignment: [...F.alignment(), ...B.alignment(), ...U16.alignment()] },
    output: undefined, publicTranscript: [], privateTranscriptOutputs: [],
  };
  const h = b ? (ppd.privateTranscriptOutputs.push({ value: HINT.toValue(hint), alignment: HINT.alignment() }), hint) : 0n;
  const r = rt.subField(rt.addField(rt.mulField(a, a), h), rt.transientHash(F, a));
  rt.queryLedgerState(ctx, ppd, writeCell(0n, F, r));
  if (!(n < 1000n)) throw new Error('n too big');
  ppd.output = { value: F.toValue(r), alignment: F.alignment() };
  dump('manual proofData', ppd);
  expect('manual step(5,true,42)', await checkProofData({ compiledDir: dir, circuitId: 'step', proofData: ppd }), true);
}

const which = process.argv[2];
const scenarios = { step: runStep, inc: runInc, manual: runManual };
for (const [name, fn] of Object.entries(scenarios)) {
  if (which && which !== name) continue;
  try { await fn(); } catch (e) { failures++; console.log(`[FAIL] scenario ${name} threw: ${e?.stack ?? e}`); }
}
console.log(`\n${failures === 0 ? 'ALL EXPECTATIONS MET' : `${failures} EXPECTATION(S) FAILED`}`);
process.exit(failures === 0 ? 0 : 1);
