// Byte strings longer than 31 bytes through the ledger (docs/ledger-model.md,
// "Byte strings over 31 bytes").
//
// A `Bytes n` with n > 31 is several field elements ("limbs") in a circuit and
// one atom of n bytes in a ledger cell. The executor joins the limbs into bytes
// when it writes (`alignedOfFields`) and splits them when it reads
// (`fieldsOfAligned`). This test writes values with every bit set through the
// real runtime and reads them back:
//
//   1. `bytes.store(w)` with w 64 bytes of 0xff: `wide : Cell (Bytes 64)`
//      written, then read back (three limbs, the first 16 bits wide); the
//      result must be w, equal to compactc's, and the ZKIR emitted by Damp must
//      accept the proof data.
//   2. `vault`'s constructor with owner 32 bytes of 0xff: the initial ledger
//      state must equal compactc's, and the owner read back must be the bytes.
//   3. `bytes.claim(admin, ...)` after the constructor-free start: owner (a
//      `Cell (Bytes 32)`) is written with a hash and read back through `popeq`.
//
// Usage: node test/bytes-limbs.mjs <oracle build dir>   (default ../build/oracle)

import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import * as rt from '@midnight-ntwrk/compact-runtime';
import { makeContract, ledgerView } from '../src/executor.mjs';
import { checkProofData } from '../harness/check.mjs';
import { toJson, proofDataOf } from '../harness/json.mjs';
import { witnesses, constructorArgs } from './calls.mjs';

const here = path.dirname(fileURLToPath(import.meta.url));
const root = path.resolve(process.argv[2] ?? path.join(here, '..', '..', 'build', 'oracle'));
const COIN_PK = '3c'.repeat(32);

let failures = 0;
const report = (ok, label, detail = '') => {
  if (!ok) failures++;
  console.log(`${ok ? 'ok   ' : 'FAIL '} ${label}${detail ? '  ' + detail : ''}`);
};
const hex = (b) => Buffer.from(b).toString('hex');
const ones = (n) => new Uint8Array(n).fill(0xff);

async function load(name) {
  const leanDir = path.join(root, 'lean', name);
  const spec = JSON.parse(await fs.readFile(path.join(leanDir, 'contract.json'), 'utf-8'));
  const mod = await import(path.join(root, 'compact', name, 'contract', 'index.js'));
  return { leanDir, spec, mod, mine: makeContract(spec, witnesses), theirs: new mod.Contract(witnesses) };
}

const cctx = () => rt.createConstructorContext({}, COIN_PK);
const callCtx = (circuitId, init, state) =>
  rt.createCircuitContext({
    circuitId,
    contractAddress: rt.dummyContractAddress(),
    coinPublicKeyOrZswapState: init.currentZswapLocalState.coinPublicKey,
    contractState: state ?? init.currentContractState,
    privateState: init.currentPrivateState,
    time: 0,
  });
const encState = (s) => toJson(s.data.state.encode(), 0);

// 1. Bytes 64, all bits set, written and read back.
{
  const c = await load('bytes');
  const mi = await c.mine.initialState(cctx());
  const ti = await c.theirs.initialState(cctx());
  const w = ones(64);
  const mine = await c.mine.circuits.store(callCtx('store', mi), w, 12345n);
  const theirs = await c.theirs.circuits.store(callCtx('store', ti), w, 12345n);
  report(hex(mine.result) === hex(w), 'bytes.store(0xff*64): the value read back is the value written', hex(mine.result));
  report(toJson(mine.result, 0) === toJson(theirs.result, 0), 'bytes.store(0xff*64): result equals compactc\'s');
  const md = proofDataOf(mine.context.callProofDataTrace.at(-1));
  const td = proofDataOf(theirs.context.callProofDataTrace.at(-1));
  report(toJson(md, 0) === toJson(td, 0), 'bytes.store(0xff*64): proof data equals compactc\'s');
  const checked = await checkProofData({ compiledDir: c.leanDir, circuitId: 'store', proofData: md });
  report(checked.ok, 'bytes.store(0xff*64): Damp\'s ZKIR accepts the proof data', checked.ok ? '' : `${checked.stage}: ${checked.error}`);
  const after = mine.context.callContext.currentQueryContext.state;
  report(hex(ledgerView(c.spec, after).wide) === hex(w), 'bytes.store(0xff*64): the ledger cell holds the 64 bytes');

  // 3. A Cell (Bytes 32) written with a hash and read back through popeq.
  const admin = new Uint8Array(32); admin.set(new TextEncoder().encode('admin'));
  const t = new Uint8Array(8).fill(0xff);
  const m3 = await c.mine.circuits.claim(callCtx('claim', mi), admin, t, true);
  const t3 = await c.theirs.circuits.claim(callCtx('claim', ti), admin, t, true);
  const owner = ledgerView(c.spec, m3.context.callContext.currentQueryContext.state).owner;
  report(hex(m3.result) === hex(owner), 'bytes.claim: the Bytes 32 read back equals the cell', hex(owner));
  report(toJson(m3.result, 0) === toJson(t3.result, 0), 'bytes.claim: result equals compactc\'s');
  const d3 = proofDataOf(m3.context.callProofDataTrace.at(-1));
  const c3 = await checkProofData({ compiledDir: c.leanDir, circuitId: 'claim', proofData: d3 });
  report(c3.ok, 'bytes.claim: Damp\'s ZKIR accepts the proof data', c3.ok ? '' : `${c3.stage}: ${c3.error}`);
}

// 2. Bytes 32, all bits set, written by the constructor.
{
  const c = await load('vault');
  const o = ones(32);
  const limit = constructorArgs.vault[1];
  const mi = await c.mine.initialState(cctx(), o, limit);
  const ti = await c.theirs.initialState(cctx(), o, limit);
  report(encState(mi.currentContractState) === encState(ti.currentContractState),
    'vault constructor(0xff*32): initial ledger state equals compactc\'s');
  report(hex(ledgerView(c.spec, mi.currentContractState.data).owner) === hex(o),
    'vault constructor(0xff*32): owner reads back as the 32 bytes');
}

console.log(failures ? `${failures} FAILED` : 'all ok');
process.exit(failures ? 1 : 0);
