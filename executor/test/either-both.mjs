// An `Either` with both sides non-zero reaching `claimUnshieldedCoinSpend`
// (docs/ledger-model.md). `tokens.mintUTo(amount, to)` passes its
// `Either<ContractAddress, UserAddress>` argument to the kernel unchanged; the
// argument is range-checked limb by limb only, so both sides may be set. The
// runtime's typed decoding of the effects (slot 8, unshielded spends) rejects
// the key; the executor, which runs the runtime, must therefore fail the call,
// as compactc's generated code does. The VM model (Damp/Ledger/Query.lean,
// `effectKey`) rejects it too: test/vm.sh runs the same calls and synthetic
// effect writes against the model, and `decodeEffects_spend_both_sides`
// (Damp/Proofs/Ledger/Kernel.lean) proves the rejection.
//
// Usage: node test/either-both.mjs <oracle build dir>   (default ../build/oracle)

import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import * as rt from '@midnight-ntwrk/compact-runtime';
import { makeContract } from '../src/executor.mjs';
import { witnesses, startState } from './calls.mjs';

const here = path.dirname(fileURLToPath(import.meta.url));
const root = path.resolve(process.argv[2] ?? path.join(here, '..', '..', 'build', 'oracle'));
const COIN_PK = '3c'.repeat(32);

let failures = 0;
const report = (ok, label, detail = '') => {
  if (!ok) failures++;
  console.log(`${ok ? 'ok   ' : 'FAIL '} ${label}${detail ? '  ' + detail : ''}`);
};
const attempt = async (f) => {
  try { return { value: await f() }; } catch (e) { return { error: e instanceof Error ? e.message : String(e) }; }
};

const leanDir = path.join(root, 'lean', 'tokens');
const spec = JSON.parse(await fs.readFile(path.join(leanDir, 'contract.json'), 'utf-8'));
const mod = await import(path.join(root, 'compact', 'tokens', 'contract', 'index.js'));
const mine = makeContract(spec, witnesses);
const theirs = new mod.Contract(witnesses);
const cctx = () => rt.createConstructorContext({}, COIN_PK);
const mi = await mine.initialState(cctx());
const ti = await theirs.initialState(cctx());
const ctx = (init) => rt.createCircuitContext({
  circuitId: 'mintUTo',
  contractAddress: rt.dummyContractAddress(),
  coinPublicKeyOrZswapState: init.currentZswapLocalState.coinPublicKey,
  contractState: startState('tokens', init.currentContractState),
  privateState: init.currentPrivateState,
  time: 0,
});
const b = (x) => new Uint8Array(32).fill(x);
const oneSided = { is_left: false, left: { bytes: b(0) }, right: { bytes: b(7) } };
const twoSided = { is_left: false, left: { bytes: b(9) }, right: { bytes: b(7) } };

const m1 = await attempt(() => mine.circuits.mintUTo(ctx(mi), 5n, oneSided));
const t1 = await attempt(() => theirs.circuits.mintUTo(ctx(ti), 5n, oneSided));
report(!m1.error && !t1.error, 'mintUTo with a one-sided Either: both complete', m1.error ?? t1.error ?? '');
const m2 = await attempt(() => mine.circuits.mintUTo(ctx(mi), 5n, twoSided));
const t2 = await attempt(() => theirs.circuits.mintUTo(ctx(ti), 5n, twoSided));
report(!!m2.error && !!t2.error, 'mintUTo with both sides set: both fail',
  `[executor: ${m2.error ?? 'completed'}] [compactc: ${t2.error ?? 'completed'}]`);

console.log(failures ? `${failures} FAILED` : 'all ok');
process.exit(failures ? 1 : 0);
