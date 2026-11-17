// The optimizer must not change behaviour. Runs the same calls against the
// optimized and unoptimized builds of the `tuned` contract and requires equal
// results, equal ledger state, and acceptance of both by the ZKIR checker.
//
// Usage: node test/opt.mjs <dir holding plain/ and opt/>

import fs from 'node:fs/promises';
import path from 'node:path';
import * as rt from '@midnight-ntwrk/compact-runtime';
import { makeContract } from '../src/executor.mjs';
import { checkProofData } from '../harness/check.mjs';
import { toJson, proofDataOf } from '../harness/json.mjs';

const root = path.resolve(process.argv[2]);
const COIN_PK = '0'.repeat(64);
let failures = 0;
const report = (ok, label, detail = '') => {
  if (!ok) failures++;
  console.log(`${ok ? 'ok   ' : 'FAIL '} ${label}${detail ? '  ' + detail : ''}`);
};

async function load(variant) {
  const dir = path.join(root, variant, 'tuned');
  const contract = makeContract(JSON.parse(await fs.readFile(path.join(dir, 'contract.json'), 'utf-8')));
  const init = await contract.initialState(rt.createConstructorContext({}, COIN_PK));
  return { dir, contract, init, state: undefined };
}

const context = (c) =>
  rt.createCircuitContext({
    circuitId: 'settle',
    contractAddress: rt.dummyContractAddress(),
    coinPublicKeyOrZswapState: c.init.currentZswapLocalState.coinPublicKey,
    contractState: c.state ?? c.init.currentContractState,
    privateState: c.init.currentPrivateState,
    time: 0,
  });

const plain = await load('plain');
const opt = await load('opt');

for (const args of [[[10n, 20n, 30n, 40n], true], [[1n, 2n, 3n, 4n], false], [[65535n, 0n, 65535n, 1n], true]]) {
  const label = `tuned.settle(${toJson(args, 0)})`.replaceAll('"', '');
  const results = [];
  for (const c of [plain, opt]) {
    const run = await c.contract.circuits.settle(context(c), ...args);
    c.state = run.context.callContext.currentQueryContext.state;
    const checked = await checkProofData({
      compiledDir: c.dir, circuitId: 'settle', proofData: proofDataOf(run.context.callProofDataTrace.at(-1)),
    });
    report(checked.ok, `${label}: ZKIR check accepts the ${c === plain ? 'unoptimized' : 'optimized'} circuit`,
      checked.ok ? '' : `${checked.stage}: ${checked.error}`);
    results.push({ result: run.result, state: c.state.state.encode() });
  }
  report(toJson(results[0], 0) === toJson(results[1], 0), `${label}: same result and ledger state`, `= ${results[1].result}`);
}

console.log(failures === 0 ? '\noptimized and unoptimized circuits agree' : `\n${failures} check(s) failed`);
process.exit(failures === 0 ? 0 : 1);
