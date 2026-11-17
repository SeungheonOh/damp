// Extra evidence beyond run.mjs:
//
//  A. Interop: deploy with compactc's module, then call the SAME on-chain
//     contract through the Damp executor (and back). Works only if the
//     executor's proof data and Damp's prover keys match what the deployed
//     (compactc) verifier keys accept.
//  B. Negative control: a Damp bundle whose keys/bump.verifier is replaced by
//     arith.verifier. Deploying registers the wrong verifier key for `bump`;
//     a `bump` call must then be rejected somewhere. Shows that the successful
//     calls in run.mjs were genuinely proof-checked rather than waved through.
//
//   node src/checks.mjs            # both
//   node src/checks.mjs interop|negative

import fs from 'node:fs';
import path from 'node:path';
import { deployContract, findDeployedContract, submitCallTx } from '@midnight-ntwrk/midnight-js-contracts';
import { ZKConfigRegistry } from '@midnight-ntwrk/midnight-js-types';
import { NodeZkConfigProvider } from '@midnight-ntwrk/midnight-js-node-zk-config-provider';
import { httpClientProofProvider } from '@midnight-ntwrk/midnight-js-http-client-proof-provider';
import { log, root, show, NET, loadFlavour, startWallet, makeProviders, readLedger, runMain } from './common.mjs';

const which = process.argv[2] ?? 'all';
const results = {};

async function call(providers, c, address, circuitId, args) {
  const r = await submitCallTx(providers, { compiledContract: c.compiled, contractAddress: address, privateStateId: 'ps', circuitId, args });
  const p = r.public;
  log.info(`  [${c.kind}] CALL ${circuitId}(${args.join(', ')}) result=${r.private.result} txId=${p.txId} block=${p.blockHeight} status=${p.status}`);
  return { kind: c.kind, circuitId, args, result: r.private.result, txId: p.txId, block: p.blockHeight, status: p.status };
}

async function interop(wallet) {
  log.info('=== A. interop: deploy compactc, call via Damp executor, and back ===');
  const compact = await loadFlavour('compact');
  const damp = await loadFlavour('damp', { bundle: 'damp-counter-interop' });
  const pc = makeProviders(wallet, compact.dir);
  const pd = makeProviders(wallet, damp.dir);
  const dep = await deployContract(pc, { compiledContract: compact.compiled, privateStateId: 'ps', initialPrivateState: {} });
  const address = dep.deployTxData.public.contractAddress;
  log.info(`  [compact] DEPLOYED ${address} block=${dep.deployTxData.public.blockHeight}`);
  const found = await findDeployedContract(pd, { compiledContract: damp.compiled, contractAddress: address, privateStateId: 'ps', initialPrivateState: {} });
  log.info(`  [damp] findDeployedContract on the compactc-deployed contract ok (${found.deployTxData.public.contractAddress})`);
  const calls = [];
  calls.push(await call(pd, damp, address, 'bump', [10n, true, false]));
  calls.push(await call(pc, compact, address, 'bump', [1n, true, true]));
  calls.push(await call(pd, damp, address, 'arith', [3n, 3n, 50n]));
  const viaCompact = await readLedger(pc, compact.ledger, address);
  const viaDamp = await readLedger(pd, damp.ledger, address);
  log.info(`  ledger via compactc ledger(): ${show(viaCompact)}; via adapter ledger(): ${show(viaDamp)}`);
  // bump 10 -> count 10, total 10; bump 1 (stop) -> count 11; arith(3,3,50) with delta 3 -> cap 6+9+0 = 15, total 47
  const expected = { count: 11n, total: 47n, cap: 15n };
  const ok = [viaCompact, viaDamp].every((l) => Object.entries(expected).every(([k, v]) => l[k] === v));
  log.info(ok ? `  INTEROP ok: matches ${show(expected)}` : `  INTEROP MISMATCH: expected ${show(expected)}`);
  if (!ok) process.exitCode = 1;
  results.interop = { address, deployBlock: dep.deployTxData.public.blockHeight, calls, viaCompact, viaDamp };
}

const errorChain = (e) => {
  const chain = [];
  for (let x = e; x && chain.length < 6; x = x.cause) chain.push(`${x.name ?? ''}: ${x.message ?? String(x)}`);
  return chain;
};

async function attemptBump(label, providers, c, address) {
  try {
    const r = await call(providers, c, address, 'bump', [5n, true, false]);
    log.error(`  ${label}: NEGATIVE CONTROL FAILED: bump against a wrong verifier key was accepted`);
    process.exitCode = 1;
    return { rejected: false, r };
  } catch (e) {
    const error = errorChain(e);
    log.info(`  ${label}: rejected as expected:\n    ${error.join('\n    ')}`);
    return { rejected: true, error };
  }
}

async function negative(wallet) {
  log.info('=== B. negative control: wrong verifier key registered for bump ===');
  const good = await loadFlavour('damp', { bundle: 'damp-counter-goodkeys' });
  const bad = await loadFlavour('damp', {
    bundle: 'damp-counter-badvk',
    mutate: (dir) => fs.copyFileSync(path.join(dir, 'keys', 'arith.verifier'), path.join(dir, 'keys', 'bump.verifier')),
  });
  const p = makeProviders(wallet, bad.dir);
  const dep = await deployContract(p, { compiledContract: bad.compiled, privateStateId: 'ps', initialPrivateState: {} });
  const address = dep.deployTxData.public.contractAddress;
  log.info(`  [damp-badvk] DEPLOYED ${address} block=${dep.deployTxData.public.blockHeight} (bump registered with arith's verifier key)`);

  // B1: everything from the bad bundle. The proof server proves with bump.prover
  // and self-verifies against the (wrong) bump.verifier it is sent.
  const b1 = await attemptBump('B1 (proof server self-check)', p, bad, address);

  // B2: get past every client-side check so that only the node is left.
  // midnight-js's proof provider resolves key material by joining the deployed
  // verifier key against the local bundle (ZKConfigRegistry), and the proof
  // server self-verifies the proof against the verifier key it is sent. This
  // registry matches against the bad bundle (as deployed) but hands the proof
  // server the GOOD bump keys, so a valid bump proof is produced and submitted;
  // the node then checks it against the wrong key it holds on chain.
  class SwapRegistry extends ZKConfigRegistry {
    async resolveKeyLocation(keyLocation) {
      const r = await super.resolveKeyLocation(keyLocation);
      if (r === undefined) return r;
      const g = await goodZk.get(r.circuitId);
      return { ...r, proverKey: g.proverKey, verifierKey: g.verifierKey, zkir: g.zkir };
    }
  }
  const goodZk = new NodeZkConfigProvider(good.dir);
  const p2 = { ...p, proofProvider: httpClientProofProvider(NET.proofServer, new SwapRegistry([new NodeZkConfigProvider(bad.dir)])) };
  const b2 = await attemptBump('B2 (node verification)', p2, bad, address);

  const after = await readLedger(p, bad.ledger, address);
  log.info(`  ledger after the rejected calls: ${show(after)}`);
  results.negative = { address, deployBlock: dep.deployTxData.public.blockHeight, b1, b2, after };
}

runMain(async () => {
  const wallet = await startWallet();
  try {
    if (which === 'all' || which === 'interop') await interop(wallet);
    if (which === 'all' || which === 'negative') await negative(wallet);
  } finally {
    fs.mkdirSync(path.join(root, 'out'), { recursive: true });
    fs.writeFileSync(path.join(root, 'out', `checks-result.json`), show(results, 2) + '\n');
    await wallet.stop().catch(() => {});
  }
});
