// Deploy the `counter` contract to the local network and call it, through
// midnight-js 5.0.0, with real proofs from the local proof server.
//
//   node src/run.mjs compact   # compactc 0.36.1 output: contract/index.js + keys + zkir
//   node src/run.mjs damp      # Damp output: contract.json + generic executor + keys + zkir
//
// Both paths use the same providers, wallet and calls; only the contract
// module and the artifact directory differ.

import fs from 'node:fs';
import path from 'node:path';
import { deployContract, findDeployedContract, submitCallTx } from '@midnight-ntwrk/midnight-js-contracts';
import { log, root, show, loadFlavour, startWallet, makeProviders, readLedger, runMain } from './common.mjs';

const mode = process.argv[2];
if (mode !== 'compact' && mode !== 'damp' && mode !== 'packaged') {
  console.error('usage: node src/run.mjs compact|damp|packaged');
  process.exit(2);
}

// [circuit, args]; expected ledger afterwards: count 12, total 97 (= 100 - delta 3), cap 24 (= 8 + 16 + 0)
const CALLS = [
  ['bump', [5n, true, false]],
  ['bump', [7n, true, true]],
  ['arith', [4n, 4n, 100n]],
];
const EXPECTED = { count: 12n, total: 97n, cap: 24n };

runMain(async () => {
  const c = await loadFlavour(mode);
  log.info(`[${mode}] artifact dir: ${c.dir}`);
  const wallet = await startWallet();
  try {
    const providers = makeProviders(wallet, c.dir);

    log.info('Deploying...');
    const t0 = Date.now();
    const deployed = await deployContract(providers, {
      compiledContract: c.compiled, privateStateId: 'counterPS', initialPrivateState: {},
    });
    const d = deployed.deployTxData.public;
    const address = d.contractAddress;
    log.info(`DEPLOYED address=${address} txId=${d.txId} txHash=${d.txHash} block=${d.blockHeight} (${Date.now() - t0} ms)`);
    log.info(`ledger after deploy: ${show(await readLedger(providers, c.ledger, address))}`);

    const txs = [];
    for (const [circuitId, args] of CALLS) {
      const t1 = Date.now();
      const r = await submitCallTx(providers, {
        compiledContract: c.compiled, contractAddress: address, privateStateId: 'counterPS', circuitId, args,
      });
      const p = r.public;
      txs.push({ circuitId, args, result: r.private.result, txId: p.txId, txHash: p.txHash, block: p.blockHeight, status: p.status });
      log.info(`CALL ${circuitId}(${args.join(', ')}) result=${r.private.result} txId=${p.txId} txHash=${p.txHash} block=${p.blockHeight} status=${p.status} (${Date.now() - t1} ms)`);
      log.info(`ledger after ${circuitId}: ${show(await readLedger(providers, c.ledger, address))}`);
    }

    // Join the deployed contract afresh, as a second client would (this also
    // compares the on-chain verifier keys with the local ones).
    const found = await findDeployedContract(providers, {
      compiledContract: c.compiled, contractAddress: address, privateStateId: 'counterPS',
    });
    log.info(`findDeployedContract ok: address=${found.deployTxData.public.contractAddress}`);

    const final = await readLedger(providers, c.ledger, address);
    log.info(`FINAL ledger (indexer): ${show(final)}`);
    const ok = Object.entries(EXPECTED).every(([k, v]) => final[k] === v);
    log.info(ok ? `RESULT ok: ledger matches expected ${show(EXPECTED)}` : `RESULT MISMATCH: expected ${show(EXPECTED)}`);
    if (c.touched) log.info(`contract-module accesses observed: ${show([...c.touched].sort())}`);
    fs.mkdirSync(path.join(root, 'out'), { recursive: true });
    fs.writeFileSync(path.join(root, 'out', `${mode}-result.json`),
      show({ mode, address, deploy: d, calls: txs, final, touched: c.touched ? [...c.touched].sort() : undefined }, 2) + '\n');
    process.exitCode = ok ? 0 : 1;
  } finally {
    await wallet.stop().catch(() => {});
  }
});
