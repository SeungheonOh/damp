// The `vault` contract: has a constructor with arguments, a Bytes<32> ledger
// cell, a persistentHash-checked witness and a pure circuit (`digest`).
//
//   node src/vault.mjs damp | compact
//
// deploy(owner = persistentHash(key), limit = 40); spend(30); spend(5);
// spend(6) must fail locally ("over limit") before any proof is made.

import fs from 'node:fs';
import path from 'node:path';
import * as rt from '@midnight-ntwrk/compact-runtime';
import { deployContract, submitCallTx } from '@midnight-ntwrk/midnight-js-contracts';
import { log, root, show, VAULT_KEY, loadFlavour, startWallet, makeProviders, readLedger, runMain } from './common.mjs';

const mode = process.argv[2] ?? 'damp';
const hex = (b) => Buffer.from(b).toString('hex');

runMain(async () => {
  const c = await loadFlavour(mode, { name: 'vault' });
  const owner = rt.persistentHash(new rt.CompactTypeBytes(32), VAULT_KEY);
  const wallet = await startWallet();
  const out = { mode, calls: [] };
  try {
    const p = makeProviders(wallet, c.dir);
    const dep = await deployContract(p, {
      compiledContract: c.compiled, privateStateId: 'vps', initialPrivateState: {}, args: [owner, 40n],
    });
    const d = dep.deployTxData.public;
    out.address = d.contractAddress; out.deploy = d;
    log.info(`[${mode}] vault DEPLOYED address=${d.contractAddress} txId=${d.txId} block=${d.blockHeight}`);
    const l0 = await readLedger(p, c.ledger, d.contractAddress);
    log.info(`ledger after deploy: owner=${hex(l0.owner)} limit=${l0.limit} spent=${l0.spent}  (expected owner=${hex(owner)})`);
    for (const amount of [30n, 5n, 6n]) {
      try {
        const r = await submitCallTx(p, { compiledContract: c.compiled, contractAddress: d.contractAddress, privateStateId: 'vps', circuitId: 'spend', args: [amount] });
        log.info(`CALL spend(${amount}) txId=${r.public.txId} block=${r.public.blockHeight} status=${r.public.status}`);
        out.calls.push({ amount, txId: r.public.txId, block: r.public.blockHeight, status: r.public.status });
      } catch (e) {
        const msgs = []; for (let x = e; x && msgs.length < 4; x = x.cause) msgs.push(x.message);
        log.info(`CALL spend(${amount}) failed: ${msgs.join(' <- ')}`);
        out.calls.push({ amount, error: msgs });
      }
      const l = await readLedger(p, c.ledger, d.contractAddress);
      log.info(`  ledger: limit=${l.limit} spent=${l.spent}`);
    }
    const final = await readLedger(p, c.ledger, d.contractAddress);
    out.final = { owner: hex(final.owner), limit: final.limit, spent: final.spent };
    const ok = hex(final.owner) === hex(owner) && final.limit === 40n && final.spent === 35n
      && out.calls[2].error !== undefined;
    log.info(ok ? 'RESULT ok: owner set by constructor, spent=35, third spend refused' : `RESULT MISMATCH ${show(out.final)}`);
    process.exitCode = ok ? 0 : 1;
  } finally {
    fs.mkdirSync(path.join(root, 'out'), { recursive: true });
    fs.writeFileSync(path.join(root, 'out', `vault-${mode}-result.json`), show(out, 2) + '\n');
    await wallet.stop().catch(() => {});
  }
});
