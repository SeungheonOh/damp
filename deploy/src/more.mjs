// Deploy and call further Damp contracts, packaged with executor/bin/damp-package.mjs,
// on the local network: `extras` (enum, Set, Maybe, commitments, a Bytes witness)
// and `shapes` (struct, vector, Map). Usage: node src/more.mjs
//
// Artifacts are read straight from ../build/oracle-main/lean (or $DAMP_OUT/lean).

import path from 'node:path';
import { CompiledContract } from '@midnight-ntwrk/compact-js';
import { deployContract, submitCallTx } from '@midnight-ntwrk/midnight-js-contracts';
import { log, root, show, bytes, startWallet, makeProviders, readLedger, runMain } from './common.mjs';
import { packageContract } from '../../executor/src/package.mjs';

const built = path.resolve(root, '..', process.env.DAMP_OUT ?? 'build/oracle-main', 'lean');

const witnesses = {
  nonce: ({ privateState }) => [privateState, bytes(32, 11, 12)],
  pick: ({ privateState }) => [privateState, { x: 1000n, y: 9n }],
};

const scenarios = [
  { name: 'extras',
    calls: [['advance', [0, bytes(32, 1, 1), { is_some: true, value: 500n }, 42n]],
            ['advance', [1, bytes(32, 2, 2), { is_some: true, value: 50n }, 43n]]],
    read: (l) => ({ phase: l.phase, seen: l.seen.size(), best: l.best }),
    expect: (l) => l.phase === 1 && l.seen.size() === 2n && l.best.is_some === false },
  { name: 'shapes',
    calls: [['pay', [77n, 10n, 3n, 2n]], ['pay', [77n, 5n, 2n, 2n]],
            ['move', [{ x: 5n, y: 2n }, [1n, 2n, 3n], true, true]]],
    read: (l) => ({ balance77: l.balances.lookup(77n), entries: l.balances.size(), origin: l.origin, flag: l.flag }),
    expect: (l) => l.balances.lookup(77n) === 15n && l.origin.x === 1011n && l.origin.y === 9n },
];

runMain(async () => {
  const wallet = await startWallet();
  let ok = true;
  try {
    for (const s of scenarios) {
      const { dir } = packageContract(path.join(built, s.name), path.join(root, 'build', `packaged-${s.name}`));
      const mod = await import(path.join(dir, 'contract', 'index.js'));
      const compiled = CompiledContract.make(`${s.name}-packaged`, mod.Contract).pipe(
        CompiledContract.withWitnesses(witnesses), CompiledContract.withCompiledFileAssets(dir));
      const providers = makeProviders(wallet, dir);
      const deployed = await deployContract(providers, { compiledContract: compiled, privateStateId: `${s.name}PS`, initialPrivateState: {} });
      const d = deployed.deployTxData.public;
      log.info(`[${s.name}] DEPLOYED address=${d.contractAddress} txHash=${d.txHash} block=${d.blockHeight}`);
      for (const [circuitId, args] of s.calls) {
        const r = await submitCallTx(providers, { compiledContract: compiled, contractAddress: d.contractAddress, privateStateId: `${s.name}PS`, circuitId, args });
        log.info(`[${s.name}] CALL ${circuitId} result=${show(r.private.result)} txHash=${r.public.txHash} block=${r.public.blockHeight} status=${r.public.status}`);
      }
      const ledger = await readLedger(providers, mod.ledger, d.contractAddress);
      const good = s.expect(ledger);
      ok &&= good;
      log.info(`[${s.name}] FINAL ledger (indexer): ${show(s.read(ledger))}`);
      log.info(`[${s.name}] RESULT ${good ? 'ok' : 'MISMATCH'}`);
    }
    process.exitCode = ok ? 0 : 1;
  } finally {
    await wallet.stop().catch(() => {});
  }
});
