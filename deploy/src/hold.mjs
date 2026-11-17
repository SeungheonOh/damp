// A Damp contract holding a shielded coin and spending it later, on the local
// network, through midnight-js 5.0.0 with real proofs.
//
//   node src/hold.mjs           Damp's build (contract.json + executor, packaged)
//   node src/hold.mjs compact   compactc 0.36.1's build of the same circuits
//                               (deploy/hold.compact -> artifacts/compact-hold), for comparison
//
// The `tokens` contract (Examples/Tokens.lean) is deployed with only the
// circuits used (the node refuses one transaction with all of them):
//   mint(1000, n, walletCoinPk)      the wallet gets 1000 of the contract's token T
//   keep({fresh nonce, T, 300})      the wallet pays a 300 coin to the contract, which
//                                    stores it with `writeCoin` (qualified with its
//                                    Merkle-tree index, looked up by the ledger)
//   spend(left(walletCoinPk), 100)   `sendShielded` of the stored coin: 100 back to the
//                                    wallet, 200 change to the contract, stored again
//   mergeHeld({fresh nonce, T, 50})  the wallet pays 50 more; `mergeCoinImmediate` of
//                                    the stored coin and the new one, stored again
// After each step it prints what the indexer shows for the contract's `held`
// cell and what the wallet shows for T. Every call is attempted; a failure is
// printed with its causes and the script goes on to read the state.
//
// Artifacts: ../build/oracle-tok/lean/tokens (or $DAMP_OUT/lean/tokens).

import fs from 'node:fs';
import path from 'node:path';
import * as Rx from 'rxjs';
import { CompiledContract } from '@midnight-ntwrk/compact-js';
import { deployContract, submitCallTx } from '@midnight-ntwrk/midnight-js-contracts';
import * as rt from '@midnight-ntwrk/compact-runtime';
import { log, root, bytes, startWallet, makeProviders, readLedger, runMain } from './common.mjs';
import { packageContract } from '../../executor/src/package.mjs';

const built = path.resolve(root, '..', process.env.DAMP_OUT ?? 'build/oracle-tok', 'lean', 'tokens');
const USED = ['mint', 'keep', 'spend', 'mergeHeld'];
const MODE = process.argv[2] ?? 'damp';
const show = (x, indent) => JSON.stringify(x, (_, v) =>
  (typeof v === 'bigint' ? v.toString() : v instanceof Uint8Array ? Buffer.from(v).toString('hex') : v), indent);
const pad32 = (s) => { const b = new Uint8Array(32); b.set(new TextEncoder().encode(s)); return b; };
const tokenType = (ds, addressHex) => rt.persistentCommit(
  new rt.CompactTypeVector(2, new rt.CompactTypeBytes(32)),
  [pad32(ds), Buffer.from(addressHex, 'hex')], pad32('midnight:derive_token'));

runMain(async () => {
  const wallet = await startWallet();
  const result = { steps: [] };
  try {
    const coinPk = Buffer.from(wallet.getCoinPublicKey(), 'hex');
    log.info(`wallet coin public key: ${coinPk.toString('hex')}`);

    let dir, mod;
    if (MODE === 'compact') {
      dir = path.join(root, 'artifacts', 'compact-hold');
      mod = await import(path.join(dir, 'contract', 'index.js'));
    } else {
    // The deployable subset of the contract (see src/tokens.mjs).
    const subset = path.join(root, 'build', 'hold-subset');
    fs.rmSync(subset, { recursive: true, force: true });
    for (const d of ['keys', 'zkir']) fs.mkdirSync(path.join(subset, d), { recursive: true });
    const spec = JSON.parse(fs.readFileSync(path.join(built, 'contract.json'), 'utf-8'));
    spec.circuits = spec.circuits.filter((c) => USED.includes(c.name));
    fs.writeFileSync(path.join(subset, 'contract.json'), JSON.stringify(spec));
    for (const c of USED) {
      for (const f of [`keys/${c}.prover`, `keys/${c}.verifier`, `zkir/${c}.zkir`, `zkir/${c}.bzkir`]) {
        fs.copyFileSync(path.join(built, f), path.join(subset, f));
      }
    }
    ({ dir } = packageContract(subset, path.join(root, 'build', 'packaged-hold')));
    mod = await import(path.join(dir, 'contract', 'index.js'));
    }
    log.info(`[hold] mode ${MODE}, artifacts ${dir}`);
    const compiled = CompiledContract.make('tokens-hold', mod.Contract).pipe(
      CompiledContract.withWitnesses({}), CompiledContract.withCompiledFileAssets(dir));
    const providers = makeProviders(wallet, dir);
    const deployed = await deployContract(providers, { compiledContract: compiled, privateStateId: 'holdPS', initialPrivateState: {} });
    const d = deployed.deployTxData.public;
    const address = d.contractAddress;
    log.info(`[hold] DEPLOYED address=${address} txHash=${d.txHash} block=${d.blockHeight}`);
    const T = Buffer.from(tokenType('damp:token', address));
    const Thex = T.toString('hex');
    log.info(`[hold] token type T = ${Thex}`);
    result.address = address; result.token = Thex;

    const walletT = async (pred = () => true, ms = 120_000) => {
      let last;
      try {
        last = await Rx.firstValueFrom(wallet.wallet.state().pipe(
          Rx.tap((s) => { last = s; }), Rx.filter((s) => pred(s.shielded.balances[Thex] ?? 0n)), Rx.take(1), Rx.timeout(ms)));
      } catch { log.warn(`[hold] wallet balance of T did not reach the expected value within ${ms} ms`); }
      return last?.shielded.balances[Thex] ?? 0n;
    };
    const held = async () => (await readLedger(providers, mod.ledger, address)).held;

    const steps = [
      ['mint', [1000n, bytes(32, 0x68, 0x31), { bytes: coinPk }], (b) => b === 1000n],
      ['keep', [{ nonce: crypto.getRandomValues(new Uint8Array(32)), color: T, value: 300n }], (b) => b === 700n],
      ['spend', [{ is_left: true, left: { bytes: coinPk }, right: { bytes: new Uint8Array(32) } }, 100n], (b) => b === 800n],
      ['mergeHeld', [{ nonce: crypto.getRandomValues(new Uint8Array(32)), color: T, value: 50n }], () => true],
    ];
    for (const [circuitId, args, expectWallet] of steps) {
      const step = { circuitId, args: show(args) };
      result.steps.push(step);
      try {
        const r = await submitCallTx(providers, { compiledContract: compiled, contractAddress: address, privateStateId: 'holdPS', circuitId, args });
        Object.assign(step, { txHash: r.public.txHash, block: r.public.blockHeight, status: r.public.status,
          zswap: show(r.private.nextZswapLocalState ?? null) });
        log.info(`[hold] CALL ${circuitId} txHash=${r.public.txHash} block=${r.public.blockHeight} status=${r.public.status}`);
      } catch (e) {
        step.error = e?.message ?? String(e);
        const causes = []; let c = e?.cause; let k = 0;
        while (c && k++ < 8) { causes.push(c?.message ?? show(c)); c = c.cause; }
        step.causes = causes;
        log.error(`[hold] CALL ${circuitId} FAILED: ${step.error}${causes.length ? `\n  causes: ${causes.join('\n  ')}` : ''}`);
      }
      step.held = show(await held());
      step.walletT = (await walletT(step.error ? () => true : expectWallet, 60_000)).toString();
      log.info(`[hold] after ${circuitId}: held (indexer) = ${step.held}`);
      log.info(`[hold] after ${circuitId}: wallet shielded balance of T = ${step.walletT}`);
    }
    fs.mkdirSync(path.join(root, 'out'), { recursive: true });
    fs.writeFileSync(path.join(root, 'out', `hold-${MODE}-result.json`), show(result, 2) + '\n');
  } finally {
    await wallet.stop().catch(() => {});
  }
});
