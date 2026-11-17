// Deploy the Damp `tokens` contract (Examples/Tokens.lean), packaged with
// executor/bin/damp-package.mjs, and mint tokens to the wallet on the local
// network, through midnight-js 5.0.0 with real proofs.
//
//   node src/tokens.mjs
//
// Calls, in order:
//   whoami()                          ownPublicKey(): must be the wallet's coin public key
//   mint(1000, nonce, walletCoinPk)   a shielded coin of this contract's token, to the wallet
//   mintU(500, walletUserAddress)     unshielded tokens of this contract's token, to the wallet
// then reads the contract's ledger from the indexer and waits for the wallet to
// show the new balances, printing exactly what it sees (it does not claim a
// balance it did not read).
//
// Artifacts are read from ../build/oracle-tok/lean/tokens (or $DAMP_OUT/lean/tokens).

import fs from 'node:fs';
import path from 'node:path';
import * as Rx from 'rxjs';
import { CompiledContract } from '@midnight-ntwrk/compact-js';
import { deployContract, submitCallTx } from '@midnight-ntwrk/midnight-js-contracts';
import * as rt from '@midnight-ntwrk/compact-runtime';
import { log, root, bytes, startWallet, makeProviders, readLedger, runMain } from './common.mjs';
import { packageContract } from '../../executor/src/package.mjs';

const built = path.resolve(root, '..', process.env.DAMP_OUT ?? 'build/oracle-tok', 'lean', 'tokens');
const USED = (process.env.TOKENS_CIRCUITS ?? 'whoami,mint,mintU,deposit,mintSelf,mintUTo,sendU,balU').split(',');
const show = (x, indent) => JSON.stringify(x, (_, v) =>
  (typeof v === 'bigint' ? v.toString() : v instanceof Uint8Array ? Buffer.from(v).toString('hex') : v), indent);
const hex = (b) => Buffer.from(b).toString('hex');
const pad32 = (s) => { const b = new Uint8Array(32); b.set(new TextEncoder().encode(s)); return b; };

/** Compact's `tokenType(pad(32, ds), ContractAddress { bytes: address })`. */
const tokenType = (ds, addressHex) => rt.persistentCommit(
  new rt.CompactTypeVector(2, new rt.CompactTypeBytes(32)),
  [pad32(ds), Buffer.from(addressHex, 'hex')], pad32('midnight:derive_token'));

const balancesOf = (st) => ({
  shielded: Object.fromEntries(Object.entries(st.shielded.balances)),
  unshielded: Object.fromEntries(Object.entries(st.unshielded.balances)),
});

/** Wait (up to `ms`) for the wallet state to satisfy `pred`; return the last state seen. */
async function waitWallet(wallet, pred, ms) {
  let last;
  try {
    return await Rx.firstValueFrom(wallet.wallet.state().pipe(
      Rx.tap((s) => { last = s; }), Rx.filter(pred), Rx.take(1), Rx.timeout(ms)));
  } catch (e) {
    log.warn(`wallet state did not reach the expected condition within ${ms} ms (${e?.name ?? e})`);
    return last;
  }
}

runMain(async () => {
  const wallet = await startWallet();
  const result = { steps: [] };
  try {
    const coinPkHex = wallet.getCoinPublicKey();
    const userAddrHex = wallet.unshieldedKeystore.getAddress();
    log.info(`wallet coin public key: ${coinPkHex}`);
    log.info(`wallet unshielded address (hex): ${userAddrHex}  bech32: ${wallet.unshieldedKeystore.getBech32Address().asString()}`);
    const before = balancesOf(await Rx.firstValueFrom(wallet.wallet.state()));
    log.info(`wallet balances before: ${show(before)}`);

    // Deploying all 20 circuits' verifier keys in one transaction is refused by
    // the node ("Transaction would exhaust the block limits"), so the contract
    // is deployed with the circuits used here only: the same contract.json with
    // the other circuits left out, as `contract tokens exports …` would build it.
    const subset = path.join(root, 'build', 'tokens-subset');
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
    const { dir } = packageContract(subset, path.join(root, 'build', 'packaged-tokens'));
    const mod = await import(path.join(dir, 'contract', 'index.js'));
    const compiled = CompiledContract.make('tokens-packaged', mod.Contract).pipe(
      CompiledContract.withWitnesses({}), CompiledContract.withCompiledFileAssets(dir));
    const providers = makeProviders(wallet, dir);
    const deployed = await deployContract(providers, { compiledContract: compiled, privateStateId: 'tokensPS', initialPrivateState: {} });
    const d = deployed.deployTxData.public;
    const address = d.contractAddress;
    log.info(`[tokens] DEPLOYED address=${address} txHash=${d.txHash} block=${d.blockHeight}`);

    const shieldedColor = hex(tokenType('damp:token', address));
    const unshieldedColor = hex(tokenType('damp:u', address));
    log.info(`expected shielded token type   tokenType("damp:token", self) = ${shieldedColor}`);
    log.info(`expected unshielded token type tokenType("damp:u", self)     = ${unshieldedColor}`);

    const zeros = new Uint8Array(32);
    const self = { bytes: Buffer.from(address, 'hex') };
    const calls = [
      ['whoami', []],
      ['mint', [1000n, bytes(32, 0x6e, 0x31), { bytes: Buffer.from(coinPkHex, 'hex') }]],
      ['mintU', [500n, { bytes: Buffer.from(userAddrHex, 'hex') }]],
      // Further, beyond the minimum: the wallet must supply a coin of the new
      // token for the contract to receive (Zswap balancing of a contract output);
      // the contract mints a coin to itself; unshielded tokens minted to the
      // contract and sent on from it to the wallet; the contract's balance.
      ['deposit', [{ nonce: crypto.getRandomValues(new Uint8Array(32)), color: Buffer.from(shieldedColor, 'hex'), value: 100n }]],
      ['mintSelf', [50n, bytes(32, 0x6e, 0x32)]],
      ['mintUTo', [40n, { is_left: true, left: self, right: { bytes: zeros } }]],
      ['sendU', [15n, { is_left: false, left: { bytes: zeros }, right: { bytes: Buffer.from(userAddrHex, 'hex') } }]],
      ['balU', []],
    ].filter(([c]) => USED.includes(c));
    for (const [circuitId, args] of calls) {
      const step = { circuitId, args: show(args) };
      result.steps.push(step);
      try {
        const r = await submitCallTx(providers, { compiledContract: compiled, contractAddress: address, privateStateId: 'tokensPS', circuitId, args });
        Object.assign(step, { result: show(r.private.result), txHash: r.public.txHash, block: r.public.blockHeight, status: r.public.status });
        log.info(`[tokens] CALL ${circuitId} result=${show(r.private.result)} txHash=${r.public.txHash} block=${r.public.blockHeight} status=${r.public.status}`);
      } catch (e) {
        step.error = e?.message ?? String(e);
        const causes = []; let c = e?.cause; let k = 0;
        while (c && k++ < 6) { causes.push(c?.message ?? show(c)); c = c.cause; }
        step.causes = causes;
        log.error(`[tokens] CALL ${circuitId} FAILED: ${step.error}${causes.length ? `\n  causes: ${causes.join('\n  ')}` : ''}`);
        log.error(e?.stack ?? '');
      }
    }

    const ledger = await readLedger(providers, mod.ledger, address);
    result.ledger = { last: ledger.last, color: ledger.color, owner: ledger.owner };
    log.info(`[tokens] ledger (indexer): ${show(result.ledger)}`);

    const st = await waitWallet(wallet, (s) => (s.shielded.balances[shieldedColor] ?? 0n) > 0n
      && (s.unshielded.balances[unshieldedColor] ?? 0n) > 0n, 180_000);
    // Read the contract's on-chain balances from the indexer's contract state.
    const read = await providers.publicDataProvider.queryContractState(address);
    try {
      const { ContractState } = await import('@midnight-ntwrk/midnight-js-protocol/v9/compact-runtime');
      const cs = read.contractState.deserialize({ v9: ContractState });
      result.contractBalance = show([...cs.balance.entries()]);
      log.info(`[tokens] contract balance (indexer contract state): ${result.contractBalance}`);
    } catch (e) { log.warn(`could not read the contract's balance: ${e?.message ?? e}`); }
    const after = balancesOf(st);
    result.walletBefore = before;
    result.walletAfter = after;
    log.info(`wallet balances after: ${show(after)}`);
    log.info(`wallet shielded balance of ${shieldedColor}: ${after.shielded[shieldedColor] ?? 'absent'}`);
    log.info(`wallet unshielded balance of ${unshieldedColor}: ${after.unshielded[unshieldedColor] ?? 'absent'}`);
    result.address = address;
    result.colors = { shielded: shieldedColor, unshielded: unshieldedColor };
    fs.mkdirSync(path.join(root, 'out'), { recursive: true });
    fs.writeFileSync(path.join(root, 'out', 'tokens-result.json'), show(result, 2) + '\n');
  } finally {
    await wallet.stop().catch(() => {});
  }
});
