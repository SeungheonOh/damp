// Shared setup: network endpoints, genesis wallet, midnight-js providers,
// and loading either contract flavour as a CompiledContract.

import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { WebSocket } from 'ws';
import pino from 'pino';
import * as Rx from 'rxjs';
import { setNetworkId } from '@midnight-ntwrk/midnight-js-network-id';
import { CompiledContract } from '@midnight-ntwrk/midnight-js-protocol/v9/compact-js';
import { ContractState } from '@midnight-ntwrk/midnight-js-protocol/v9/compact-runtime';
import { indexerPublicDataProvider } from '@midnight-ntwrk/midnight-js-indexer-public-data-provider';
import { httpClientProofProvider } from '@midnight-ntwrk/midnight-js-http-client-proof-provider';
import { NodeZkConfigProvider } from '@midnight-ntwrk/midnight-js-node-zk-config-provider';
import {
  FluentWalletBuilder, MidnightWalletProvider, inMemoryPrivateStateProvider,
  logger as testkitLogger, syncWallet,
} from '@midnight-ntwrk/testkit-js';

globalThis.WebSocket = WebSocket; // GraphQL subscriptions in Node
testkitLogger.level = 'warn';

export const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
export const log = pino({ level: process.env.LOG_LEVEL ?? 'info', transport: { target: 'pino-pretty' } });

export const NET = {
  networkId: 'undeployed',
  indexer: process.env.MN_INDEXER ?? 'http://127.0.0.1:8088/api/v4/graphql',
  indexerWS: process.env.MN_INDEXER_WS ?? 'ws://127.0.0.1:8088/api/v4/graphql/ws',
  node: process.env.MN_NODE ?? 'http://127.0.0.1:9944',
  nodeWS: process.env.MN_NODE_WS ?? 'ws://127.0.0.1:9944',
  proofServer: process.env.MN_PROOF_SERVER ?? 'http://127.0.0.1:6300',
  faucet: '',
};
// Genesis-funded seed of the local `undeployed` devnet (public, dev only).
const SEED = process.env.MN_SEED ?? '0000000000000000000000000000000000000000000000000000000000000001';

/** `n` bytes: `first`, then zeros, then `last` (as executor/test/run.mjs builds them). */
export const bytes = (n, first, last) => { const b = new Uint8Array(n); b[0] = first; b[n - 1] = last; return b; };
export const VAULT_KEY = bytes(32, 21, 22);

export const witnesses = {
  delta: ({ privateState }) => [privateState, 3n],      // counter
  key: ({ privateState }) => [privateState, VAULT_KEY], // vault
};

export const show = (x, indent) => JSON.stringify(x, (_, v) => (typeof v === 'bigint' ? v.toString() : v), indent);

/**
 * One contract flavour as midnight-js wants it.
 *   kind 'compact': compactc's contract/index.js from artifacts/compact-counter
 *   kind 'damp':    Damp's contract.json via the adapter, bundled into build/<bundle>
 *   kind 'packaged': Damp's output packaged by executor/bin/damp-package.mjs, loaded with no adapter
 * `mutate(bundleDir)` may alter a Damp bundle before its manifest is written (negative controls).
 */
export async function loadFlavour(kind, { name = 'counter', bundle = `damp-${name}`, mutate } = {}) {
  let loaded;
  if (kind === 'compact') {
    const dir = path.join(root, 'artifacts', `compact-${name}`);
    const mod = await import(path.join(dir, 'contract', 'index.js'));
    loaded = { dir, Contract: mod.Contract, ledger: mod.ledger };
  } else if (kind === 'packaged') {
    // Damp's own packager: no adapter. The bundle sits under deploy/ so its
    // executor loads the same compact-runtime as midnight-js.
    const { packageContract } = await import('../../executor/src/package.mjs');
    const { dir } = packageContract(path.join(root, 'artifacts', `lean-${name}`), path.join(root, 'build', `packaged-${name}`));
    const mod = await import(path.join(dir, 'contract', 'index.js'));
    loaded = { dir, Contract: mod.Contract, ledger: mod.ledger };
  } else {
    const { prepareDampBundle } = await import('./damp-adapter.mjs');
    loaded = await prepareDampBundle(path.join(root, 'artifacts', `lean-${name}`), path.join(root, 'build', bundle), { mutate });
  }
  const compiled = CompiledContract.make(`${name}-${kind}`, loaded.Contract).pipe(
    CompiledContract.withWitnesses(witnesses),
    CompiledContract.withCompiledFileAssets(loaded.dir),
  );
  return { ...loaded, kind, compiled };
}

/** Start and sync the genesis wallet; wait for spendable DUST. */
export async function startWallet() {
  setNetworkId(NET.networkId);
  log.info('Building wallet from the genesis seed...');
  const env = { walletNetworkId: NET.networkId, ...NET };
  const { wallet: facade, seeds, keystore } = await FluentWalletBuilder.forEnvironment(env).withSeed(SEED).buildWithoutStarting();
  const wallet = await MidnightWalletProvider.withWallet(log, env, facade, seeds, keystore);
  await wallet.start(false);
  await syncWallet(wallet.wallet, 2_000, 300_000);
  const st = await Rx.firstValueFrom(wallet.wallet.state().pipe(
    Rx.filter((s) => s.dust.availableCoins.length > 0), Rx.take(1), Rx.timeout(300_000)));
  log.info(`Wallet synced. NIGHT: ${show(st.unshielded.balances)}  DUST: ${st.dust.balance(new Date())}`);
  return wallet;
}

/** midnight-js providers for one artifact directory. */
export function makeProviders(wallet, dir) {
  const zk = new NodeZkConfigProvider(dir);
  return {
    privateStateProvider: inMemoryPrivateStateProvider(),
    publicDataProvider: indexerPublicDataProvider(NET.indexer, NET.indexerWS),
    zkConfigProvider: zk,
    proofProvider: httpClientProofProvider(NET.proofServer, zk),
    walletProvider: wallet,
    midnightProvider: wallet,
    config: { networkId: NET.networkId, ttlSeconds: 3600 },
  };
}

/** Read the contract's public ledger back through the indexer and decode it with `ledger`. */
export async function readLedger(providers, ledger, address) {
  const read = await providers.publicDataProvider.queryContractState(address);
  if (read === null) throw new Error('contract state not found');
  return ledger(read.contractState.deserialize({ v9: ContractState }).data);
}

export function runMain(main) {
  main().catch((e) => {
    log.error(e?.stack ?? String(e));
    let c = e?.cause; let depth = 0;
    while (c && depth++ < 6) { log.error(`cause: ${c?.stack ?? c?.message ?? show(c)}`); c = c.cause; }
    process.exitCode = 1;
  }).then(() => process.exit(process.exitCode ?? 0));
}
