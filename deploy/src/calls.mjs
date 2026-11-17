// Cross-contract calls on the local network (docs/calls.md), with Damp
// contracts packaged by executor/src/package.mjs.
//
//   node src/calls.mjs [simple|nested|cast|all]      (default: all)
//
// simple: deploy `adder` and `rich`, then `caller(adder, rich)`; call
//         caller.bump(5), which calls adder.addTo(5); read both ledgers back.
// nested: deploy `relay(adder)` and `top(relay)`; call top.go(9), which calls
//         relay.relay(9), which calls adder.addTo(9).
// cast:   deploy `picker`; call picker.viaArg(<adder's address as Bytes 32>, 3),
//         register(1, <adder's address>), viaMap(1, 4): the callee chosen at run
//         time from an address cast to a contract type.
//
// The contracts are read from ../build/oracle-cc/lean (`DAMP_OUT=build/oracle-cc
// ../test/oracle.sh` builds them with keys; set DAMP_OUT to use another build).
// midnight-js gets what a cross-contract call needs: a `contractModuleProvider`
// (callee address -> the callee's packaged `contract/index.js`) and, as
// `zkConfigProvider`, a registry over every packaged contract's keys, so that
// the proof of each call in the tree finds its prover key.

import fs from 'node:fs';
import path from 'node:path';
import * as rt from '@midnight-ntwrk/compact-runtime';
import { CompiledContract } from '@midnight-ntwrk/compact-js';
import { deployContract, submitCallTx } from '@midnight-ntwrk/midnight-js-contracts';
import { ZKConfigRegistry } from '@midnight-ntwrk/midnight-js-types';
import { NodeZkConfigProvider } from '@midnight-ntwrk/midnight-js-node-zk-config-provider';
import { httpClientProofProvider } from '@midnight-ntwrk/midnight-js-http-client-proof-provider';
import { log, root, show, NET, startWallet, makeProviders, readLedger, runMain } from './common.mjs';
import { packageContract } from '../../executor/src/package.mjs';

const mode = process.argv[2] ?? 'all';
const built = path.resolve(root, '..', process.env.DAMP_OUT ?? 'build/oracle-cc', 'lean');
const names = ['adder', 'rich', 'caller', 'relay', 'top', 'picker'];

/** Every message down an error's `cause` chain. */
const messages = (e) => { const m = []; for (let x = e; x && m.length < 8; x = x.cause) m.push(x.message ?? String(x)); return m; };

/** Ask the indexer's GraphQL API. */
async function graphql(query, variables = {}) {
  const res = await fetch(NET.indexer, { method: 'POST', headers: { 'content-type': 'application/json' }, body: JSON.stringify({ query, variables }) });
  return res.json();
}

runMain(async () => {
  const out = { mode, steps: [] };
  const pkg = {};
  for (const n of names) {
    const { dir } = packageContract(path.join(built, n), path.join(root, 'build', 'calls', n));
    const mod = await import(path.join(dir, 'contract', 'index.js'));
    const compiled = CompiledContract.make(`${n}-damp`, mod.Contract).pipe(
      CompiledContract.withWitnesses({}), CompiledContract.withCompiledFileAssets(dir));
    pkg[n] = { dir, mod, compiled };
  }
  // Which contract is deployed where; the module provider serves the callees from it.
  const deployedAt = new Map();
  const contractModuleProvider = {
    resolve: (address) => {
      const n = deployedAt.get(String(address));
      return n === undefined ? undefined : async () => pkg[n].mod;
    },
  };
  const registry = new ZKConfigRegistry(names.map((n) => new NodeZkConfigProvider(pkg[n].dir)));

  const wallet = await startWallet();
  try {
    const base = makeProviders(wallet, pkg.adder.dir);
    const providersFor = (n) => ({ ...base, zkConfigProvider: new NodeZkConfigProvider(pkg[n].dir),
      proofProvider: httpClientProofProvider(NET.proofServer, new NodeZkConfigProvider(pkg[n].dir)) });
    // The caller's own artifacts as `zkConfigProvider` (midnight-js reads the
    // contract's runtime version from it, which a registry cannot answer:
    // "source.getArtifactRuntimeVersion is not a function"); the registry over
    // every contract behind the proof provider, which resolves the key of each
    // call in the tree by its verifier key's hash.
    const callProviders = (n) => ({ ...providersFor(n), proofProvider: httpClientProofProvider(NET.proofServer, registry), contractModuleProvider });
    const ref = (n) => ({ bytes: rt.encodeContractAddress(out[n].address) });

    const deploy = async (n, args = []) => {
      const dep = await deployContract(providersFor(n), { compiledContract: pkg[n].compiled, privateStateId: `${n}PS`, initialPrivateState: {}, args });
      const d = dep.deployTxData.public;
      deployedAt.set(String(d.contractAddress), n);
      out[n] = { address: d.contractAddress, deployTx: d.txHash ?? d.txId, block: d.blockHeight };
      log.info(`[${n}] DEPLOYED address=${d.contractAddress} tx=${d.txHash ?? d.txId} block=${d.blockHeight}`);
    };
    const call = async (n, circuitId, args) => {
      const label = `${n}.${circuitId}(${args.map((a) => show(a)).join(', ')})`;
      try {
        const r = await submitCallTx(callProviders(n), { compiledContract: pkg[n].compiled, contractAddress: out[n].address, privateStateId: `${n}PS`, circuitId, args });
        const step = { call: label, result: r.private.result, tx: r.public.txHash ?? r.public.txId, block: r.public.blockHeight, status: r.public.status,
          calls: (r.calls ?? []).map((c) => `${deployedAt.get(String(c.contractAddress)) ?? c.contractAddress}.${c.circuitId}`) };
        out.steps.push(step);
        log.info(`CALL ${label} result=${show(r.private.result)} tx=${step.tx} block=${step.block} status=${step.status}`);
        return step;
      } catch (e) {
        const step = { call: label, error: messages(e) };
        out.steps.push(step);
        log.error(`CALL ${label} FAILED: ${messages(e).join(' <- ')}`);
        return step;
      }
    };
    const ledgers = async (ns) => {
      const view = {};
      for (const n of ns) {
        const l = await readLedger(base, pkg[n].mod.ledger, out[n].address);
        const hex = (b) => Buffer.from(b).toString('hex');
        view[n] = Object.fromEntries(Object.keys(l).map((k) =>
          [k, l[k] instanceof Uint8Array ? hex(l[k]) : typeof l[k] === 'object' && l[k]?.bytes ? hex(l[k].bytes) : l[k]]));
      }
      log.info(`LEDGERS (indexer): ${show(view)}`);
      return view;
    };
    const actions = async (ns) => {
      const seen = {};
      for (const n of ns) {
        const r = await graphql(`query ($a: HexEncoded!) { contractAction(address: $a) { __typename address
          ... on ContractCall { entryPoint transaction { hash block { height } } }
          ... on ContractDeploy { transaction { hash block { height } } } } }`, { a: out[n].address });
        seen[n] = r.data?.contractAction ?? r.errors;
      }
      log.info(`INDEXER latest contract actions: ${show(seen)}`);
      return seen;
    };
    /** The indexer's view of one transaction: its result and every contract action in it. */
    const transaction = async (hash) => {
      const r = await graphql(`query ($h: HexEncoded!) { transactions(offset: { hash: $h }) { hash block { height }
        ... on RegularTransaction { transactionResult { status } }
        contractActions { __typename address ... on ContractCall { entryPoint } } } }`, { h: hash });
      const t = r.data?.transactions ?? r.errors;
      log.info(`INDEXER transaction ${hash}: ${show(t)}`);
      return t;
    };

    if (mode === 'simple' || mode === 'all') {
      await deploy('adder');
      await deploy('rich');
      await deploy('caller', [ref('adder'), ref('rich')]);
      out.simpleBefore = await ledgers(['adder', 'caller']);
      out.simpleCall = await call('caller', 'bump', [5n]);
      out.simpleAfter = await ledgers(['adder', 'caller']);
      out.simpleActions = await actions(['adder', 'caller']);
      if (out.simpleCall.tx) out.simpleTx = await transaction(out.simpleCall.tx);
    }
    if (mode === 'nested' || mode === 'all') {
      if (!out.adder) await deploy('adder');
      await deploy('relay', [ref('adder')]);
      await deploy('top', [ref('relay')]);
      out.nestedBefore = await ledgers(['adder', 'relay', 'top']);
      out.nestedCall = await call('top', 'go', [9n]);
      out.nestedAfter = await ledgers(['adder', 'relay', 'top']);
      out.nestedActions = await actions(['adder', 'relay', 'top']);
      if (out.nestedCall.tx) out.nestedTx = await transaction(out.nestedCall.tx);
    }
    if (mode === 'cast' || mode === 'all') {
      if (!out.adder) await deploy('adder');
      await deploy('picker');
      const adderBytes = rt.encodeContractAddress(out.adder.address);
      out.castBefore = await ledgers(['adder']);
      out.castArg = await call('picker', 'viaArg', [adderBytes, 3n]);
      out.castRegister = await call('picker', 'register', [1n, adderBytes]);
      out.castMap = await call('picker', 'viaMap', [1n, 4n]);
      out.castAfter = await ledgers(['adder']);
      out.castActions = await actions(['adder', 'picker']);
      if (out.castMap.tx) out.castTx = await transaction(out.castMap.tx);
    }
  } finally {
    fs.mkdirSync(path.join(root, 'out'), { recursive: true });
    fs.writeFileSync(path.join(root, 'out', `calls-${mode}-result.json`), show(out, 2) + '\n');
    await wallet.stop().catch(() => {});
  }
});
