// A simulated chain for cross-contract calls (docs/calls.md), shared by
// test/run.mjs and test/conformance.mjs.
//
// Contracts are deployed at fixed addresses with their ledger state and the
// verifier key of every provable circuit (as on chain: the runtime's
// verifier-key guard compares their fingerprints with the module's
// `expectedVk`), and each address is bound to the module implementing it:
// compactc's generated module, or a Damp contract's (the executor's
// `contractModule`, or a directory packaged by package.mjs). A call runs with
// the world's `stateProvider` and `moduleProvider`, as midnight-js supplies
// them; afterwards `commit` installs the final state of every contract the
// call touched, as the transaction would.

import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import * as rt from '@midnight-ntwrk/compact-runtime';

/** The block every call is made against (the runtime requires one for a cross-contract call). */
export const PARENT_BLOCK = '11'.repeat(32);

export const sha256 = (bytes) => crypto.createHash('sha256').update(bytes).digest('hex');

/** The verifier keys under `<dir>/keys`, by circuit. */
export function verifierKeys(dir) {
  const keys = {};
  const kdir = path.join(dir, 'keys');
  if (!fs.existsSync(kdir)) return keys;
  for (const f of fs.readdirSync(kdir)) {
    if (f.endsWith('.verifier')) keys[f.slice(0, -'.verifier'.length)] = new Uint8Array(fs.readFileSync(path.join(kdir, f)));
  }
  return keys;
}

/** `expectedVk` for verifier keys, as compactc writes it. */
export const expectedVkOf = (keys) => Object.fromEntries(Object.entries(keys).map(([c, k]) => [c, sha256(k)]));

/**
 * A module provider in compactc's documented convention: the code of contract
 * `T` is `<root>/T/contract/index.js`. `names` maps each address to `T`.
 */
export function directoryModuleProvider(root, names) {
  return {
    resolve: (address) => {
      const name = names[address];
      if (name === undefined) return undefined;
      return () => import(path.join(root, name, 'contract', 'index.js'));
    },
  };
}

const stateValueOf = (s) => (s instanceof rt.StateValue ? s : s instanceof rt.ChargedState ? s.state : s.data.state);

export class World {
  /**
   * With `standInKeys`, the keys given to `deploy` may be any bytes: the
   * contract state served answers `operation(circuit)` with them itself
   * (test/conformance.mjs, which has no real keys; the runtime only takes the
   * key's fingerprint). Otherwise they must be real verifier keys.
   */
  constructor({ standInKeys = false } = {}) {
    this.standInKeys = standInKeys;
    /** address -> { name, data (StateValue), keys, module } */
    this.contracts = new Map();
    /** A module provider used instead of the bound modules, if set. */
    this.provider = undefined;
  }

  /** Deploy `name` at `address` with ledger state `state`, verifier keys `keys` and module `module` (may be undefined). */
  deploy(address, name, state, keys, module) {
    this.contracts.set(address, { name, data: stateValueOf(state), keys, module });
  }

  /** The contract state at `address` as the chain holds it: ledger data, and an operation per verifier key. */
  contractState(address) {
    const c = this.contracts.get(address);
    if (!c) return undefined;
    const cs = new rt.ContractState();
    cs.data = new rt.ChargedState(c.data);
    if (this.standInKeys) {
      return Object.create(cs, {
        operation: { value: (circuit) => (Object.hasOwn(c.keys, circuit) ? { verifierKey: c.keys[circuit] } : undefined) },
      });
    }
    for (const [circuit, key] of Object.entries(c.keys)) {
      const op = new rt.ContractOperation();
      op.verifierKey = key;
      cs.setOperation(circuit, op);
    }
    return cs;
  }

  get stateProvider() {
    return { getContractState: async (_block, address) => this.contractState(address) };
  }

  get moduleProvider() {
    if (this.provider) return this.provider;
    return {
      resolve: (address) => {
        const m = this.contracts.get(address)?.module;
        return m === undefined ? undefined : async () => m;
      },
    };
  }

  /** A circuit context for calling `circuitId` of the contract at `address`. */
  context(address, circuitId, privateState, coinPublicKey) {
    return rt.createCircuitContext({
      circuitId,
      contractAddress: address,
      coinPublicKeyOrZswapState: coinPublicKey,
      contractState: this.contractState(address),
      privateState,
      time: 0,
      parentBlockHash: PARENT_BLOCK,
      crossContract: { stateProvider: this.stateProvider, moduleProvider: this.moduleProvider },
    });
  }

  /** Install the final state of every contract a completed call touched. */
  commit(run) {
    for (const [address, qc] of Object.entries(run.context.queryContexts)) {
      const c = this.contracts.get(address);
      if (c) c.data = qc.state.state;
    }
  }

  state(address) {
    return this.contracts.get(address)?.data;
  }
}

// ---------------------------------------------------------------- comparing calls whose opening is random

/**
 * The proof data of a call and of every call nested in it
 * (`context.callProofDataTrace`, callees first), made comparable across runs:
 * each communication commitment's random opening (sampled by the runtime, so
 * different in every run) and the commitment derived from it are checked and
 * then replaced by placeholders. Checked: the commitment the caller claims
 * (the last field of the `push` before `concat cached 160`) is
 * `communicationCommitment(callee input, callee output, opening)`, the opening
 * being the caller's private output right after the callee's output, and the
 * callee's entry carries the same pair (`commCommData`). Returns
 * `{ entries, problems }`.
 */
export function normalizeTrace(trace) {
  const problems = [];
  const entries = trace.map((e) => ({
    circuitId: e.circuitId, contractAddress: e.contractAddress,
    input: e.input, output: e.output,
    publicTranscript: e.publicTranscript.map((op) => op),
    privateTranscriptOutputs: e.privateTranscriptOutputs.map((v) => v),
  }));
  // Each callee entry precedes its caller's; a caller's claims are in its
  // public transcript in call order, as are its callees' entries among the
  // entries before it that it called directly.
  const used = new Set();
  trace.forEach((caller, ci) => {
    const pt = caller.publicTranscript;
    const claims = [];
    pt.forEach((op, i) => {
      if (typeof op === 'object' && op.concat && op.concat.cached && op.concat.n === 160) claims.push(i - 1);
    });
    // The callees of this entry: the most recent unused entries before it, in order.
    const callees = [];
    for (let j = ci - 1; j >= 0 && callees.length < claims.length; j--) {
      if (!used.has(j) && trace[j].commCommData) callees.unshift(j);
    }
    let priv = 0;
    claims.forEach((pi, k) => {
      const callee = trace[callees[k]];
      if (!callee) { problems.push(`${caller.circuitId}: claim ${k} has no callee entry`); return; }
      used.add(callees[k]);
      // The opening follows the callee's output among the caller's private outputs.
      const outs = caller.privateTranscriptOutputs;
      const at = outs.findIndex((v, i) => i >= priv && i + 1 < outs.length &&
        key(v) === key(callee.output) && key(outs[i + 1]) === key(randAligned(callee.commCommData.commCommRand)));
      if (at < 0) { problems.push(`${caller.circuitId}: claim ${k}: the callee's output and opening are not among the private outputs`); return; }
      priv = at + 2;
      const comm = rt.communicationCommitment(callee.input, callee.output, callee.commCommData.commCommRand);
      if (comm !== callee.commCommData.commComm) problems.push(`${caller.circuitId}: claim ${k}: commitment is not that of the callee's input, output and opening`);
      const push = pt[pi].push;
      const cell = rt.StateValue.decode(push.value).asCell();
      if (key(cell.value.at(-1)) !== key(randAligned(comm).value[0])) {
        problems.push(`${caller.circuitId}: claim ${k}: the claimed commitment is not the callee's`);
      }
      // Placeholders.
      entries[ci].privateTranscriptOutputs[at + 1] = '<opening>';
      const placeholder = { ...cell, value: [...cell.value.slice(0, -1), '<commitment>'] };
      entries[ci].publicTranscript[pi] = { push: { storage: push.storage, value: placeholder } };
    });
  });
  return { entries, problems };
}

/** The AlignedValue of a hex-encoded `Fr`, as the runtime records an opening. */
function randAligned(frHex) {
  const all = Buffer.from(frHex, 'hex').slice(1);
  let end = all.length;
  while (end > 0 && all[end - 1] === 0) end--;
  return { value: [new Uint8Array(all.slice(0, end))], alignment: [{ tag: 'atom', value: { tag: 'field' } }] };
}

// Byte strings by content: the runtime hands out some as Buffers, whose
// `toJSON` would otherwise run before the replacer sees them.
function key(x) {
  return JSON.stringify(x, function (k, v) {
    const raw = this[k];
    return raw instanceof Uint8Array ? Buffer.from(raw).toString('hex') : typeof v === 'bigint' ? `${v}n` : v;
  });
}
