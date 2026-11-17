// Thin adapter: makes a Damp build (contract.json + zkir/ + keys/) look like
// the compactc output directory and contract module that midnight-js 5 expects.
//
// What it does, and why (see DEPLOY-NOTES.md for the evidence):
//
//  1. Copies the Damp executor (executor/src/executor.mjs, verbatim) next to
//     the bundle, so its `import '@midnight-ntwrk/compact-runtime'` resolves
//     to the SAME copy midnight-js uses (deploy/node_modules). midnight-js
//     crosses the WASM boundary with objects the contract returns
//     (ContractState.operation/setOperation, maintenanceAuthority setter), so
//     two runtime copies would fail with "expected instance of ...".
//  2. Lays out the asset directory the zk-config provider reads:
//       keys/<c>.prover, keys/<c>.verifier, zkir/<c>.bzkir,
//       compiler/contract-info.json        (declares runtime-version 0.21.0)
//       compiler/contract-manifest.json    (sha-256 of every file; required by
//                                           NodeZkConfigProvider's default
//                                           integrity mode 'require')
//  3. Exposes `Contract`, a class whose instances are `makeContract(spec, witnesses)`,
//     i.e. { witnesses, circuits, impureCircuits, provableCircuits, initialState },
//     plus `ledger(state)` decoded generically from contract.json.
//  4. Optionally records every property midnight-js reads off the class and
//     the instance (DAMP_TRACE=0 to turn off).

import crypto from 'node:crypto';
import fs from 'node:fs';
import path from 'node:path';
import { pathToFileURL } from 'node:url';

const EXECUTOR_SRC = process.env.DAMP_EXECUTOR ??
  new URL('../../executor/src/executor.mjs', import.meta.url).pathname;
const RUNTIME_VERSION = '0.21.0'; // the compact-runtime the executor is written against

const sha256 = (bytes) => crypto.createHash('sha256').update(bytes).digest('hex');

function copyDir(from, to) {
  fs.mkdirSync(to, { recursive: true });
  for (const f of fs.readdirSync(from)) fs.copyFileSync(path.join(from, f), path.join(to, f));
}

/** Build the bundle directory `out` from Damp's output directory `src`. */
export async function prepareDampBundle(src, out, { mutate } = {}) {
  fs.rmSync(out, { recursive: true, force: true });
  copyDir(path.join(src, 'keys'), path.join(out, 'keys'));
  copyDir(path.join(src, 'zkir'), path.join(out, 'zkir'));
  fs.mkdirSync(path.join(out, 'contract'), { recursive: true });
  fs.copyFileSync(path.join(src, 'contract.json'), path.join(out, 'contract', 'contract.json'));
  fs.copyFileSync(EXECUTOR_SRC, path.join(out, 'contract', 'executor.mjs'));
  if (mutate) mutate(out);
  const spec = JSON.parse(fs.readFileSync(path.join(out, 'contract', 'contract.json'), 'utf-8'));

  // compiler/contract-info.json: only `runtime-version` is read by midnight-js
  // (to place the artifacts on a ledger era); the rest mirrors compactc's.
  fs.mkdirSync(path.join(out, 'compiler'), { recursive: true });
  const info = {
    'compiler-version': 'damp',
    'language-version': '0.28.0',
    'runtime-version': RUNTIME_VERSION,
    circuits: spec.circuits.map((c) => ({ name: c.name, pure: !c.proof, proof: !!c.proof })),
  };
  fs.writeFileSync(path.join(out, 'compiler', 'contract-info.json'), JSON.stringify(info, null, 2) + '\n');

  // compiler/contract-manifest.json, in compactc's format (manifest-version 1).
  const manifest = {
    'manifest-version': '1',
    'compiler-version': 'damp',
    'language-version': '0.28.0',
    'runtime-version': RUNTIME_VERSION,
  };
  for (const d of ['compiler', 'contract', 'zkir', 'keys']) {
    manifest[d] = { type: 'directory' };
    for (const f of fs.readdirSync(path.join(out, d)).sort()) {
      const bytes = fs.readFileSync(path.join(out, d, f));
      manifest[d][f] = { type: 'file', size: bytes.length, hash: sha256(bytes) };
    }
  }
  fs.writeFileSync(path.join(out, 'compiler', 'contract-manifest.json'), JSON.stringify(manifest, null, 2) + '\n');

  const { makeContract } = await import(pathToFileURL(path.join(out, 'contract', 'executor.mjs')).href);
  const rt = await import('@midnight-ntwrk/compact-runtime');

  const touched = process.env.DAMP_TRACE === '0' ? undefined : new Set();
  const trace = (prefix, obj) => (touched === undefined ? obj : new Proxy(obj, {
    get(t, k, r) { if (typeof k === 'string') touched.add(`${prefix}.${k}`); return Reflect.get(t, k, r); },
    has(t, k) { if (typeof k === 'string') touched.add(`${prefix}.${k} (in)`); return Reflect.has(t, k); },
    ownKeys(t) { touched.add(`${prefix} (keys)`); return Reflect.ownKeys(t); },
    getOwnPropertyDescriptor(t, k) { if (typeof k === 'string') touched.add(`${prefix}.${k} (own)`); return Reflect.getOwnPropertyDescriptor(t, k); },
  }));

  class Contract {
    constructor(witnesses = {}) {
      const c = makeContract(spec, witnesses);
      for (const k of ['impureCircuits', 'provableCircuits', 'circuits']) c[k] = trace(`instance.${k}`, c[k]);
      return trace('instance', c);
    }
  }
  const TracedContract = touched === undefined ? Contract : new Proxy(Contract, {
    construct(t, args, nt) { touched.add('Contract (new)'); return Reflect.construct(t, args, nt); },
    get(t, k, r) { if (typeof k === 'string') touched.add(`Contract.${k}`); return Reflect.get(t, k, r); },
  });

  /** The public ledger as a plain object, decoded from contract.json's ledger layout. */
  function ledger(stateIn) {
    const sv = stateIn instanceof rt.ChargedState ? stateIn.state : stateIn;
    const slots = sv.asArray();
    const out = {};
    for (const f of spec.ledger) {
      const slot = slots[f.index];
      switch (f.type.kind) {
        case 'counter': out[f.name] = rt.valueToBigInt(slot.asCell().value); break;
        case 'cell': {
          const s = f.type.shape;
          const v = slot.asCell().value;
          if (s.kind === 'field' || s.kind === 'uint') out[f.name] = rt.valueToBigInt(v);
          else if (s.kind === 'bool') out[f.name] = rt.valueToBigInt(v) === 1n;
          else if (s.kind === 'bytes') out[f.name] = new rt.CompactTypeBytes(s.length).fromValue([...v]);
          else out[f.name] = slot.asCell(); // composite cells: raw AlignedValue
          break;
        }
        default: out[f.name] = slot; // map / set: raw StateValue
      }
    }
    return out;
  }

  return { dir: out, Contract: TracedContract, ledger, touched, spec };
}
