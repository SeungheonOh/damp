// Executor tests. For each example contract, run the same calls through
//   (a) the generic executor on the Lean compiler's contract.json, and
//   (b) the module compactc generated from the equivalent Compact source,
// then require that
//   1. both produce identical proof data and results,
//   2. Midnight's ZKIR checker accepts the executor's proof data against the
//      circuit the Lean compiler emitted, and
//   3. the checker rejects it once the claimed output is tampered with.
//
// Usage: node test/run.mjs <oracle build dir>   (default ../build/oracle; see test/oracle.sh)

import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import * as rt from '@midnight-ntwrk/compact-runtime';
import { makeContract, contractModule } from '../src/executor.mjs';
import { packageContract } from '../src/package.mjs';
import { checkProofData } from '../harness/check.mjs';
import { toJson, proofDataOf } from '../harness/json.mjs';
import { witnesses, constructorArgs, calls, startState, addresses, strangers } from './calls.mjs';
import { World, verifierKeys, expectedVkOf, normalizeTrace, directoryModuleProvider } from './world.mjs';

/** Contracts that call or are called by others run in a simulated chain (below). */
const inWorld = (name) => Object.hasOwn(addresses, name);

const here = path.dirname(fileURLToPath(import.meta.url));
const root = path.resolve(process.argv[2] ?? path.join(here, '..', '..', 'build', 'oracle'));
const COIN_PK = '3c'.repeat(32);   // the user's coin public key (what ownPublicKey returns)

let failures = 0;
const report = (ok, label, detail = '') => {
  if (!ok) failures++;
  console.log(`${ok ? 'ok   ' : 'FAIL '} ${label}${detail ? '  ' + detail : ''}`);
};

// Calls on a contract are chained: each starts from the ledger state the previous one left.
const circuitContext = (circuitId, init, state, name) =>
  rt.createCircuitContext({
    circuitId,
    contractAddress: rt.dummyContractAddress(),
    coinPublicKeyOrZswapState: init.currentZswapLocalState.coinPublicKey,
    contractState: startState(name, state ?? init.currentContractState),
    privateState: init.currentPrivateState,
    time: 0,
  });
const stateAfter = (run) => run.context.callContext.currentQueryContext.state;
const show = (x) => toJson(x, 0);

const attempt = async (f) => {
  try { return { value: await f() }; } catch (e) { return { error: e instanceof Error ? e.message : String(e) }; }
};

const loaded = new Map();
async function load(name) {
  if (!loaded.has(name)) {
    const leanDir = path.join(root, 'lean', name);
    const spec = JSON.parse(await fs.readFile(path.join(leanDir, 'contract.json'), 'utf-8'));
    const mine = makeContract(spec, witnesses);
    const mod = await import(path.join(root, 'compact', name, 'contract', 'index.js'));
    const theirs = new mod.Contract(witnesses);
    const cctx = () => rt.createConstructorContext({}, COIN_PK);
    const ctorArgs = constructorArgs[name] ?? [];
    const mineInit = await mine.initialState(cctx(), ...ctorArgs);
    const theirsInit = await theirs.initialState(cctx(), ...ctorArgs);
    const enc = (i) => toJson(i.currentContractState.data.state.encode(), 0);
    report(enc(mineInit) === enc(theirsInit), `${name}: initial ledger state equals compactc's`);
    const entry = { leanDir, mod, mine, theirs, mineInit, theirsInit };
    // Merkle roots for the call table, read through compactc's `ledger()`.
    const theirLedger = () => mod.ledger(entry.theirsState ?? theirsInit.currentContractState.data);
    entry.rootOf = (field) => theirLedger()[field].root();
    entry.rootIn = (field, k) => theirLedger()[field].lookup(k).root();
    loaded.set(name, entry);
  }
  return loaded.get(name);
}

for (const [name, circuit, argsOf, shouldSucceed] of calls) {
  if (inWorld(name)) continue;
  const c = await load(name);
  const args = typeof argsOf === 'function' ? argsOf(c) : argsOf;
  const label = `${name}.${circuit}(${args.map(show).join(', ')})`.replaceAll('"', '');
  const mine = await attempt(() => c.mine.circuits[circuit](circuitContext(circuit, c.mineInit, c.mineState, name), ...args));
  const theirs = await attempt(() => c.theirs.circuits[circuit](circuitContext(circuit, c.theirsInit, c.theirsState, name), ...args));
  const proved = c.mine.spec.circuits.find((x) => x.name === circuit).proof;

  if (!shouldSucceed) {
    report(!!mine.error && !!theirs.error, `${label}: both fail`, `[${mine.error ?? 'executor succeeded'}]`);
    continue;
  }
  if (mine.error || theirs.error) {
    report(false, `${label}: runs`, mine.error ?? theirs.error);
    continue;
  }
  if (!proved) {
    // Never touches the ledger: no circuit to check against, only the result to compare.
    report(toJson(mine.value.result, 0) === toJson(theirs.value.result, 0), `${label}: result equals compactc's (no proof needed)`);
    continue;
  }
  c.mineState = stateAfter(mine.value);
  c.theirsState = stateAfter(theirs.value);
  const mineData = proofDataOf(mine.value.context.callProofDataTrace.at(-1));
  const theirsData = proofDataOf(theirs.value.context.callProofDataTrace.at(-1));
  report(toJson(mineData, 0) === toJson(theirsData, 0), `${label}: proof data equals compactc's`);
  report(toJson(mine.value.result, 0) === toJson(theirs.value.result, 0), `${label}: result equals compactc's`, `= ${toJson(mine.value.result, 0)}`);
  {
    // The coins the call asked the runtime to add to the transaction.
    const zswap = (r) => toJson(r.value.context.callContext.currentZswapLocalState, 0);
    const z = mine.value.context.callContext.currentZswapLocalState;
    report(zswap(mine) === zswap(theirs), `${label}: Zswap local state equals compactc's`,
      `(${z.inputs.length} input(s), ${z.outputs.length} output(s))`);
  }

  const checked = await checkProofData({ compiledDir: c.leanDir, circuitId: circuit, proofData: mineData });
  report(checked.ok, `${label}: ZKIR check accepts`, checked.ok ? '' : `${checked.stage}: ${checked.error}`);

  const tampered = structuredClone(mineData);
  // Change the lowest byte of one recorded value, keeping the encoding canonical:
  // the output if there is one, otherwise the first witness result that has a
  // value, otherwise the first input.
  const target = [tampered.output, ...tampered.privateTranscriptOutputs, tampered.input]
    .find((t) => t.value.length > 0);
  // A call with no arguments, no witness values and no result (e.g. writing a
  // constant) has nothing private to tamper with.
  if (!target) continue;
  const atom = Uint8Array.from(target.value[0].length ? target.value[0] : [0]);
  atom[0] = atom[0] === 255 ? 254 : atom[0] + 1;
  target.value[0] = atom;
  const rejected = await checkProofData({ compiledDir: c.leanDir, circuitId: circuit, proofData: tampered });
  report(!rejected.ok, `${label}: ZKIR check rejects a tampered value`);
}

// The decoded view of the final ledger state must read the same as compactc's.
for (const [name, c] of loaded) {
  if (!c.mineState) continue;
  const mine = c.mine.ledger(c.mineState);
  const theirs = c.mod.ledger(c.theirsState);
  for (const f of c.mine.spec.ledger) {
    const kind = f.type.kind;
    if (kind === 'cell' || kind === 'counter') {
      report(show(mine[f.name]) === show(theirs[f.name]), `${name}: ledger view of ${f.name} equals compactc's`, `= ${show(mine[f.name])}`);
    } else if (kind === 'map' || kind === 'set') {
      const entries = (v) => show([...v].map((e) => show(e)).sort());
      report(mine[f.name].size() === theirs[f.name].size() && entries(mine[f.name]) === entries(theirs[f.name]),
        `${name}: ledger view of ${f.name} equals compactc's`, `(${mine[f.name].size()} entries)`);
    }
  }
}

// ---------------------------------------------------------------- cross-contract calls
//
// The contracts of `addresses` are deployed in four simulated chains (world.mjs)
// that differ only in which implementation each address runs:
//   damp      every contract is the Damp build (the executor, `contractModule`);
//   compactc  every contract is compactc's generated module;
//   mixed     caller and top are Damp, their callees (adder, rich, relay) compactc's;
//   packaged  caller and top are compactc's, their callees Damp contracts packaged
//             by package.mjs and loaded, as compactc's documentation describes,
//             from `<root>/<T>/contract/index.js`.
// Each chain deploys with the verifier keys of the implementation it runs. Every
// call is made in every chain; the proof data of the call and of every call
// nested in it (the whole `callProofDataTrace`), the result, the Zswap local
// states and, at the end, the ledger state of every contract must be the same in
// all four, up to the commitments' random openings (`normalizeTrace`); every
// proof data entry, Damp's and compactc's, must be accepted by the ZKIR checker
// against the Damp circuit of its contract.

const worldCalls = calls.filter(([name]) => inWorld(name));
if (worldCalls.length > 0) {
  const names = Object.keys(addresses);
  const specs = {}, compactMods = {}, dampMods = {}, dampKeys = {}, compactKeys = {};
  const pkgRoot = path.join(root, 'pkg');
  for (const n of names) {
    const leanDir = path.join(root, 'lean', n);
    specs[n] = JSON.parse(await fs.readFile(path.join(leanDir, 'contract.json'), 'utf-8'));
    compactMods[n] = await import(path.join(root, 'compact', n, 'contract', 'index.js'));
    dampKeys[n] = verifierKeys(leanDir);
    compactKeys[n] = verifierKeys(path.join(root, 'compact', n));
    dampMods[n] = contractModule(specs[n], expectedVkOf(dampKeys[n]));
    packageContract(leanDir, path.join(pkgRoot, n));
  }
  const nameAt = Object.fromEntries(names.map((n) => [addresses[n], n]));
  const entry = (n) => n === 'caller' || n === 'top' || n === 'picker';
  const setups = [
    ['damp', () => 'damp'],
    ['compactc', () => 'compactc'],
    ['mixed', (n) => (entry(n) ? 'damp' : 'compactc')],
    ['packaged', (n) => (entry(n) ? 'compactc' : 'damp')],
  ];
  const worlds = [];
  for (const [label, kindOf] of setups) {
    const w = new World();
    const impl = {};
    for (const n of names) {
      const kind = kindOf(n);
      const mod = kind === 'damp' ? dampMods[n] : compactMods[n];
      const contract = new mod.Contract(witnesses);
      const init = await contract.initialState(rt.createConstructorContext({}, COIN_PK), ...(constructorArgs[n] ?? []));
      w.deploy(addresses[n], n, init.currentContractState.data, kind === 'damp' ? dampKeys[n] : compactKeys[n], mod);
      impl[n] = { contract, init, kind };
    }
    for (const s of Object.values(strangers)) {
      if (!s.like) continue;
      const base = w.contracts.get(addresses[s.like]);
      w.deploy(s.address, s.like, base.data, s.keys ? s.keys(base.keys) : base.keys, s.bound ? (s.wrap ? s.wrap(base.module) : base.module) : undefined);
      if (s.bound) nameAt[s.address] = s.like;
    }
    if (label === 'packaged') {
      // A stranger with a doctored module (`wrap`) has no package of its own: the directory provider
      // finds no implementation for it, so calls to it fail in this chain for that reason.
      const doctored = new Set(Object.values(strangers).filter((s) => s.wrap).map((s) => s.address));
      const bound = Object.fromEntries([...w.contracts].filter(([a, c]) => c.module !== undefined && !doctored.has(a))
        .map(([a, c]) => [a, c.name]));
      w.provider = directoryModuleProvider(pkgRoot, bound);
    }
    worlds.push({ label, w, impl });
  }
  const [damp, compactc] = worlds;
  for (const n of names) {
    const enc = (W) => toJson(W.w.state(addresses[n]).encode(), 0);
    report(worlds.every((W) => enc(W) === enc(compactc)), `${n}: initial ledger state equals compactc's in every chain`);
  }

  let proved = false;
  for (const [name, circuit, argsOf, shouldSucceed, opts] of worldCalls) {
    // An argument list may depend on the implementation called ('damp' or 'compactc').
    const argsIn = (kind) => (typeof argsOf === 'function' ? argsOf(kind) : argsOf);
    const label = `${name}.${circuit}(${argsIn('damp').map(show).join(', ')})`.replaceAll('"', '');
    const runs = [];
    for (const W of worlds) {
      const { contract, init, kind } = W.impl[name];
      const args = argsIn(kind);
      const ctx = W.w.context(addresses[name], circuit, init.currentPrivateState, init.currentZswapLocalState.coinPublicKey);
      runs.push(await attempt(() => contract.circuits[circuit](ctx, ...args)));
    }
    if (!shouldSucceed && opts?.dampCallerOnly) {
      // A check only Damp's executor makes (compactc's generated caller takes the callee's result as
      // it comes): every chain whose caller is Damp's must refuse; compactc's outcome is shown.
      const mine = runs.filter((_, i) => worlds[i].impl[name].kind === 'damp');
      report(mine.length > 0 && mine.every((r) => r.error), `${label}: fails in every chain whose ${name} is Damp's`,
        `[${runs.map((r, i) => `${worlds[i].label}: ${r.error ?? 'succeeded'}`).join(' | ')}]`);
      continue;
    }
    if (!shouldSucceed) {
      report(runs.every((r) => r.error), `${label}: fails in every chain`,
        `[${runs.map((r, i) => `${worlds[i].label}: ${r.error ?? 'succeeded'}`).join(' | ')}]`);
      continue;
    }
    const failed = runs.findIndex((r) => r.error);
    if (failed >= 0) {
      report(false, `${label}: runs`, `${worlds[failed].label}: ${runs[failed].error}`);
      continue;
    }
    const traces = runs.map((r) => r.value.context.callProofDataTrace);
    const norms = traces.map(normalizeTrace);
    const n = traces[0].length;
    for (const [i, W] of worlds.entries()) {
      report(norms[i].problems.length === 0, `${label} [${W.label}]: openings and commitments check`, norms[i].problems.join('; '));
      if (W === compactc) continue;
      report(toJson(norms[i].entries, 0) === toJson(norms[1].entries, 0),
        `${label} [${W.label}]: proof data of all ${n} call(s) equals compactc's`,
        traces[i].map((e) => `${nameAt[e.contractAddress] ?? e.contractAddress}.${e.circuitId}`).join(' <- '));
      report(toJson(runs[i].value.result, 0) === toJson(runs[1].value.result, 0),
        `${label} [${W.label}]: result equals compactc's`, `= ${toJson(runs[i].value.result, 0)}`);
      report(toJson(runs[i].value.context.zswapLocalStates, 0) === toJson(runs[1].value.context.zswapLocalStates, 0),
        `${label} [${W.label}]: Zswap local states equal compactc's`);
    }
    // Every entry, Damp's and compactc's, against the Damp circuit of its contract.
    for (const W of [damp, compactc]) {
      for (const e of W === damp ? traces[0] : traces[1]) {
        const cn = nameAt[e.contractAddress];
        const checked = await checkProofData({
          compiledDir: path.join(root, 'lean', cn), circuitId: e.circuitId, proofData: proofDataOf(e), prove: !proved && W === damp && cn === 'caller',
        });
        report(checked.ok, `${label} [${W.label}]: ZKIR check of ${cn}.${e.circuitId} accepts`
          + (checked.proof ? ` (and a real proof: ${checked.proof.length} bytes)` : ''), checked.ok ? '' : `${checked.stage}: ${checked.error}`);
        if (checked.proof) proved = true;
      }
    }
    const top = structuredClone(proofDataOf(traces[0].at(-1)));
    const target = [top.output, ...top.privateTranscriptOutputs, top.input].find((t) => t.value.length > 0);
    if (target) {
      const atom = Uint8Array.from(target.value[0].length ? target.value[0] : [0]);
      atom[0] = atom[0] === 255 ? 254 : atom[0] + 1;
      target.value[0] = atom;
      const rejected = await checkProofData({ compiledDir: path.join(root, 'lean', name), circuitId: circuit, proofData: top });
      report(!rejected.ok, `${label}: ZKIR check rejects a tampered value`);
    }
    for (const [i, W] of worlds.entries()) W.w.commit(runs[i].value);
  }
  for (const n of names) {
    const enc = (W) => toJson(W.w.state(addresses[n]).encode(), 0);
    report(worlds.every((W) => enc(W) === enc(compactc)), `${n}: final ledger state equals compactc's in every chain`);
    const mine = dampMods[n].ledger(damp.w.state(addresses[n]));
    const theirs = compactMods[n].ledger(compactc.w.state(addresses[n]));
    for (const f of specs[n].ledger) {
      if (f.type.kind !== 'cell' && f.type.kind !== 'counter') continue;
      report(show(mine[f.name]) === show(theirs[f.name]), `${n}: ledger view of ${f.name} equals compactc's`, `= ${show(mine[f.name])}`);
    }
  }
}

// One real proof, to exercise the prover key generated from the Lean-emitted circuit.
{
  const c = await load('counter');
  const run = await c.mine.circuits.bump(circuitContext('bump', c.mineInit), 12n, true, false);
  const proved = await checkProofData({
    compiledDir: c.leanDir, circuitId: 'bump',
    proofData: proofDataOf(run.context.callProofDataTrace.at(-1)), prove: true,
  });
  report(proved.ok && !!proved.proof, 'counter.bump: real proof generated', proved.ok ? `${proved.proof.length} bytes` : `${proved.stage}: ${proved.error}`);
}

console.log(failures === 0 ? '\nall executor checks passed' : `\n${failures} check(s) failed`);
process.exit(failures === 0 ? 0 : 1);
