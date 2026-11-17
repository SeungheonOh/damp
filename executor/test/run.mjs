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
import { makeContract } from '../src/executor.mjs';
import { checkProofData } from '../harness/check.mjs';
import { toJson, proofDataOf } from '../harness/json.mjs';
import { witnesses, constructorArgs, calls, startState } from './calls.mjs';

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
