// The cross-contract call assumption of `--ledger-opt`, tested with real
// contracts (docs/ledger-model.md, "Calls"; Damp/Proofs/Ledger/Calls.lean).
//
// To the executor's definition (Damp/Executor/Spec.lean) a call is a witness:
// its oracle sees the call's arguments and the private state, and cannot see or
// change the caller's ledger state. `--ledger-opt` is proved under exactly that
// (Damp/Proofs/Ledger/Calls.lean, `CallIsolated`). In the executor a callee runs
// through the runtime's `crossContractCall` against its OWN query context, and
// the caller's query context is restored afterwards (executor.mjs,
// `callWitness`). This test checks the assumption on the runtime rather than
// reading it off the code.
//
// Every query any contract makes is logged (the runtime's
// `QueryContext.prototype.query` is wrapped): the address, the instructions,
// the contract state, effects and call context before and after. For every
// contract taking part in a call, its queries must thread: each starts from the
// contract state, effects and call context the previous one of the same
// contract left. The only exception
// allowed is the runtime's own claim of a call made by a Damp caller, which the
// executor undoes and the caller's circuit then makes again with the same
// instructions from the same state (docs/calls.md): a query whose successor has
// the same instructions and the same starting point is counted as undone. Any
// other discontinuity means something other than the contract's own circuit
// changed its ledger state during a call: the hole the proof assumes away.
//
// The calls (contracts of Examples/Calls.lean, built by Damp, run by Damp's
// executor; `back`, a compactc contract from test/calls-isolation.sh, which
// calls `bump` of the contract stored in its ledger):
//   1. caller.bump(5): the callee (adder) writes its own state; nothing calls back.
//   2. caller.twice(1, 2): the same callee twice.
//   3. top.go(9): nested, top -> relay -> adder (relay is caller and callee).
//   4. back.addTo(7): back (compactc) -> caller.bump (Damp, as a callee) -> adder.
//   5. caller.via(back, 4): re-entrant, caller -> back -> caller.bump. The
//      runtime refuses re-entry (`assertNoReentrancy`); the test reports what
//      happens and checks the caller's state is unchanged.
//   6. caller.via(caller, 4): a contract calling itself (refused).
//
// Usage: node test/call-isolation.mjs <dir of Damp contract.json builds> <dir of back's compactc build> [results.json]
// With a third argument, the result (or refusal) of every call and every contract's final state are
// written there (test/calls-isolation.sh compares the --O2 and --O2 --ledger-opt callers with it).

import path from 'node:path';
import fs from 'node:fs';
import * as rt from '@midnight-ntwrk/compact-runtime';
import * as ocrt from '@midnightntwrk/onchain-runtime-v4';
import { contractModule } from '../src/executor.mjs';
import { World, expectedVkOf } from './world.mjs';
import { toJson } from '../harness/json.mjs';

const [leanDir, backDir] = process.argv.slice(2).map((d) => path.resolve(d));
const COIN_PK = '3c'.repeat(32);

let failures = 0;
const report = (ok, what, detail = '') => {
  if (!ok) failures++;
  console.log(`${ok ? 'ok  ' : 'FAIL'}  ${what}${detail ? `  ${detail}` : ''}`);
};

// ---------------------------------------------------------------- the query log

// Canonical JSON of an encoded state value: map entries sorted, so that two
// encodings of one value compare equal whatever the iteration order.
function canon(x) {
  if (x instanceof Map) return { $map: [...x.entries()].map(([k, v]) => [canon(k), canon(v)]).sort((a, b) => (toJson(a, 0) < toJson(b, 0) ? -1 : 1)) };
  if (Array.isArray(x)) return x.map(canon);
  if (x instanceof Uint8Array || typeof x !== 'object' || x === null) return x;
  if (x.tag === 'map' && Array.isArray(x.content)) {
    return { tag: 'map', content: x.content.map(canon).sort((a, b) => (toJson(a, 0) < toJson(b, 0) ? -1 : 1)) };
  }
  return Object.fromEntries(Object.keys(x).sort().map((k) => [k, canon(x[k])]));
}
const sv = (v) => toJson(canon(v.encode()), 0);
function snapshot(qc) {
  const st = qc.toVmStack();
  return { state: sv(st.get(2)), effects: sv(st.get(1)), context: sv(st.get(0)) };
}

let log = [];
const realQuery = ocrt.QueryContext.prototype.query;
ocrt.QueryContext.prototype.query = function (ops, cm, gasLimit) {
  const entry = { address: this.address, ops: toJson(ops, 0), before: snapshot(this) };
  const r = realQuery.call(this, ops, cm, gasLimit);
  entry.after = snapshot(r.context);
  log.push(entry);
  return r;
};

// ---------------------------------------------------------------- the chain

const addresses = {
  adder: 'c0'.repeat(32), rich: 'c1'.repeat(32), relay: 'c2'.repeat(32),
  caller: 'c3'.repeat(32), top: 'c4'.repeat(32), back: 'c5'.repeat(32),
};
const nameAt = Object.fromEntries(Object.entries(addresses).map(([n, a]) => [a, n]));
const ref = (name) => ({ bytes: rt.encodeContractAddress(addresses[name]) });
const constructorArgs = { caller: [ref('adder'), ref('rich')], relay: [ref('adder')], top: [ref('relay')], back: [ref('caller')] };

// Stand-in verifier keys (the runtime only fingerprints them; test/conformance.mjs does the same).
const world = new World({ standInKeys: true });
const impl = {};
for (const name of ['adder', 'rich', 'relay', 'caller', 'top']) {
  const spec = JSON.parse(fs.readFileSync(path.join(leanDir, name, 'contract.json'), 'utf-8'));
  const keys = Object.fromEntries(spec.circuits.filter((k) => k.proof).map((k) => [k.name, new TextEncoder().encode(`${name}.${k.name}`)]));
  impl[name] = { mod: contractModule(spec, expectedVkOf(keys)), keys, kind: 'damp' };
}
{
  const m = await import(path.join(backDir, 'contract', 'index.js'));
  const keys = { addTo: new TextEncoder().encode('back.addTo'), clear: new TextEncoder().encode('back.clear') };
  // compactc's module with --skip-zk has no `expectedVk`: give it the stand-ins'.
  impl.back = { mod: { ...m, expectedVk: expectedVkOf(keys) }, keys, kind: 'compactc' };
}
for (const [name, it] of Object.entries(impl)) {
  it.contract = new it.mod.Contract({});
  it.init = await it.contract.initialState(rt.createConstructorContext({}, COIN_PK), ...(constructorArgs[name] ?? []));
  world.deploy(addresses[name], name, it.init.currentContractState.data, it.keys, it.mod);
}

// ---------------------------------------------------------------- the check

/**
 * Check that the queries of every contract thread, starting from its state on
 * chain. Returns { ok, perContract: {name: {queries, undone, calls}}, problems }.
 */
function threading(entries, startStates) {
  const problems = [];
  const per = {};
  const byAddr = new Map();
  entries.forEach((e, i) => { if (!byAddr.has(e.address)) byAddr.set(e.address, []); byAddr.get(e.address).push({ ...e, i }); });
  for (const [addr, qs] of byAddr) {
    const name = nameAt[addr] ?? addr;
    const info = { queries: qs.length, undone: 0, gaps: 0, gapsUnchanged: 0 };
    let cur = startStates[addr];
    for (let k = 0; k < qs.length; k++) {
      const q = qs[k];
      if (k > 0 && q.i > qs[k - 1].i + 1) {
        // Other contracts ran in between: a call. Their queries may not have changed ours.
        info.gaps++;
      }
      // The call context too (address, commitment indices, block, ...): a call may change none of
      // the caller's ledger state (`CallIsolated`, Damp/Executor/Witnesses.lean).
      const same = (a, b) => a.state === b.state && a.effects === b.effects && (a.context === undefined || b.context === undefined || a.context === b.context);
      if (cur === undefined || same(q.before, cur)) {
        if (k > 0 && q.i > qs[k - 1].i + 1) info.gapsUnchanged++;
      } else if (k > 0 && q.ops === qs[k - 1].ops && same(q.before, qs[k - 1].before) &&
                 (k < 2 || same(q.before, qs[k - 2].after))) {
        // The previous query was the runtime's own claim, undone by the executor; this is the circuit's.
        info.undone++;
      } else {
        problems.push(`${name}: query ${k} starts from ${q.before.state !== cur.state ? 'another contract state' : q.before.effects !== cur.effects ? 'other effects' : 'another call context'} than its previous query left`);
      }
      cur = q.after;
    }
    per[name] = info;
  }
  return { ok: problems.length === 0, per, problems };
}

const chainState = () => Object.fromEntries(Object.keys(addresses).filter((n) => world.state(addresses[n])).map((n) => {
  const cs = world.contractState(addresses[n]);
  // The state a fresh query context sees: the contract's data, no effects yet.
  const qc = new ocrt.QueryContext(new ocrt.ChargedState(world.state(addresses[n])), addresses[n]);
  return [addresses[n], { state: snapshot(qc).state, effects: undefined, cs }];
}));

async function call(label, name, circuit, args, expect) {
  log = [];
  const start = chainState();
  const it = impl[name];
  const ctx = world.context(addresses[name], circuit, it.init.currentPrivateState, COIN_PK);
  let run, error;
  try { run = await it.contract.circuits[circuit](ctx, ...args); } catch (e) { error = e instanceof Error ? e.message : String(e); }
  const entries = log;
  // Compare contract states only at the first query of each contract (the effects start empty
  // for a fresh query context, which the snapshot of `chainState` does not include).
  const starts = Object.fromEntries(Object.entries(start).map(([a, s]) => [a, undefined]));
  const firstOf = new Map();
  for (const e of entries) if (!firstOf.has(e.address)) firstOf.set(e.address, e);
  for (const [a, e] of firstOf) {
    if (start[a] && e.before.state !== start[a].state) report(false, `${label}: ${nameAt[a]}'s first query starts from its state on chain`);
  }
  const th = threading(entries, starts);
  const summary = Object.entries(th.per).map(([n, i]) => `${n}: ${i.queries} queries, ${i.gaps} call(s) in between (state unchanged across ${i.gapsUnchanged}), ${i.undone} undone runtime claim(s)`).join('; ');
  if (expect === 'ok') {
    report(!error, `${label}: completes`, error ?? `result ${toJson(run.result, 0)}`);
  } else {
    report(!!error, `${label}: refused`, error ? `(${error.split('\n')[0].slice(0, 160)})` : 'but it completed');
  }
  report(th.ok, `${label}: every contract's queries thread; nothing else changed its state or effects`, th.ok ? `[${summary}]` : th.problems.join('; '));
  if (run) {
    // The state each contract ends with is what its last query left.
    for (const [a, qc] of Object.entries(run.context.queryContexts)) {
      const qs = entries.filter((e) => e.address === a);
      if (qs.length === 0) continue;
      const fin = snapshot(qc);
      report(fin.state === qs.at(-1).after.state && fin.effects === qs.at(-1).after.effects,
        `${label}: ${nameAt[a]} ends with the state and effects its last query left`);
    }
    world.commit(run);
  } else {
    // Nothing of a failed call survives.
    for (const [a, s] of Object.entries(start)) {
      const qc = new ocrt.QueryContext(new ocrt.ChargedState(world.state(a)), a);
      report(snapshot(qc).state === s.state, `${label}: ${nameAt[a]}'s state on chain unchanged`);
    }
  }
  return { run, error, entries, th };
}

const show = (n) => {
  const qc = new ocrt.QueryContext(new ocrt.ChargedState(world.state(addresses[n])), addresses[n]);
  return impl[n].mod.ledger ? toJson(impl[n].mod.ledger(world.state(addresses[n])), 0) : snapshot(qc).state;
};

const r1 = await call('caller.bump(5)', 'caller', 'bump', [5n], 'ok');
report(r1.entries.some((e) => nameAt[e.address] === 'adder'), 'caller.bump(5): the callee wrote its own state', `adder now ${show('adder')}`);
const r2 = await call('caller.twice(1, 2)', 'caller', 'twice', [1n, 2n], 'ok');
const r3 = await call('top.go(9)', 'top', 'go', [9n], 'ok');
const r4 = await call('back.addTo(7)', 'back', 'addTo', [7n], 'ok');
report(r4.th.per.caller?.queries > 0, 'back.addTo(7): caller.bump ran as a callee (Damp executor between two calls)', `caller now ${show('caller')}`);
const before = show('caller');
const r5 = await call('caller.via(back, 4) [re-entrant: caller -> back -> caller]', 'caller', 'via', [ref('back'), 4n], 'refused');
report(/re-entrancy/i.test(r5.error ?? ''), 're-entry is refused by the runtime\'s guard, before the inner caller.bump runs',
  r5.entries.filter((e) => nameAt[e.address] === 'caller').length + ' caller queries');
report(show('caller') === before, 'the caller\'s ledger state is unchanged after the refused re-entrant call');
// The check has teeth: in the log of caller.bump(5), let the callee's run have
// changed the caller's state (the caller's first query after the call starts
// from another state), and the threading check must say so.
{
  const forged = r1.entries.map((e) => ({ ...e }));
  const firstAfter = forged.findIndex((e, i) => nameAt[e.address] === 'caller' && i > 0 && nameAt[forged[i - 1].address] !== 'caller');
  forged[firstAfter] = { ...forged[firstAfter], before: { ...forged[firstAfter].before, state: forged[firstAfter].before.state + ' ' } };
  report(!threading(forged, {}).ok, 'the check detects a caller state changed during a call (forged log)');
}
// The same with the caller's call context changed during the call (the check compares it too).
{
  const forged = r1.entries.map((e) => ({ ...e }));
  const firstAfter = forged.findIndex((e, i) => nameAt[e.address] === 'caller' && i > 0 && nameAt[forged[i - 1].address] !== 'caller');
  forged[firstAfter] = { ...forged[firstAfter], before: { ...forged[firstAfter].before, context: forged[firstAfter].before.context + ' ' } };
  report(!threading(forged, {}).ok, 'the check detects a caller call context changed during a call (forged log)');
}
const r6 = await call('caller.via(caller, 4) [self-call]', 'caller', 'via', [ref('caller'), 4n], 'refused');
if (process.argv[4]) {
  const res = (r) => (r.error ? 'refused' : toJson(r.run.result, 0));
  const states = Object.fromEntries(Object.keys(addresses).filter((n) => world.state(addresses[n])).map((n) => [n, show(n)]));
  fs.writeFileSync(process.argv[4], JSON.stringify({ bump: res(r1), twice: res(r2), go: res(r3), addTo: res(r4), via: res(r5),
    self: res(r6), states }));
}

console.log(failures === 0 ? 'ALL PASS' : `${failures} FAILED`);
process.exit(failures === 0 ? 0 : 1);
