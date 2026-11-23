// Differential test of the opt-in ledger passes (`--ledger-opt`: `Circuit.ledgerReuse`, then
// `Circuit.ledgerDeadStore`; Damp/Optimize/LedgerReuse.lean, LedgerDeadStore.lean)
// through the real runtime. The same calls as test/bench.mjs (values, witnesses and calls copied from
// it; zerocash_core is left out: its calls need compactc's module for Merkle paths, and the pass does
// not change it) are made against two Damp builds of each benchmark program:
//   o2: `lake exe damp-bench --O2`, and
//   lo: `lake exe damp-bench --O2 --ledger-opt`,
// each starting from the ledger state its own previous call left. For every call it requires that
// both succeed or both fail, and, when they succeed, that
//   1. the results are identical,
//   2. the ledger state afterwards (its encoding) and the Zswap local state are identical,
//   3. the private transcript is identical (the public transcript is NOT compared: the pass sends
//      fewer ledger programs, which is the point),
//   4. Midnight's ZKIR checker accepts the `lo` proof data against the `lo` circuit.
// It also reports the gas the runtime charged each build (`gasCost` of the call), summed over the
// calls of the circuits the pass changed.
//
// Usage: node test/ledger-opt.mjs <dir holding o2/ and lo/>

import fs from 'node:fs/promises';
import path from 'node:path';
import * as rt from '@midnight-ntwrk/compact-runtime';
import { makeContract } from '../src/executor.mjs';
import { checkProofData } from '../harness/check.mjs';
import { toJson, proofDataOf } from '../harness/json.mjs';

const root = path.resolve(process.argv[2]);
const COIN_PK = '3c'.repeat(32);

let failures = 0, checks = 0;
const report = (ok, label, detail = '') => {
  checks++;
  if (!ok) failures++;
  if (!ok || process.env.LO_VERBOSE) console.log(`${ok ? 'ok   ' : 'FAIL '} ${label}${detail ? '  ' + detail : ''}`);
};

// ------------------------------------------------------------------------------- values
const bytes = (n, first, last) => { const b = new Uint8Array(n); b[0] = first; b[n - 1] = last; return b; };
const zeros = new Uint8Array(32);
const range = (n, f = (i) => BigInt(i + 1)) => Array.from({ length: n }, (_, i) => f(i));
const pk = { bytes: bytes(32, 0xaa, 0xbb) };
const user = { bytes: bytes(32, 0x75, 0x73) };
const other = { bytes: bytes(32, 5, 6) };
const coin = (n, color, value) => ({ nonce: bytes(32, n, n + 1), color, value });
const qcoin = (n, color, value, mt_index) => ({ ...coin(n, color, value), mt_index });
const red = bytes(32, 0x52, 0x44);
const hashBytes32 = (b) => rt.persistentHash(new rt.CompactTypeBytes(32), b);
const padBytes = (n, str) => { const b = new Uint8Array(n); b.set(new TextEncoder().encode(str)); return b; };
// A MerkleTreePath<n, T> leading nowhere: every sibling zero.
const noPath = (n, leaf) => ({ leaf, path: Array.from({ length: n }, () => ({ sibling: { field: 0n }, goes_left: false })) });

// What the witnesses return is decided by the call being made, through `ctx`; both implementations
// read the same object, so they are asked the same.
const ctx = {};
const witnesses = {
  // tiny
  secretKey: ({ privateState }) => [privateState, ctx.sk ?? bytes(32, 21, 22)],
  'private$secret_key': ({ privateState }) => [privateState, ctx.sk ?? bytes(32, 21, 22)],
  // threading
  num: ({ privateState }, n) => [privateState, n * 2n + 1n],
  // coracle
  local_secret_key: ({ privateState }) => [privateState, ctx.sk],
  local_board: ({ privateState }) => [privateState, ctx.board],
  local_set_board: ({ privateState }) => [privateState, []],
  fresh_nonce: ({ privateState }) => [privateState, 77n],
  // election_core (every call below fails before it matters; they must still be answered)
  private_secret_key: ({ privateState }) => [privateState, ctx.sk ?? bytes(32, 21, 22)],
  private_state: ({ privateState }) => [privateState, 0],
  private_state_advance: ({ privateState }) => [privateState, []],
  private_vote_record: ({ privateState }) => [privateState, []],
  private_vote: ({ privateState }) => [privateState, 0],
  context_eligible_voters_path_of: ({ privateState }) => [privateState, { is_some: false, value: noPath(10, zeros) }],
  context_committed_votes_path_of: ({ privateState }) => [privateState, { is_some: false, value: noPath(10, zeros) }],
  // zerocash_core
  private_zk_secret_key: ({ privateState }) => [privateState, ctx.zsk],
  private_zk_public_key: ({ privateState }) => [privateState, ctx.zpk],
  private_add_coin: ({ privateState }) => [privateState, []],
  private_remove_coin: ({ privateState }) => [privateState, []],
  context_path_of: ({ privateState }) => [privateState, ctx.path],
  context_new_coin_info: ({ privateState }) => [privateState, ctx.coinInfo],
  // types
  t17_witness: ({ privateState }, b) => [privateState, 5n],
};

// ------------------------------------------------------------------------------- the calls
// [program, circuit, args (or a function of the loaded program `c` that may set `ctx`), succeeds?]
const toSelfR = { is_left: false, left: pk, right: { bytes: zeros } };
const U = (v) => v;
const zsk = { bytes: bytes(32, 0x5a, 0x5b) };
const zcoin = { nonce: { bytes: bytes(32, 1, 2) }, opening: { bytes: bytes(32, 3, 4) } };
const zcoin2 = { nonce: { bytes: bytes(32, 9, 8) }, opening: { bytes: bytes(32, 7, 6) } };
const zpk = { bytes: hashBytes32(zsk.bytes) };   // what derive_zk_public_key gives
// What commitment_from_coin_info gives: the leaf stored by zerocash_mint.
const zcommit = (coin, pk) => ({ bytes: rt.persistentHash(new rt.CompactTypeVector(4, new rt.CompactTypeBytes(32)),
  [padBytes(32, 'lares:zerocash:commit'), coin.nonce.bytes, coin.opening.bytes, pk.bytes]) });
const board = (n, p) => ({ nonce: n, contents: { position: p } });
const as = (sk, b) => (c) => { ctx.sk = sk; ctx.board = b; return c.args ?? []; };
const skA = bytes(32, 0xa1, 0xa2), skB = bytes(32, 0xb1, 0xb2);
const withCtx = (f, args) => (c) => { f(c); return args(c); };
const native = zeros;
const wager = (n, v) => coin(n, red, v);

const calls = [
  ['counter', 'increment', [], true],
  ['counter', 'increment', [], true],

  ['tiny', 'get', [], true],
  ['tiny', 'set', [9n], false],
  ['tiny', 'clear', [], true],
  ['tiny', 'get', [], true],
  ['tiny', 'set', [9n], true],
  ['tiny', 'get', [], true],
  ['tiny', 'clear', [], true],
  ['tiny', 'public_key', [bytes(32, 1, 2)], true],

  ['test01', 'get', [], true],
  ['test01', 'set', [9n, 3n], false],
  ['test01', 'clear', [], true],
  ['test01', 'set', [20n, 3n], true],
  ['test01', 'set', [20n, 4n], false],
  ['test01', 'set', [9n, 0n], true],
  ['test01', 'get', [], true],
  ['test01', 'clear', [], true],

  ['threading', 'fib', [1n], true],
  ['threading', 'fib', [2n], true],
  ['threading', 'fib', [3n], true],
  ['threading', 'fib', [5n], false],
  ['threading', 'fib', [1n], true],
  ['threading', 'fib2', [false], true],
  ['threading', 'fib2', [false], true],
  ['threading', 'fib2', [true], true],

  ['gas_cost', 'testGasCost', [], true],
  ['gas_cost', 'testGasCost', [], true],

  ['block_time', 'testBlockTimeLt', [0n], true],
  ['block_time', 'testBlockTimeLt', [100n], true],
  ['block_time', 'testBlockTimeGte', [0n], true],
  ['block_time', 'testBlockTimeGt', [5n], true],
  ['block_time', 'testBlockTimeLte', [5n], true],

  ['unshielded_tokens', 'mintUnshieldedToSelfTest', [bytes(32, 1, 1), 100n], true],
  ['unshielded_tokens', 'mintUnshieldedToUserTest', [bytes(32, 2, 2), user, 7n], true],
  ['unshielded_tokens', 'mintUnshieldedToContractTest', [bytes(32, 3, 3), other, 8n], true],
  ['unshielded_tokens', 'getUnshieldedBalanceTest', [bytes(32, 1, 1)], true],
  ['unshielded_tokens', 'getUnshieldedBalanceGtTest', [bytes(32, 1, 1), 0n], true],
  ['unshielded_tokens', 'getUnshieldedBalanceLtTest', [bytes(32, 1, 1), 5n], true],
  ['unshielded_tokens', 'receiveUnshieldedTest', [bytes(32, 1, 1), 12n], true],
  ['unshielded_tokens', 'mintShieldedToSelfTest', [bytes(32, 1, 1), 50n, bytes(32, 2, 2)], true],
  ['unshielded_tokens', 'mintShieldedToUserTest', [bytes(32, 1, 1), 51n, bytes(32, 2, 3), pk], true],
  ['unshielded_tokens', 'mintShieldedToContractTest', [bytes(32, 1, 1), 52n, bytes(32, 2, 4), other], true],
  ['unshielded_tokens', 'receiveShieldedTest', [coin(6, red, 77n)], true],
  ['unshielded_tokens', 'sendShieldedToUserTest', [qcoin(7, red, 100n, 3n), pk, 30n], true],
  ['unshielded_tokens', 'sendShieldedToSelfTest', [qcoin(7, red, 100n, 3n), 100n], true],
  ['unshielded_tokens', 'sendShieldedToContractTest', [qcoin(7, red, 100n, 3n), other, 40n], true],
  ['unshielded_tokens', 'sendShieldedToUserTest', [qcoin(7, red, 100n, 3n), pk, 101n], false],
  ['unshielded_tokens', 'sendImmediateShieldedToUserTest', [coin(9, red, 20n), pk, 20n], true],
  ['unshielded_tokens', 'sendImmediateShieldedToSelfTest', [coin(9, red, 20n), 5n], true],
  ['unshielded_tokens', 'sendImmediateShieldedToContractTest', [coin(9, red, 20n), other, 5n], true],

  // coracle: two players (skA is red, skB is blue) play until blue cannot answer, then both withdraw.
  ['coracle', 'start', (c) => { ctx.sk = skA; ctx.board = board(77n, 5n); return [5n, wager(1, 10n), coin(2, native, 100000n)]; }, true],
  ['coracle', 'start', (c) => { ctx.sk = skB; ctx.board = board(77n, 6n); return [6n, wager(3, 10n), coin(4, native, 100000n)]; }, true],
  ['coracle', 'guess', (c) => { ctx.sk = skA; ctx.board = board(77n, 5n); return [3n]; }, false],
  ['coracle', 'guess', (c) => { ctx.sk = skB; ctx.board = board(77n, 6n); return [4n]; }, true],
  ['coracle', 'guess', (c) => { ctx.sk = skA; ctx.board = board(77n, 5n); return [6n]; }, true],
  ['coracle', 'guess', (c) => { ctx.sk = skB; ctx.board = board(77n, 6n); return [2n]; }, false],
  ['coracle', 'concede', (c) => { ctx.sk = skB; ctx.board = board(77n, 6n); return []; }, true],
  ['coracle', 'withdraw', (c) => { ctx.sk = skA; ctx.board = board(77n, 5n); return []; }, true],
  ['coracle', 'is_red', [skA, bytes(32, 1, 1)], true],
  ['coracle', 'is_player_alive', [board(1n, 3n), 4n], true],

  // election_core has no constructor, so `authority` is never set: every call is refused.
  ['election_core', 'add_voter', [bytes(32, 8, 8)], false],
  ['election_core', 'set_topic', [11n], false],
  ['election_core', 'advance', [], false],
  ['election_core', 'vote_commit', [0], false],
  ['election_core', 'vote_reveal', [], false],

  ['zerocash_core', 'zerocash_mint', (c) => { ctx.zpk = zpk; ctx.coinInfo = zcoin; return []; }, true],
  // the path of a coin that is not in the tree, then of the minted one, then (spent) again
  ['zerocash_core', 'spend', (c) => { ctx.zsk = zsk; ctx.coinInfo = zcoin2; ctx.path = noPath(32, zcommit(zcoin, zpk)); return [{ zk: { bytes: bytes(32, 4, 4) } }, zcoin]; }, false],
  ['zerocash_core', 'spend', (c) => { ctx.zsk = zsk; ctx.coinInfo = zcoin2; ctx.path = c.pathOf('commitments', zcommit(zcoin, zpk)); return [{ zk: { bytes: bytes(32, 4, 4) } }, zcoin]; }, true],
  ['zerocash_core', 'spend', (c) => { ctx.zsk = zsk; ctx.coinInfo = zcoin2; ctx.path = c.pathOf('commitments', zcommit(zcoin, zpk)); return [{ zk: { bytes: bytes(32, 4, 4) } }, zcoin]; }, false],
  // a path to the right root, but for another leaf than the coin's commitment
  ['zerocash_core', 'spend', (c) => { ctx.zsk = zsk; ctx.coinInfo = zcoin2; ctx.path = c.pathOf('commitments', zcommit(zcoin2, { bytes: bytes(32, 4, 4) })); return [{ zk: { bytes: bytes(32, 4, 4) } }, zcoin2]; }, false],

  ...['test_circuit_returned_vector', 'test_circuit_returned_tuple', 'test_nested_circuit_matrix', 'test_circuit_calls_in_loop',
      'test_dynamic_vector_processing', 'test_complex_nested_patterns', 'test_concatenated_circuit_results',
      'test_conditional_circuit_calls', 'test_recursive_style_processing', 'test_vector_slicing_with_circuits', 'test']
    .map((n) => ['pm_19287', n, [], true]),

  ['pm_20028', 'test1', [], true],
  ['pm_20028', 'test2', [], true],
  ['pm_20028', 'test4', [5n, 6n], true],
  ['pm_20028', 'test4', [(1n << 248n) - 1n, 6n], true],
  ['pm_20028', 'test5', [], true],
  ['pm_20028', 'test6', [], true],
  ['pm_20028', 'test8', [], true],
  ['pm_20028', 'test9', [], true],
  ['pm_20028', 'test_cast_comparison', [], true],

  ['types', 'test10a', [3n], true],
  ['types', 'test10', [3n, range(10)], true],
  ['types', 'test16', [range(10, (i) => BigInt(i))], true],

  ['assert_misc', 'ellen', [{ a: [4n], b: 5n, c: true }], true],
  ['assert_misc', 'myswitch', [1n, 2n, true], true],
  ['assert_misc', 'myswitch', [3n, 4n, false], true],
  ['assert_misc', 'myswitch', [3n, 3n, false], false],
  ['assert_misc', 'myswitch', [70000n, 1n, true], false],
  ['assert_misc', 'abel', [], true],
  ['assert_misc', 'abel', [], true],

  ['adt_counter', 'test_all', [], true],
  ['adt_counter', 'test_big_increment', [], true],
  ['adt_list_struct', 'test', [], true],
  ['adt_map_list', 'test', [], true],
  // The first assertion of each of these demands a root the test cannot know, the second its opposite:
  // the circuit is refused whatever the argument.
  ['adt_merkle', 'test', [], false],
  ['adt_merkle', 'test_historic', [], false],

  ['composable_inner', 'add', [3n], true],
  ['composable_inner', 'add', [4n], true],

  ['vectors', 'test1b', [[1n], [2n]], true],
  ['vectors', 'test2', [[1n, 2n], [3n, 4n]], true],
  ['vectors', 'test4', [], true],
  ['vectors', 'slice_to_ledger', [range(8)], true],

  ['proof_data', 'test1', [], true],
  ['proof_data', 'test2', [], true],

  ['zkir_generation', 'increment', [], true],
  ['zkir_generation', 'test1', [range(10, (i) => BigInt(250 - 7 * i))], true],
  ['zkir_generation', 'test1', [[...range(9), 256n]], false],
  ['zkir_generation', 'test2', [[200n]], true],
];

const constructorArgs = { tiny: [5n], test01: [5n], coracle: [], threading: [], gas_cost: [], pm_19287: [] };

const LEVELS = ['o2', 'lo'];

// Static checks on every circuit of every program: the same circuits with the same arguments, and the
// rewritten one sends at most as many ledger programs and has at most as many ZKIR instructions.
{
  const progs = (await fs.readdir(path.join(root, 'o2'), { withFileTypes: true })).filter((d) => d.isDirectory()).map((d) => d.name);
  for (const prog of progs) {
    const spec = async (l) => JSON.parse(await fs.readFile(path.join(root, l, prog, 'contract.json'), 'utf-8'));
    const [a, b] = [await spec('o2'), await spec('lo')];
    report(JSON.stringify(a.circuits.map((c) => [c.name, c.args])) === JSON.stringify(b.circuits.map((c) => [c.name, c.args])),
      `${prog}: same circuits and arguments`);
    for (const ca of a.circuits) {
      const cb = b.circuits.find((c) => c.name === ca.name);
      if (!cb) continue;
      const nl = (c) => c.body.filter((s) => s.kind === 'ledger' && s.ops.length > 0).length;
      report(nl(cb) <= nl(ca), `${prog}.${ca.name}: no more ledger programs`, `${nl(ca)} -> ${nl(cb)}`);
      try {
        const z = async (l) => JSON.parse(await fs.readFile(path.join(root, l, prog, 'zkir', `${ca.name}.zkir`), 'utf-8'));
        const [za, zb] = [await z('o2'), await z('lo')];
        report(zb.instructions.length <= za.instructions.length, `${prog}.${ca.name}: no more ZKIR instructions`,
          `${za.instructions.length} -> ${zb.instructions.length}`);
      } catch { /* circuits without ZKIR (none expected) */ }
    }
  }
}
const attempt = async (f) => { try { return { value: await f() }; } catch (e) { return { error: e instanceof Error ? e.message : String(e) }; } };
const encodeState = (s) => toJson((s instanceof rt.ChargedState ? s.state : s.data.state).encode(), 0);
const stateAfter = (run) => run.context.callContext.currentQueryContext.state;

const loaded = new Map();
async function load(name) {
  if (loaded.has(name)) return loaded.get(name);
  const impl = {};
  for (const level of LEVELS) {
    const dir = path.join(root, level, name);
    const spec = JSON.parse(await fs.readFile(path.join(dir, 'contract.json'), 'utf-8'));
    impl[level] = { contract: makeContract(spec, witnesses), spec, dir };
    try {
      impl[level].init = await impl[level].contract.initialState(rt.createConstructorContext({}, COIN_PK), ...(constructorArgs[name] ?? []));
    } catch (e) { impl[level].initError = String(e); }
  }
  const enc = (l) => impl[l].init ? toJson(impl[l].init.currentContractState.data.state.encode(), 0) : `error: ${impl[l].initError}`;
  report(enc('o2') === enc('lo'), `${name}: same initial ledger state`);
  const entry = { name, impl };
  loaded.set(name, entry);
  return entry;
}

const circuitContext = (circuitId, impl) =>
  rt.createCircuitContext({
    circuitId,
    contractAddress: rt.dummyContractAddress(),
    coinPublicKeyOrZswapState: impl.init.currentZswapLocalState.coinPublicKey,
    contractState: impl.state ?? impl.init.currentContractState,
    privateState: impl.init.currentPrivateState,
    time: 0,
  });

// The circuits the pass changed: their ZKIR differs.
const changedCircuit = async (name, circuit) => {
  try {
    const f = (d) => fs.readFile(path.join(root, d, name, 'zkir', `${circuit}.zkir`), 'utf-8');
    return (await f('o2')) !== (await f('lo'));
  } catch { return false; }
};

// The runtime's cost record of a call: { readTime, computeTime, bytesWritten, bytesDeleted }.
const FIELDS = ['readTime', 'computeTime', 'bytesWritten', 'bytesDeleted'];
const gasOf = (run) => {
  const g = run.value?.gasCost;
  if (g === undefined || g === null) return null;
  return Object.fromEntries(FIELDS.map((f) => [f, BigInt(g[f] ?? 0)]));
};
const gas = { o2: Object.fromEntries(FIELDS.map((f) => [f, 0n])), lo: Object.fromEntries(FIELDS.map((f) => [f, 0n])) };
const gasRows = [];
let changedCalls = 0, sample = null;
for (const [name, circuit, argsOf, shouldSucceed] of calls) {
  if (name === 'zerocash_core' || name === 'composable_outer') continue;
  const c = await load(name);
  const args = typeof argsOf === 'function' ? argsOf(c) : argsOf;
  const label = `${name}.${circuit}(${args.map((a) => toJson(a, 0)).join(', ')})`.replaceAll('"', '').slice(0, 110);
  const changed = process.env.LO_ALL ? true : await changedCircuit(name, circuit);
  const runs = {};
  for (const level of LEVELS) runs[level] = await attempt(() => c.impl[level].contract.circuits[circuit](circuitContext(circuit, c.impl[level]), ...args));
  const errs = LEVELS.filter((l) => runs[l].error);
  if (errs.length > 0) {
    report(errs.length === LEVELS.length && !shouldSucceed, `${label}: both refuse${shouldSucceed ? ' (expected to succeed)' : ''}`,
      errs.map((l) => `${l}: ${runs[l].error}`).join(' | '));
    continue;
  }
  report(shouldSucceed, `${label}: both succeed`);
  for (const level of LEVELS) c.impl[level].state = stateAfter(runs[level].value);
  const res = (l) => toJson(runs[l].value.result, 0);
  const zsw = (l) => toJson(runs[l].value.context.callContext.currentZswapLocalState, 0);
  const trace = (l) => runs[l].value.context.callProofDataTrace;
  const priv = (l) => { const t = trace(l); return t.length ? toJson(proofDataOf(t.at(-1)).privateTranscriptOutputs ?? null, 0) : 'none'; };
  report(res('o2') === res('lo'), `${label}: same result`);
  report(encodeState(c.impl.o2.state) === encodeState(c.impl.lo.state), `${label}: same ledger state`);
  report(zsw('o2') === zsw('lo'), `${label}: same Zswap local state`);
  report(priv('o2') === priv('lo'), `${label}: same private transcript`);
  const t = trace('lo');
  const proved = c.impl.lo.spec.circuits.find((x) => x.name === circuit)?.proof;
  if (proved && t.length) {
    const checked = await checkProofData({ compiledDir: c.impl.lo.dir, circuitId: circuit, proofData: proofDataOf(t.at(-1)) });
    report(checked.ok, `${label}: ZKIR check accepts lo`, checked.ok ? '' : `${checked.stage}: ${checked.error}`);
  }
  if (changed) {
    changedCalls++;
    sample ??= runs.lo.value.gasCost;
    const go = gasOf(runs.o2), gl = gasOf(runs.lo);
    if (go !== null && gl !== null) {
      for (const f of FIELDS) { gas.o2[f] += go[f]; gas.lo[f] += gl[f]; }
      gasRows.push([label, go, gl]);
    }
  }
}

console.log(`\n${changedCalls} successful calls of circuits the pass changed`);
if (process.env.LO_VERBOSE) console.log('gasCost sample:', toJson(sample ?? null, 0));
for (const [l, a, b] of gasRows) {
  console.log(`  ${FIELDS.map((f) => `${f} ${a[f]} -> ${b[f]}`).join(', ')}  ${l}`);
}
console.log('gas over those calls (o2 -> lo):');
for (const f of FIELDS) console.log(`  ${f}: ${gas.o2[f]} -> ${gas.lo[f]} (saved ${gas.o2[f] - gas.lo[f]})`);
console.log(failures === 0 ? `ledger-opt: ${checks} checks passed` : `ledger-opt: ${failures} of ${checks} checks FAILED`);
process.exit(failures === 0 ? 0 : 1);
