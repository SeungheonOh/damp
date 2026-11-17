// The calls the executor tests make, shared by test/run.mjs (against compactc's
// generated modules) and test/conformance.mjs (against the Lean definition,
// test/executor.sh).
//
// An argument list may be a function of the loaded contract `c`, evaluated just
// before the call; it may use `c.rootOf(field)` (the current root of Merkle tree
// field `field`) and `c.rootIn(field, key)` (of the tree at `key` of map field
// `field`), which each test provides.

import * as rt from '@midnight-ntwrk/compact-runtime';

/** `n` bytes: `first`, then zeros, then `last`. */
const bytes = (n, first, last) => { const b = new Uint8Array(n); b[0] = first; b[n - 1] = last; return b; };
const admin = new Uint8Array(32); admin.set(new TextEncoder().encode('admin'));

const vaultKey = bytes(32, 21, 22);

export const witnesses = {
  hint: ({ privateState }) => [privateState, 7n],
  delta: ({ privateState }) => [privateState, 3n],
  pick: ({ privateState }) => [privateState, { x: 1000n, y: 9n }],
  secret: ({ privateState }) => [privateState, bytes(32, 7, 250)],
  nonce: ({ privateState }) => [privateState, bytes(32, 11, 12)],
  key: ({ privateState }) => [privateState, vaultKey],
  // Returns nothing; counts its calls in the private state.
  note: ({ privateState }, x) => [{ ...privateState, notes: [...(privateState.notes ?? []), x] }, []],
};

// ---------------------------------------------------------------- cross-contract calls (docs/calls.md)
//
// These contracts run in a simulated chain (world.mjs), each deployed at its
// address below, in this order (callees before their callers), and every call
// on one of them is made against that chain. A contract value is its address,
// `{ bytes }` in JS.
export const addresses = {
  adder: 'a0'.repeat(32),
  rich: 'a1'.repeat(32),
  relay: 'a2'.repeat(32),
  caller: 'a3'.repeat(32),
  top: 'a4'.repeat(32),
  picker: 'a5'.repeat(32),
};
// Addresses that hold something else than they claim:
//   ghost: the adder's code and state, but no module bound to the address
//     (the caller cannot find the implementation);
//   impostor: the adder's module, but the verifier key deployed for `addTo` is
//     `clear`'s (the runtime's verifier-key guard refuses the module);
//   nobody: nothing deployed at all.
export const strangers = {
  ghost: { address: 'b0'.repeat(32), like: 'adder', bound: false },
  impostor: { address: 'b1'.repeat(32), like: 'adder', bound: true, keys: (k) => ({ ...k, addTo: k.clear }) },
  nobody: { address: 'b2'.repeat(32) },
};
const ref = (name) => ({ bytes: rt.encodeContractAddress(addresses[name] ?? strangers[name].address) });
// An address as `picker` takes it: plain bytes in the Damp build (which casts
// them), a contract value in compactc's (which cannot). The argument lists of
// its calls are functions of the implementation, 'damp' or 'compactc'.
const addrFor = (kind, name) => (kind === 'damp' ? ref(name).bytes : ref(name));

// Constructor arguments, per contract.
export const constructorArgs = {
  vault: [rt.persistentHash(new rt.CompactTypeBytes(32), vaultKey), 40n],
  caller: [ref('adder'), ref('rich')],
  relay: [ref('adder')],
  top: [ref('relay')],
};

// Coins and recipients for the tokens contract. The test contract's address is
// the runtime's dummy address, 32 zero bytes.
const zeros = new Uint8Array(32);
const pk = { bytes: bytes(32, 0xaa, 0xbb) };
const self = { bytes: zeros };
const other = { bytes: bytes(32, 5, 6) };
const user = { bytes: bytes(32, 0x75, 0x73) };
const toKey = { is_left: true, left: pk, right: { bytes: zeros } };
const toSelf = { is_left: false, left: { bytes: zeros }, right: self };
const toOther = { is_left: false, left: { bytes: zeros }, right: other };
const uToSelf = { is_left: true, left: self, right: { bytes: zeros } };
const uToOther = { is_left: true, left: other, right: { bytes: zeros } };
const uToUser = { is_left: false, left: { bytes: zeros }, right: user };
const red = bytes(32, 0x52, 0x44);
const blue = bytes(32, 0x42, 0x4c);
const coin = (n, color, value) => ({ nonce: bytes(32, n, n + 1), color, value });
const qcoin = (n, color, value, mt_index) => ({ ...coin(n, color, value), mt_index });
const U128_MAX = (1n << 128n) - 1n;

// The unshielded token the tokens contract mints (`tokenType(pad(32, "damp:u"),
// self)`), and the balance of it the contract holds when each call starts, so
// that the balance circuits read something other than the default 0.
const uColor = rt.persistentCommit(new rt.CompactTypeVector(2, new rt.CompactTypeBytes(32)),
  [new Uint8Array([...new TextEncoder().encode('damp:u'), ...new Uint8Array(26)]), zeros],
  new Uint8Array([...new TextEncoder().encode('midnight:derive_token'), ...new Uint8Array(11)]));
const balances = {
  tokens: new Map([[{ tag: 'unshielded', raw: Buffer.from(uColor).toString('hex') }, 25n]]),
};

/**
 * The contract state a call starts from, as `createCircuitContext` takes it:
 * `state` itself, or, for a contract given balances above, a ContractState
 * holding it with those balances.
 */
export function startState(name, state) {
  const balance = balances[name];
  if (!balance) return state;
  const cs = new rt.ContractState();
  cs.data = state instanceof rt.ContractState ? state.data : state;
  cs.balance = balance;
  return cs;
}

const rootOf = (field) => (c) => c.rootOf(field);
const rootIn = (field, k) => (c) => c.rootIn(field, k);

// [contract, circuit, args, should the call succeed]. `args` may be a function
// of the loaded contract, evaluated just before the call.
export const calls = [
  ['step', 'step', [5n, true, 42n], true],
  ['step', 'step', [5n, false, 42n], true],
  ['step', 'step', [5n, true, 5000n], false],
  ['counter', 'bump', [12n, true, false], true],
  ['counter', 'bump', [12n, true, true], true],
  ['counter', 'bump', [12n, false, false], true],
  ['counter', 'bump', [600n, true, false], false],
  ['counter', 'arith', [9n, 4n, 100n], false],
  ['counter', 'arith', [4n, 4n, 100n], true],
  ['counter', 'arith', [3n, 4n, 100n], false],
  ['shapes', 'move', [{ x: 5n, y: 2n }, [1n, 2n, 3n], true, true], true],
  ['shapes', 'move', [{ x: 5n, y: 2n }, [1n, 2n, 3n], true, false], true],
  ['shapes', 'move', [{ x: 5n, y: 2n }, [1n, 2n, 3n], false, true], true],
  ['shapes', 'move', [{ x: 5n, y: 300n }, [1n, 2n, 3n], true, true], false],
  ['shapes', 'pay', [77n, 10n, 3n, 2n], true],
  ['shapes', 'pay', [77n, 5n, 2n, 2n], true],
  ['shapes', 'pay', [78n, 1n, 7n, 9n], true],
  ['shapes', 'pay', [77n, 1n, 7n, 9n], true],
  ['loops', 'tally', [[1n, 2n, 3n, 4n], [true, false, true, true], 3n], true],
  ['loops', 'tally', [[1n, 2n, 3n, 4n], [false, true, false, false], 200n], true],
  ['bytes', 'claim', [bytes(32, 1, 2), bytes(8, 3, 4), true], false],
  ['bytes', 'claim', [admin, bytes(8, 3, 4), true], true],
  ['bytes', 'claim', [admin, bytes(8, 5, 6), false], true],
  ['bytes', 'store', [bytes(64, 9, 200), 12345n], true],
  ['extras', 'advance', [0, bytes(32, 1, 1), { is_some: true, value: 500n }, 42n], true],
  ['extras', 'advance', [1, bytes(32, 1, 1), { is_some: true, value: 500n }, 42n], false],
  ['extras', 'advance', [1, bytes(32, 2, 2), { is_some: true, value: 50n }, 43n], true],
  ['extras', 'advance', [2, bytes(32, 3, 3), { is_some: false, value: 0n }, 44n], true],
  ['extras', 'advance', [0, bytes(32, 4, 4), { is_some: false, value: 0n }, 45n], false],
  ['vault', 'spend', [30n], true],
  ['vault', 'spend', [5n], true],
  ['vault', 'spend', [6n], false],
  ['vault', 'digest', [3n, 4n], true],
  ['notes', 'save', [5n, 6n, true], true],
  ['notes', 'save', [7n, 8n, false], true],
  ['structures', 'tick', [5n, 10n, false], true],
  ['structures', 'tick', [3n, 2n, false], true],
  ['structures', 'tick', [1n, 100n, true], true],
  ['structures', 'tick', [0n, 1n, false], false],
  ['structures', 'books', [7n, false], true],
  ['structures', 'books', [8n, false], true],
  ['structures', 'books', [9n, true], true],
  ['structures', 'dequeue', [], true],
  ['structures', 'enqueue', [11n], true],
  ['structures', 'enqueue', [0n], true],
  ['structures', 'dequeue', [], true],
  ['structures', 'enqueue', [5n], true],
  ['structures', 'enqueue', [6n], true],
  ['structures', 'dequeue', [], true],
  ['structures', 'plant', [1n, 2n, 3n, bytes(32, 4, 5)], true],
  ['structures', 'plant', [6n, 7n, 16n, bytes(32, 8, 9)], false],
  ['structures', 'check', (c) => [rootOf('tree')(c), false], true],
  ['structures', 'check', [{ field: 123n }, true], true],
  ['structures', 'record', (c) => [bytes(32, 1, 2), bytes(32, 3, 4), bytes(32, 5, 6), 2n, rootOf('hist')(c), 0n], true],
  ['structures', 'record', (c) => [bytes(32, 7, 8), bytes(32, 9, 10), bytes(32, 11, 12), 5n, rootOf('hist')(c), 1n], true],
  ['structures', 'record', [bytes(32, 1, 2), bytes(32, 3, 4), bytes(32, 5, 6), 2n, { field: 99n }, 2n], true],
  ['structures', 'stamp', [0n], true],
  ['structures', 'stamp', [5n], true],
  ['structures_nested', 'vote', [1n, 5n], true],
  ['structures_nested', 'vote', [1n, 2n], true],
  ['structures_nested', 'vote', [2n, 0n], false],
  ['structures_nested', 'group', [7n, 1n, 5n, false], true],
  ['structures_nested', 'group', [7n, 1n, 5n, false], true],
  ['structures_nested', 'group', [7n, 2n, 100n, false], true],
  ['structures_nested', 'group', [7n, 1n, 100n, true], true],
  ['structures_nested', 'group', [7n, 2n, 100n, true], true],
  ['structures_nested', 'join', [1n, 10n, false], true],
  ['structures_nested', 'join', [1n, 11n, false], true],
  ['structures_nested', 'join', [2n, 12n, true], true],
  ['structures_nested', 'enqueue', [1n, 10n], true],
  ['structures_nested', 'enqueue', [1n, 11n], true],
  ['structures_nested', 'enqueue', [1n, 12n], true],
  ['structures_nested', 'enqueue', [2n, 13n], true],
  ['structures_nested', 'grow', [1n, 10n, 5n, { field: 0n }, false], true],
  ['structures_nested', 'grow', (c) => [1n, 20n, 6n, rootIn('trees', 1n)(c), false], true],
  ['structures_nested', 'grow', [1n, 30n, 7n, { field: 0n }, true], true],
  ['structures_nested', 'grow', [1n, 30n, 16n, { field: 0n }, false], false],
  ['structures_nested', 'hgrow', [1n, 10n, 5n, { field: 0n }, 0n], true],
  ['structures_nested', 'hgrow', (c) => [1n, 20n, 6n, rootIn('hists', 1n)(c), 0n], true],
  ['structures_nested', 'hgrow', (c) => [1n, 30n, 7n, rootIn('hists', 1n)(c), 1n], true],
  ['structures_nested', 'hgrow', [1n, 40n, 8n, { field: 0n }, 2n], true],
  ['tokens', 'whoami', [], true],
  ['tokens', 'native', [], true],
  ['tokens', 'derive', [bytes(32, 1, 2)], true],
  ['tokens', 'mint', [100n, bytes(32, 1, 1), pk], true],
  ['tokens', 'mint', [1n << 64n, bytes(32, 1, 1), pk], false],
  ['tokens', 'mintSelf', [50n, bytes(32, 2, 2)], true],
  ['tokens', 'mintTo', [7n, bytes(32, 3, 3), toKey], true],
  ['tokens', 'mintTo', [8n, bytes(32, 4, 4), toSelf], true],
  ['tokens', 'mintTo', [9n, bytes(32, 5, 5), toOther], true],
  ['tokens', 'deposit', [coin(6, red, 77n)], true],
  ['tokens', 'setTreasury', [qcoin(7, red, 100n, 3n)], true],
  ['tokens', 'pay', [toKey, 30n], true],
  ['tokens', 'pay', [toSelf, 100n], true],
  ['tokens', 'pay', [toOther, 40n], true],
  ['tokens', 'pay', [toKey, 101n], false],
  ['tokens', 'payImm', [coin(8, blue, 20n), toSelf, 5n], true],
  ['tokens', 'payImm', [coin(9, blue, 20n), toKey, 20n], true],
  ['tokens', 'payImm', [coin(9, blue, 20n), toOther, 21n], false],
  ['tokens', 'burn', [10n], true],
  ['tokens', 'burn', [100n], true],
  ['tokens', 'merge', [qcoin(10, red, 5n, 4n)], true],
  ['tokens', 'merge', [qcoin(11, blue, 5n, 5n)], false],
  ['tokens', 'merge', [qcoin(12, red, U128_MAX, 6n)], false],
  ['tokens', 'mergeImm', [coin(13, red, 1n)], true],
  ['tokens', 'mergeImm', [coin(14, blue, 1n)], false],
  ['tokens', 'evolve', [3n], true],
  ['tokens', 'evolve', [4n], true],
  ['tokens', 'mintU', [1000n, user], true],
  ['tokens', 'mintUTo', [5n, uToSelf], true],
  ['tokens', 'mintUTo', [6n, uToOther], true],
  ['tokens', 'mintUTo', [7n, uToUser], true],
  ['tokens', 'sendU', [10n, uToUser], true],
  ['tokens', 'sendU', [3n, uToSelf], true],
  ['tokens', 'sendU', [4n, uToOther], true],
  ['tokens', 'recvU', [12n], true],
  ['tokens', 'balU', [], true],
  ['tokens', 'cmpU', [0n], true],
  ['tokens', 'cmpU', [5n], true],
  ['tokens', 'cmpU', [25n], true],
  ['tokens', 'cmpU', [26n], true],
  // Holding coins: store a received coin, spend it with and without change (the
  // change stored again), merge stored coins.
  ['tokens', 'keepOnly', [coin(30, red, 5n), toSelf], false],
  ['tokens', 'keep', [coin(31, red, 100n)], true],
  ['tokens', 'spend', [toKey, 30n], true],
  ['tokens', 'spend', [toSelf, 20n], true],
  ['tokens', 'keepMap', [1n, coin(32, red, 40n)], true],
  ['tokens', 'mergeKept', [1n], true],
  ['tokens', 'mergeKept', [2n], false],
  ['tokens', 'mergeHeld', [coin(33, red, 10n)], true],
  ['tokens', 'spend', [toKey, 101n], false],
  ['tokens', 'spend', [toOther, 100n], true],
  ['tokens', 'keepSet', [coin(34, blue, 7n)], true],
  ['tokens', 'keepList', [coin(35, blue, 8n)], true],
  ['tokens', 'keepList', [coin(36, blue, 9n)], true],
  // cross-contract calls (in the simulated chain; see `addresses`)
  ['adder', 'addTo', [100n], true],
  ['caller', 'bump', [5n], true],
  ['caller', 'bump', [13n], false],                  // the callee's assert fails
  ['caller', 'maybe', [true, 7n], true],
  ['caller', 'maybe', [false, 8n], true],            // not called, not claimed
  ['caller', 'twice', [1n, 2n], true],
  ['caller', 'twice', [3n, 13n], false],             // the second call fails
  ['caller', 'via', [ref('adder'), 4n], true],
  ['caller', 'via', [ref('rich'), 4n], false],       // rich does not have the contract type Adder
  ['caller', 'via', [ref('ghost'), 4n], false],      // no implementation for the address
  ['caller', 'via', [ref('impostor'), 4n], false],   // verifier key differs from the module's
  ['caller', 'via', [ref('nobody'), 4n], false],     // nothing deployed there
  ['caller', 'reset', [], true],
  ['caller', 'fancy', [{ x: 10n, y: 3n }, bytes(32, 7, 8), 500n], true],
  ['caller', 'fancy', [{ x: 10n, y: 300n }, bytes(32, 7, 8), 1n], false],   // argument out of range
  ['caller', 'fancy', [{ x: 1n, y: 255n }, bytes(32, 9, 9), 65535n], true],
  ['top', 'go', [9n], true],                         // top -> relay -> adder
  ['top', 'go', [13n], false],                       // the innermost callee's assert fails
  ['relay', 'relay', [2n], true],
  ['top', 'go', [1n], true],
  // the callee chosen at run time: an address cast to a contract type
  ['picker', 'viaArg', (k) => [addrFor(k, 'adder'), 3n], true],
  ['picker', 'register', (k) => [1n, addrFor(k, 'adder')], true],
  ['picker', 'viaMap', [1n, 4n], true],                          // the address from a Map lookup
  ['picker', 'both', (k) => [addrFor(k, 'adder'), 2n], true],    // one address, two contract types
  ['picker', 'viaArg', (k) => [addrFor(k, 'rich'), 1n], false],  // no such entry point at that address
  ['picker', 'wrongSig', (k) => [addrFor(k, 'adder'), 1n], false], // the entry point has another signature
  ['picker', 'viaArg', (k) => [addrFor(k, 'ghost'), 1n], false], // no implementation registered for the address
  ['picker', 'register', (k) => [2n, addrFor(k, 'rich')], true],
  ['picker', 'viaMap', [2n, 1n], false],                         // the stored address has no `addTo`
];

