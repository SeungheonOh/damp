# ZKIR oracle harness: notes

Unless marked *(inferred)*, every fact below was observed: either by running the harness or by reading the installed `dist/*.js` / `*.d.ts` under `node_modules`. The compact checkout at a local checkout of the Compact compiler (0.33) is older than the runtime installed here, and some of its signatures differ (see the end of this file).

## Packages (installed in `executor/package.json`, exact pins)

| package | version | role |
|---|---|---|
| `@midnight-ntwrk/compact-runtime` | 0.21.0 | runtime that compactc 0.36.1 output expects (`checkRuntimeVersion('0.21.0')`) |
| `@midnightntwrk/onchain-runtime-v4` | 4.0.2 (transitive, `^4.0.0-rc.3`) | wasm VM; compact-runtime re-exports most of it |
| `@midnightntwrk/zkir-v3` | 3.2.1 | ZKIR v3 wasm: `check`, `prove`, `jsonIrToBinary`, `Zkir` |

- Both scopes exist for zkir-v3 (`@midnight-ntwrk/zkir-v3` and `@midnightntwrk/zkir-v3`), with the same version list. I used `@midnightntwrk/…`, which is what the compact test-center imports.
- `@midnightntwrk/compact-runtime` does not exist (npm E404). The runtime is only published as `@midnight-ntwrk/compact-runtime`.
- Node v26.13.1 and npm 11.20.0. The package's `exports.node` resolves to `midnight_zkir_wasm_fs.js`. Importing the browser entry directly gives an "ExperimentalWarning: Importing WebAssembly module instances".

## Running it

```
cd executor
node harness/run-compactc-module.mjs            # step, inc, manual; full JSON dumps
QUIET=1 node harness/run-compactc-module.mjs    # verdicts only (exit 0 iff all expectations met)
node harness/run-compactc-module.mjs manual     # just one scenario: step | inc | manual
```

Fixtures were recompiled with compactc 0.36.1 into `executor/fixtures/{step,inc}/` and include the `.compact` source. They live inside `executor/` so that the generated `import '@midnight-ntwrk/compact-runtime'` resolves against `executor/node_modules`. A compiled dir placed anywhere else needs `node_modules` resolvable from it.

## The oracle: `harness/check.mjs`

```js
checkProofData({ compiledDir, circuitId, proofData, timeoutMs?, prove? })
  -> { ok: true, outputs, proof? } | { ok: false, stage: 'serialize'|'check'|'prove', error }
```

1. It serializes the preimage with `proofDataIntoSerializedPreimage(input, output, publicTranscript, privateTranscriptOutputs, keyLocation)`. That function comes from onchain-runtime-v4 and is re-exported by compact-runtime. `keyLocation` is a plain string; we pass the circuit id.
2. It then calls `zkir.check(preimage, provider)`. The provider is `{ lookupKey(keyLocation) -> {proverKey, verifierKey, ir}, getParams(k) -> Uint8Array }`, where `ir` is the bytes of `zkir/<c>.bzkir`. `jsonIrToBinary(<.zkir text>)` gives an equivalent `ir`.
3. **`check` reads only `ir`.** The probe confirmed this: with empty `proverKey`/`verifierKey` and a `getParams` that throws, `check` still passes and calls only `lookupKey`. So `check` rebuilds the circuit witness from the preimage and evaluates the constraints. It does not produce or verify a proof.
4. With `prove: true`, it also runs `zkir.prove`. This does read `keys/<c>.prover` and calls `getParams(k)`, which loads `~/.cache/midnight/zk-params/bls_midnight_2p<k>` (k=9 for `step`). It takes about 1 s and returns a 3845-byte proof for `step`. Proving tampered data fails with the same error that `check` gives.
5. **No proof verifier is exported** by zkir-v3 or onchain-runtime-v4, so the `.verifier` keys go unused here.
6. `check` resolves to an array of `bigint|undefined`. Observed values: `[null,null,null]` for `step`, `[null×6]` for `inc(3,true)`, and `[null,null,null,4n,2n,1n]` for `inc(3,false)`. *(inferred: these are the public-input slots the IR computes; their meaning is not established.)*
7. A wrong `keyLocation` gives `failed to resolve key at '<loc>'` (when `lookupKey` returns `undefined`).

How rejections look (all observed):

| tampered field | error |
|---|---|
| witness output, pushed cell value, or input | `Public transcript input mismatch for input N; expected: Some(hex), computed: Some(hex)` |
| circuit output | `Communications commitment mismatch` |
| `popeq.result` read | `Failed direct assertion` |
| a dropped op | `... expected: None, computed: Some(..)` |

A non-canonical Value fails earlier, at serialization. For example, the field 5 encoded as `[0x05,0x00]` gives `value deserialized as aligned failed alignment check`.

## Value encoding (`AlignedValue = { value: Uint8Array[], alignment: AlignmentSegment[] }`)

- **AlignmentSegment** is `{tag:'atom', value:{tag:'field'}}`, `{tag:'atom', value:{tag:'bytes', length:L}}`, `{tag:'atom', value:{tag:'compress'}}`, or `{tag:'option', value: Alignment[]}`.
- **Composite values** concatenate both lists: `value = a.toValue(x).concat(b.toValue(y))` and `alignment = a.alignment().concat(b.alignment())`. Circuit inputs, structs and tuples are built this way.
- **`bigIntToValue(x)`** returns one atom: x as little-endian bytes with trailing zero bytes stripped. So 0 → `[Uint8Array(0)]`, 5 → `[05]`, 300 → `[2c01]`. This byte string must be canonical.
- **`CompactTypeField`** (a plain object, not a class): `alignment()` = `[{atom field}]`; `toValue(x)` = `bigIntToValue(x)`; `fromValue(v)` = `valueToBigInt([v.shift()])`.
- **`new CompactTypeUnsignedInteger(maxValue, lengthBytes)`**:
  - `alignment()` = `[{atom bytes length}]`.
  - `toValue` range-checks against `maxValue`, then uses Field encoding (LE, stripped).
  - `fromValue` shifts one atom and reads it as LE.
  - compactc chooses `length` as the minimum number of bytes for the max: `Uint<0..10>` → (9n,1), `Uint<16>` → (65535n,2), `Uint<8>` → (255n,1). `Counter` is (2^64-1, 8).
  - Ledger array/field indices are encoded as `(255n,1)`.
- **`CompactTypeBoolean`**: `alignment()` = `[{atom bytes 1}]`. `true` → `[Uint8Array[1]]` and `false` → `[Uint8Array[]]`. `fromValue` throws unless it gets an empty array or `[1]`.
- **`new CompactTypeBytes(n)`**: `alignment()` = `[{atom bytes n}]`. `toValue` strips trailing zeros, so 32 zero bytes become `[Uint8Array(0)]`. `fromValue` pads back to n.
- **`fromValue` mutates its argument**: it consumes atoms from the front with `shift`/`splice`. To decode composites, call the member decoders in sequence on the same array.
- Generated struct, Maybe and Either types are small classes with the same three methods that concatenate their members (see the `_Either_0` and `_Maybe_0` classes in `fixtures/*/contract/index.js`).

## Contexts

```js
createConstructorContext(initialPrivateState, coinPublicKeyHex64)
  -> { initialPrivateState, initialZswapLocalState: {coinPublicKey:{bytes}, currentIndex, inputs, outputs} }

createCircuitContext({ circuitId, contractAddress, coinPublicKeyOrZswapState, contractState, privateState,
                       gasLimit?, costModel?, time?, parentBlockHash?, crossContract? })   // ONE OPTIONS OBJECT in 0.21
  -> { callContext:{circuitId, contractAddress, initialQueryContext, currentQueryContext, currentGasCost,
                    currentPrivateState, currentZswapLocalState, parentBlockHash, time},
       queryContexts:{[addr]:QueryContext}, gasCosts, zswapLocalStates, contractStates:{}, costModel,
       callProofDataTrace: [], gasLimit, activeContracts:Set, events: [] }
```

- `contractState` can be a `ContractState`, a `ChargedState` or a `StateValue`.
- `coinPublicKeyOrZswapState` can be a hex string, `{bytes}`, or a (possibly encoded) zswap local state.
- `time` defaults to `Math.floor(Date.now()/1000)`.
- `gasLimit` defaults to `undefined`, which means unlimited. A tiny limit raises `CompactError: ran out of gas budget`.
- `costModel` defaults to `CostModel.initialCostModel()`.
- Addresses: `sampleContractAddress()` and `dummyContractAddress()`. compactc's own constructor code uses `dummyContractAddress()`.

## What a compactc circuit wrapper does (the shape a generic executor must reproduce)

```js
const context = copyCircuitContext(ctxIn);          // shallow copies of the maps/arrays
const ppd = { input: {value, alignment},            // concat of arg descriptors' toValue/alignment
              output: undefined, publicTranscript: [], privateTranscriptOutputs: [] };
... body ...
ppd.output = { value: desc.toValue(result), alignment: desc.alignment() };   // [] / [] for return type []
finalizeCallProofData(context, ppd);   // pushes {...ppd, circuitId, contractAddress, initialQueryContext,
                                       //          finalQueryContext, zswapLocalState} onto context.callProofDataTrace
return { result, context, gasCost: context.callContext.currentGasCost };
```

- **Witness call**: `[nextPS, r] = witnesses.w(createWitnessContext(ledger(currentQueryContext.state), currentPrivateState, currentQueryContext.address))`. It is synchronous: generated code does not `await` it. Then:
  - set `context.callContext.currentPrivateState = nextPS`;
  - type-check `r`;
  - `ppd.privateTranscriptOutputs.push({value: desc.toValue(r), alignment: desc.alignment()})`.

  A witness call that is skipped at runtime (the false branch of `b ? hint() : 0`) pushes nothing. The proof still checks.
- **Ledger ops**: `queryLedgerState(context, ppd, ops)` is synchronous.
  - It runs `currentQueryContext.query(ops, costModel, gasLimit)`.
  - It updates `currentQueryContext` and gas, and the per-address maps when `callContext.contractAddress` is set.
  - It appends `ops` to `ppd.publicTranscript`. Each `popeq` gets its `result: undefined` replaced by the AlignedValue that was actually read, in order.
  - It returns the read AlignedValue if exactly one `read` event happened, otherwise `undefined`. Callers then do `desc.fromValue(ret.value)`.
  - VM errors are rethrown as `CompactError`.
- **Builtins**:
  - `transientHash(desc, v)` returns a bigint.
  - `persistentHash(desc, v)` returns a 32-byte `Uint8Array`.
  - Field arithmetic: `addField`, `subField`, `mulField`.
  - `assert(cond, msg)` throws `CompactError: failed assert: <msg>`. The circuit fails in JS before any proof data exists.
- **Async**: `initialState(ctx)` and every circuit are `async`. Internally only `_circuit_0` bodies are awaited; `queryLedgerState`, witnesses and hashes are all synchronous.

## Impact op JSON (`Op<null>` going in; the transcript stores `Op<AlignedValue>`)

Ops seen in the generated code:

```js
// Cell write, ledger field i (Cell<T>):
{ push: { storage: false, value: StateValue.newCell({ value: U8.toValue(i), alignment: U8.alignment() }).encode() } }
{ push: { storage: true,  value: StateValue.newCell({ value: T.toValue(v),  alignment: T.alignment()  }).encode() } }
{ ins:  { cached: false, n: 1 } }

// Cell read, field i:
{ dup: { n: 0 } }
{ idx: { cached: false, pushPath: false, path: [ { tag: 'value', value: { value: U8.toValue(i), alignment: U8.alignment() } } ] } }
{ popeq: { cached: false, result: undefined } }   // in transcript: result = AlignedValue read

// Counter.increment(k) on field i:
{ idx:  { cached: false, pushPath: true, path: [ {tag:'value', value:{value:U8.toValue(i), alignment:U8.alignment()}} ] } }
{ addi: { immediate: Number(k) } }        // compactc: parseInt(valueToBigInt({value:U16.toValue(k),...}.value))
{ ins:  { cached: true, n: 1 } }
// Counter read: same as Cell read but popeq.cached = true.
```

- `StateValue.newCell(av).encode()` returns `{ tag: 'cell', content: AlignedValue }`. The full `EncodedStateValue` union is `null | cell | map(Map<AlignedValue,ESV>) | array(ESV[]) | boundedMerkleTree`.
- The other op forms exist in the type but were not seen in these samples: `noop`, `lt`, `eq`, `type`, `size`, `new`, `and`, `or`, `neg`, `log`, `root`, `pop`, `subi`, `branch{skip}`, `jmp{skip}`, `add`, `sub`, `concat{cached,n}`, `member`, `rem{cached}`, `swap{n}`, `ckpt`.
- Path keys are `{tag:'value', value: AlignedValue}` or `{tag:'stack'}`.
- Real `inc(3,true)` transcript (popeq result abbreviated):
  `[{dup:{n:0}}, {idx:{cached:false,pushPath:false,path:[{tag:'value',value:{value:[01],alignment:[bytes1]}}]}}, {popeq:{cached:false,result:{value:[aac8…605a],alignment:[bytes32]}}}, {idx:{cached:false,pushPath:true,path:[{…value:[<empty>]…}]}}, {addi:{immediate:3}}, {ins:{cached:true,n:1}}]`

## Initial ContractState (what compactc's `initialState` does)

```js
const state = new ContractState();
let sv = StateValue.newArray();
for (each ledger field) sv = sv.arrayPush(StateValue.newNull());   // one slot per ledger field
state.data = new ChargedState(sv);
for (each provable circuit) state.setOperation('<name>', new ContractOperation());  // empty op (no VK)
const ctx = createCircuitContext({ circuitId: 'constructor', contractAddress: dummyContractAddress(),
                                   coinPublicKeyOrZswapState: cctx.initialZswapLocalState.coinPublicKey,
                                   contractState: state.data, privateState: cctx.initialPrivateState });
queryLedgerState(ctx, ppd, <Cell-write ops for each field's default value>);   // 0n, new Uint8Array(32), ...
state.data = new ChargedState(ctx.callContext.currentQueryContext.state.state);
return { currentContractState: state, currentPrivateState: ctx.callContext.currentPrivateState,
         currentZswapLocalState: ctx.callContext.currentZswapLocalState };
```

- `currentQueryContext.state` is a `ChargedState`, and `.state` on that gives the `StateValue`.
- The scenario `manual` in `run-compactc-module.mjs` rebuilds both this and the `step` call using only runtime calls, without importing `contract/index.js`. `check` accepts the result. This is the template for the generic executor.

## Surprises

- **`checkRuntimeVersion(v)`**: major versions must match. For 0.x the minor must match exactly. Expected minor and patch must be ≤ the actual ones. It also compares `MAX_FIELD` with the runtime's value.
- **Version drift from the 0.33 checkout**: compactc 0.36.1 output and runtime 0.21 call `createCircuitContext({…})` with an options object, but the 0.33 checkout's `test-center/util.ts` calls it positionally (`createCircuitContext('constructor', addr, cpk, state, ps)`). Use the installed `dist/*.d.ts` as the reference.
- **Generated module setup**: the module also creates a `_dummyContract` and an `_emptyContext` at module load. Generated `ledger(state)` getters run `queryLedgerState` on a synthetic context that has no address. That is why `queryLedgerState` guards the per-address update.
- **`t.compact`'s `inc`** asserts `persistentHash(secret()) == owner`, but nothing ever sets `owner`, so it is 32 zero bytes. The harness first patches ledger slot 1 with a hand-written Cell-write program, then calls `inc`.
- **Pure circuits** such as `arith` produce no `.zkir`. Their `circuits.arith(ctx, …)` returns `{result, context}` with no proof data.
