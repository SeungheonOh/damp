# Deploying Damp contracts with midnight-js: notes

Date: 2026-11-16. Unless something is marked *(read in source)*, every fact
here was observed by running it against the local network in `compose.yml`.
"Source" means the installed `node_modules/@midnight-ntwrk/*/dist/*.js` of
midnight-js 5.0.0 and compact-js 3.0.0.

## Result

| scenario | outcome |
|---|---|
| baseline: compactc `counter`, deploy + 3 calls + read back | **works** |
| **Damp `counter`** (contract.json + executor + adapter), deploy + 3 calls + read back | **works** |
| interop: compactc deploys, Damp calls the same contract, and the reverse | **works** (`findDeployedContract` also accepts it) |
| **Damp `vault`** (constructor with args, `Bytes<32>` cell, `persistentHash` witness check) | **works** |
| negative B1: wrong verifier key, proof made from the same bundle | rejected by the proof server's self-verification (`400`) |
| negative B2: wrong verifier key on chain, valid `bump` proof submitted | rejected **by the node**: `Transaction malformed: failed to verify proof: Invalid proof`, `Malformed(InvalidProof)` (RPC `1010 … Custom error: 115`; 115 is `MalformedError::InvalidProof` in midnight-node `ledger/src/ledger_9/types.rs`) |

No step was mocked. Proofs come from the proof-server container (`POST /check`
and `POST /prove` appear in its log for every call). Transactions are balanced
and signed by a real wallet-sdk 2.0.0 wallet built from the genesis seed
`00…01`. They are submitted to the node and read back through the indexer.
The B2 control shows that the node really verifies each contract proof against
the verifier key registered at deploy. So the Damp calls that succeeded passed
the node's verification.

### Evidence (fresh chain, `./scripts/all.sh`, logs in `out/`)

Damp counter (`out/damp-counter.log`):

```
DEPLOYED address=7d3aead464541705c62212a8ed091a56db65449a88b773ae110766b045f0161a txId=00525490…05612 txHash=b2381a1e…440f1 block=25
CALL bump(5, true, false) result=5  txHash=258588b4…ed60f block=28 status=SucceedEntirely
CALL bump(7, true, true)  result=12 txHash=61a3c93d…ec753 block=31 status=SucceedEntirely
CALL arith(4, 4, 100)     result=97 txHash=2670cfc8…b31e  block=34 status=SucceedEntirely
FINAL ledger (indexer): {"count":"12","total":"97","cap":"24"}
RESULT ok: ledger matches expected {"count":"12","total":"97","cap":"24"}
```

The indexer was also queried directly over GraphQL, without midnight-js
(`out/indexer-damp-counter.json`). It shows a `ContractDeploy` at height 25 and
`ContractCall`s with entry points `bump`, `bump` and `arith` at heights 28, 31
and 34, all with the transaction hashes above.

Baseline counter (`out/baseline-counter.log`): deployed at block 8. The calls
landed at blocks 11, 14 and 17 with the same results and the same final ledger.

Interop (`out/checks.log`): the compactc module deployed
`e1da2644…58ae` (block 42). Then Damp `bump(10,true,false)` landed at block 45,
compactc `bump(1,true,true)` at block 48 and Damp `arith(3,3,50)` at block 51.
The ledger then read `{count:11,total:47,cap:15}` through both compactc's
`ledger()` and the adapter's `ledger()`.

Vault (`out/damp-vault.log`): deployed at block 62 with constructor args. The
ledger then read `owner=35ce7c7f…8f34` (= `persistentHash(key)`), `limit=40`,
`spent=0`. `spend(30)` landed at block 65 and `spend(5)` at block 68.
`spend(6)` was refused locally with `failed assert: over limit`, before any
proof was made.

## What midnight-js 5 requires of a contract module

### Properties actually touched (observed)

The adapter wraps the contract class and instance in a `Proxy` and logs every
`get`, `has`, `ownKeys` and `getOwnPropertyDescriptor`. Over a full
deploy, 3 calls and a `findDeployedContract`, it saw only these:

```
Contract (new)                       new Contract(witnesses), done by compact-js createContract()
Contract.prototype                   (from construction)
instance.initialState                deploy only
instance.provableCircuits            read, and its keys enumerated (Object.keys)
instance.provableCircuits.<c>        read + hasOwn, for c in {bump, arith}
```

midnight-js never read `circuits`, `impureCircuits`, `witnesses`,
`pureCircuits`, `ledger`, `expectedVk`, `circuitSignatures` or
`declaredInterfaces` on this path. `ledger()` is only needed by the
application, here to decode the state read back from the indexer. The adapter
supplies a generic one.

### Contracts on those members *(read in source, consistent with what ran)*

* **The container, not the instance.** You pass
  `CompiledContract.make(tag, ContractClass)` piped through
  `withWitnesses(w)` (or `withVacantWitnesses`) and
  `withCompiledFileAssets(dir)`. midnight-js tells the eras apart by shape: an
  object with no own `impureCircuits` and a string `tag` is a ledger-9
  container. A raw instance whose `initialState` is an `async function` is
  refused as `unwrapped-ledger9-contract`. A raw instance with a plain
  `function` `initialState` is routed to the ledger-8 path.
* **`new ctor(witnesses)`** must not throw for the witnesses supplied.
* **`initialState(constructorContext, ...args)`** may be sync or async. It must
  return
  `{ currentContractState, currentPrivateState, currentZswapLocalState }`, where
  * `currentContractState` is a `ContractState` from **the same compact-runtime /
    onchain-runtime-v4 WASM instance** that midnight-js uses. midnight-js calls
    `.operation(c)` and `.setOperation(c, op)` on it to insert each verifier key,
    and sets `.maintenanceAuthority`. It must already hold an operation for every
    key of `provableCircuits`, or you get "Circuit 'c' is undefined for the given
    contract state".
  * `currentZswapLocalState` is in the encoded form that
    `decodeZswapLocalState` accepts.
* **`provableCircuits[c](circuitContext, ...args)`** is awaited. Its result is
  read as `{ result, context }`, and the context must carry
  `callProofDataTrace` (entries with `publicTranscript`,
  `initialQueryContext`, `finalQueryContext`, `circuitId`, `contractAddress` and
  the proof data), `callContext.currentPrivateState`,
  `callContext.currentZswapLocalState`, `events` and `gasCosts`. The executor
  already produces exactly this, via `copyCircuitContext` and
  `finalizeCallProofData` from compact-runtime 0.21.
* `Object.keys(provableCircuits)` is the list of circuits whose verifier keys
  get deployed. It must equal the set of `keys/<c>.verifier` files.

### Asset directory (`withCompiledFileAssets(dir)` and `NodeZkConfigProvider(dir)`)

```
dir/keys/<c>.prover
dir/keys/<c>.verifier
dir/zkir/<c>.bzkir                     (.zkir is not read)
dir/compiler/contract-manifest.json    integrity manifest (see below)
dir/compiler/contract-info.json        only `runtime-version` is read, as a fallback
```

* **Era detection.** midnight-js decides which ledger era a contract belongs to
  from the artifact's declared `runtime-version`. It reads that from the
  manifest first and from `contract-info.json` second. `0.21.0` places the
  contract on ledger 9. Without either file the deploy fails with
  `ZkArtifactContractInfoError`. Damp emits neither file.
* **Integrity.** `NodeZkConfigProvider`'s default `verify` mode is `'require'`.
  With no `compiler/contract-manifest.json` it throws `ZkArtifactIntegrityError`
  ("no ZK artifact manifest … was found"). Every key, ZKIR and contract-info
  file that is read must also appear in the manifest with the right size and
  sha-256. The format is compactc's: `manifest-version: "1"`, plus
  `{dir: {type:"directory", file: {type:"file", size, hash}}}`. The alternative
  would be to construct the provider with `{ verify: 'off' }`, which I avoided.
* The proof provider resolves key material by joining the **deployed** verifier
  key hash against the local bundles (`ZKConfigRegistry`). If the local
  `.verifier` differs from the one on chain, the call fails before proving:
  `ZKArtifactNotFoundError: No ZK artifact bundle matches the deployed verifier
  key`.

## The adapter (`src/damp-adapter.mjs`)

1. Copies `executor/src/executor.mjs` **verbatim** into the bundle
   (`build/damp-<name>/contract/executor.mjs`) and imports it from there. Its
   bare import `@midnight-ntwrk/compact-runtime` then resolves to
   `deploy/node_modules`, the single deduped copy that midnight-js also uses.
   Importing it in place would resolve to `executor/node_modules`, a second WASM
   instance. Its `ContractState` would then fail midnight-js's WASM setters, as
   compact-js's own comments warn ("expected instance of …"). I did not test the
   in-place import, so the failure itself was not observed.
2. Copies `keys/` and `zkir/`. Writes `compiler/contract-info.json`
   (`runtime-version: "0.21.0"`, `compiler-version: "damp"`) and a
   `compiler/contract-manifest.json` hashing every file it ships.
3. `class Contract { constructor(w) { return makeContract(spec, w); } }`. This
   needs no executor change: `makeContract` already returns
   `{witnesses, circuits, impureCircuits, provableCircuits, initialState}`.
4. `ledger(state)` is generic over `contract.json`'s `ledger` list. It handles
   `counter` and `cell` of field, uint, bool and bytes. Composite cells, maps and
   sets are returned raw.

That is the whole gap. **The executor needed no changes.**

## Obstacles hit, and other observations

* **Finding the current local-network recipe.** `midnightntwrk/midnight-local-dev`
  is archived and points to `midnightntwrk/midnight-examples`. That repo's
  `toolchain.json` is the source of truth for the versions (midnight-js 5.0.0,
  node 2.1.101, indexer 4.4.101, proof server 9.0.0, compactc 0.36.0 and
  language 0.28). `example-counter` is archived too. compactc 0.36.1 artifacts
  (runtime 0.21.0) work with this toolchain unchanged.
* **Proof server self-verification.** The proof server checks the proof it makes
  against the verifier key it is sent, so a key mismatch fails at `/prove` with
  `400` ("self-verification failed! … check that your keys match!"). Reaching the
  node with a valid proof against a wrong on-chain key needs a custom
  `ZKConfigRegistry`, which `src/checks.mjs` B2 provides.
* **Two `/prove` requests per call** in the proof-server log (about 0.05 s and
  0.23 s). *(inferred)* One is the contract call and the other is the
  wallet's DUST-fee proof. The first request uses k=9 public parameters, which
  are downloaded from `srs.midnight.network` and logged as "verified correct".
* **Runtime pin.** midnight-js-protocol 5.0.0 pins compact-runtime **0.21.0**
  exactly and onchain-runtime-v4 at 4.0.0 (overridden to 4.0.0, as
  midnight-examples does). `executor/package.json` resolves onchain-runtime-v4
  4.0.2. That made no difference here, because the executor ran against the
  deploy project's 4.0.0.
* The indexer reports the contract state with a `midnight:contract-state[v8]`
  serialization header, even though midnight-js tags the state era `v9` and
  deserializes it with ledger-9's `ContractState`. *(not investigated)*
* npm skipped 5 install scripts (allowScripts policy). The prebuilt binaries
  were enough: `classic-level` loads. The wallet syncs to the local chain in
  about 30 s. DUST is spendable at once on the genesis wallet
  (`1.25e24` specks).
* Node 26.13.1 was used, while upstream pins Node 22. I saw no problems.
* `@midnight-ntwrk/midnight-js-level-private-state-provider` is in
  `package.json` but unused. The scripts use testkit's
  `inMemoryPrivateStateProvider`.

## Tokens

`node src/tokens.mjs` (log: `out/tokens.log`, summary: `out/tokens-result.json`)
deploys the Damp `tokens` contract (`Examples/Tokens.lean`, built into
`../build/oracle-tok/lean/tokens` by `DAMP_OUT=build/oracle-tok ./test/all.sh`),
packaged with `executor/src/package.mjs` and loaded with no adapter, and calls
it through midnight-js 5.0.0 with real proofs. Network brought up fresh with
`docker compose -p damp-local -f compose.yml up -d --wait` and taken down
after. Observed, 2026-11-16:

* **Deploying all 20 circuits fails**: the node refuses the deploy
  transaction with `RpcError: 1010: Invalid Transaction: Transaction would
  exhaust the block limits` (20 verifier keys in one transaction). The script
  therefore deploys the contract with only the circuits it calls (the same
  `contract.json` with the other circuits left out, as
  `contract tokens exports …` would build it; `TOKENS_CIRCUITS` selects them).
  With 3 circuits and with 8 circuits the deploy went through.
* Second run, 8 circuits (`whoami, mint, mintU, deposit, mintSelf, mintUTo, sendU, balU`),
  wallet = genesis seed `00…01`, coin public key
  `1bd4f827be97ff013c4a702e4b08f30ec378728a54670cf7cc92cb9b1a14eff6`,
  unshielded address `bc610dd0…37284b`
  (`mn_addr_undeployed1h3ssm5ru2t6eqy4g3she78zlxn96e36ms6pq996aduvmateh9p9sk96u7s`):

```
DEPLOYED address=cc9bacac0a75f8a0eb1c989e6dafdabf168b6f58d09c048c016b5a5e9ff8d8eb block=40
expected shielded token type   tokenType("damp:token", self) = 3b359946c4803c096cc5b172dc8e72aab8924683c422c2d105746e311a59bf8a
expected unshielded token type tokenType("damp:u", self)     = ef3394b1ab24ddf406fac20d88736fdcd09d075a37c8fb852ac80376661f73fc
CALL whoami   result={"bytes":"1bd4f827be97ff013c4a702e4b08f30ec378728a54670cf7cc92cb9b1a14eff6"} block=43 status=SucceedEntirely
CALL mint     (1000, nonce, wallet coin pk)                      block=46 status=SucceedEntirely
CALL mintU    (500, wallet user address)                         block=49 status=SucceedEntirely
CALL deposit  ({random nonce, color 3b35…bf8a, value 100})       block=52 status=SucceedEntirely
CALL mintSelf (50, nonce)                                        block=55 status=SucceedEntirely
CALL mintUTo  (40, left(self))                                   block=58 status=SucceedEntirely
CALL sendU    (15, right(wallet user address))                   block=61 status=SucceedEntirely
CALL balU     result="25"                                        block=64 status=SucceedEntirely
ledger (indexer): last={nonce 6e00…0032, color 3b35…bf8a, value 50}, color=ef33…73fc, owner=1bd4…eff6
contract balance (indexer contract state): [[{"tag":"unshielded","raw":"ef3394b1…73fc"},"25"]]
wallet shielded balance of 3b359946…bf8a: 900
wallet unshielded balance of ef3394b1…73fc: 515
```

  The wallet's shielded balances before the run held only the genesis tokens
  (`00…00`, `00…01`, `00…02`) and the `9d3dda…e503` token of the first run.
  After it: `3b35…bf8a: 900` (1000 minted to it, then 100 of them sent to the
  contract by `deposit`: the wallet balanced the contract's Zswap output by
  spending its 1000 coin and taking 900 change) and unshielded
  `ef33…73fc: 515` (500 minted to it plus 15 the contract sent it). The
  contract's unshielded balance on chain is 25 (40 minted to itself, 15 sent),
  which `balU` also returned (it reads the balance at the start of its
  transaction). `whoami` (the built-in `ownPublicKey`) returned the wallet's
  own coin public key. `mintSelf`'s coin (50) went to the contract; its
  `last` cell shows it, but nothing reads shielded coins held by a contract
  here.
* First run (3 circuits: `whoami, mint, mintU`): deployed `ecb09aa1…f4ca` at
  block 20; `whoami`, `mint(1000, …)`, `mintU(500, …)` at blocks 23, 26, 29,
  all `SucceedEntirely`; the wallet then showed shielded
  `9d3ddad005404f0e1455421a08f730648aea57a8de3f9310b9c1bb7baca6e503: 1000` and
  unshielded `9861540174e26e6401c6de147d0343d2c7e8f9fafb64aba9b70e4e418dbbff94: 500`,
  each the `tokenType` of that contract.

So the Zswap inputs and outputs the executor's built-in witnesses record are
what midnight-js and the wallet need: midnight-js turned them into the
transaction's Zswap part, the wallet balanced it (spending its own coin for
`deposit`), the node accepted the proofs and claims, and the wallet received
the coins. Not tried on chain: `sendShielded`, `mergeCoin` and their
immediate forms (the contract would need a `QualifiedShieldedCoinInfo` with
the real Merkle-tree index of a coin it holds, which needs `writeCoin`, not
ported), `evolve`, burning, and the balance comparisons.

## Holding a coin: `writeCoin`, then spending it

`node src/hold.mjs` (Damp's build) and `node src/hold.mjs compact` (compactc
0.36.1's build of the same four circuits, `deploy/hold.compact` →
`artifacts/compact-hold`; its verifier keys are byte-identical to those of the
same circuits in `test/oracle/tokens.compact`). Deployed circuits: `mint`,
`keep` (`receiveShielded` + `held.writeCoin`), `spend` (`sendShielded(held, …)`
+ `writeCoin` of the change), `mergeHeld` (`receiveShielded` +
`mergeCoinImmediate(held, coin)` + `writeCoin`). Wallet: genesis seed,
coin public key `1bd4f827…eff6`. Four runs on one fresh chain (logs
`out/hold-{damp,compact}-{1,2}.log`, summaries `out/hold-damp-1-result.json`,
`out/hold-damp-result.json`, `out/hold-compact-result.json`), then the network
was taken down.

What was observed, per step (indexer: the contract's `held` cell; wallet: its
shielded balance of the contract's token T):

| step | Damp run 1 | compactc run 1 | Damp run 2 | compactc run 2 |
|---|---|---|---|---|
| deploy | block 8 | block 53 | block 72 | block 88 |
| `mint(1000, …, wallet)` | ok, block 11; wallet T = 1000 | ok, block 56; 1000 | ok, block 75; 1000 | ok, block 91; 1000 |
| `keep({fresh, T, 300})` | ok, block 15; held = {value 300, **mt_index 30**}; wallet 700 | ok, block 59; held {300, mt_index 36}; 700 | ok, block 78; held {300, mt_index 39}; 700 | ok, block 94; held {300, mt_index 42}; 700 |
| `spend(left(wallet), 100)` | **rejected** | **rejected** | **rejected** | **rejected** |
| `mergeHeld({fresh, T, 50})` | ok, block 20; held = {value **350**, **mt_index 31**}; wallet 650 | **rejected** | **rejected** | **rejected** |

Every rejection is the same, at submission:
`RpcError: 1010: Invalid Transaction: Custom error: 104`, and the node logs
for each (all 7, verbatim apart from the hash):

```
🚫 Rejected transaction cb52a417…0e86 from mempool: guaranteed execution would fail: ran out of gas budget
```

Findings:

* **`writeCoin` works on chain.** After `keep`, the indexer shows the coin
  stored with an `mt_index` the ledger looked up when the transaction ran (30,
  36, 39, 42: global Zswap Merkle-tree indices; the local run had computed 0,
  its own call-local index, and the circuit commits to neither: there is no
  `popeq`). The wallet paid for the contract's Zswap output (1000 → 700).
* **Spending a stored coin works on chain at least once**: Damp run 1's
  `mergeHeld` spent the coin stored at index 30 (its nullifier, computed by
  the circuit from the stored `QualifiedShieldedCoinInfo`, was accepted), merged
  it with a fresh 50 coin and stored the 350 result at index 31; the wallet
  went 700 → 650.
* **`spend` (`sendShielded` of the stored coin) was rejected in all four runs,
  with compactc's own build exactly as with Damp's**, and `mergeHeld` was
  rejected in three of four, again for both builds. The node rejects the
  transaction because its guaranteed section runs out of the gas budget the
  transaction declares. The declared budget is computed off-chain by
  midnight-js / the ledger's transcript partitioning from the local run. The
  local gas costs of Damp's executor and compactc's module are identical for
  these calls (checked: `keep`, `spend`, `mergeHeld` give equal `gasCost`
  objects, e.g. `spend` `{readTime 340000000, computeTime 10301161279,
  bytesWritten 1750, bytesDeleted 1624}` from both). So this is not a Damp
  difference; it is a property of these transactions under midnight-js 5.0.0 /
  ledger 9 on this network. *(Not established: why the on-chain cost exceeds
  the declared budget, or why `mergeHeld` passed once.)* So
  "send part of a held coin back to the wallet with change" could not be
  observed on chain; nothing after `keep` changed the wallet or `held` except
  that one `mergeHeld`.

## Not covered

* Only `counter` and `vault` were tried on chain. `step`, `shapes`, `loops`,
  `bytes` and `extras` were not deployed. Their circuits go through the same
  executor paths that are checked locally.
* No pure-circuit call through midnight-js. `vault.digest` has no keys and
  midnight-js never asked for `pureCircuits`.
* Cross-contract calls and maintenance
  transactions (`submitInsertVerifierKeyTx` and the like) were not exercised.
* Only the Node `NodeZkConfigProvider` was used, not a browser or fetch provider.
