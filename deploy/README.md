# deploy/: Damp contracts on a local Midnight network

This directory deploys and calls contracts on a local Midnight network (node,
indexer and proof server in Docker) through midnight-js 5.0.0, with real proofs.
It runs two builds of each contract:

* **baseline**: compactc 0.36.1's output (`contract/index.js`, `keys/`, `zkir/`, `compiler/`).
* **damp**: Damp's output (`contract.json`, `keys/`, `zkir/`), run by the
  generic executor `executor/src/executor.mjs` through a thin adapter
  (`src/damp-adapter.mjs`).

Status, 2026-11-16: everything below has run end to end. That covers deploying
the Damp `counter` and `vault`, calling their circuits, and reading the ledger
back from the indexer. Evidence is in [DEPLOY-NOTES.md](DEPLOY-NOTES.md) and in
`out/`.

## Versions

| component | version |
|---|---|
| node image | `midnightntwrk/midnight-node:2.1.101` (`CFG_PRESET=dev`, network id `undeployed`) |
| indexer image | `midnightntwrk/indexer-standalone:4.4.101` (GraphQL `/api/v4/graphql`) |
| proof server image | `midnightntwrk/proof-server:9.0.0` |
| midnight-js (`contracts`, `protocol`, `types`, `utils`, providers) | 5.0.0 (`network-id` 5.0.0-rc.5) |
| testkit-js | 5.0.0 |
| wallet SDK | `@midnightntwrk/wallet-sdk` 2.0.0 |
| compact-runtime | 0.21.0 (one deduped copy, shared by midnight-js, compactc's module and the executor) |
| onchain-runtime-v4 / ledger-v9 / zkir-v3 | 4.0.0 / 1.0.0 / 3.2.0 (npm overrides) |
| compactc (baseline artifacts) | 0.36.1, language 0.28.0 |
| Node | v26.13.1 (upstream pins Node 22; 26 worked) |

These pins are the ones in `toolchain.json` of
github.com/midnightntwrk/midnight-examples, the current official example repo
("Everything here targets Ledger 9"). The older `midnight-local-dev` repo is
archived and points there. `compose.yml` is that repo's
`examples/hello-world/compose.yml`, with `name: damp-local` added.

## Ports

The ports are bound to 127.0.0.1 only: node `9944`, indexer `8088` and proof
server `6300`. These are the upstream defaults, and they were free on this
machine. To move them, edit `compose.yml` and set `MN_NODE`, `MN_NODE_WS`,
`MN_INDEXER`, `MN_INDEXER_WS` and `MN_PROOF_SERVER` for the scripts.

## Rerun

```bash
cd deploy
npm install                       # once

# start the network (project name damp-local)
docker compose -p damp-local -f compose.yml up -d --wait

node src/run.mjs compact          # baseline: compactc counter, deploy + bump/bump/arith + read back
node src/run.mjs damp             # the same with the Damp counter (contract.json + executor)
node src/checks.mjs               # interop (compactc deploy, Damp calls) + negative controls
node src/vault.mjs damp           # Damp vault: constructor args, Bytes<32>, persistentHash witness
node src/vault.mjs compact        # baseline vault
node src/tokens.mjs               # Damp tokens: mint shielded/unshielded to the wallet, and more
                                  # (needs ../build/oracle-tok: DAMP_OUT=build/oracle-tok ../test/all.sh)

# or all of the above against a fresh chain (down, up, run everything; logs in out/)
./scripts/all.sh

# stop and remove the network (containers, network; the chain is not persisted)
docker compose -p damp-local -f compose.yml down
```

Each script takes about 1.5 to 3 minutes. Wallet sync takes about 30 s, and
each transaction about 18 s (prove, balance, submit, then wait for the block and
the indexer).

To use fresh compiler output, run `./scripts/refresh-artifacts.sh --oracle`.
It runs `../test/oracle.sh` and then copies `build/oracle/{lean,compact}/{counter,vault}`
into `artifacts/`. Leave out `--oracle` to copy without rebuilding. The adapter
copies the executor from `../executor/src/executor.mjs` each time it runs, so the
executor is always the current one. Set `DAMP_EXECUTOR=<path>` to use another
copy.

## Files

| path | what |
|---|---|
| `compose.yml` | the local network: node, indexer and proof server |
| `package.json` | the npm project. Pins midnight-js 5.0.0 and its toolchain, with the same overrides as midnight-examples |
| `src/common.mjs` | endpoints, the genesis wallet (seed `00…01`), providers, loading a contract flavour as a `CompiledContract`, reading the ledger back from the indexer |
| `src/damp-adapter.mjs` | **the adapter**. It turns a Damp build into the asset directory and contract class that midnight-js expects, and records every property midnight-js reads from the contract |
| `src/run.mjs` | deploys `counter` and calls `bump(5,true,false)`, `bump(7,true,true)` and `arith(4,4,100)`. Then it runs `findDeployedContract`, checks the final ledger `{count:12,total:97,cap:24}`, and writes `out/<mode>-result.json` |
| `src/checks.mjs` | A: deploys the compactc counter, then calls it through the Damp executor and back again. B: two negative controls with a wrong verifier key. B1 is rejected by the proof server and B2 by the node |
| `src/tokens.mjs` | the `tokens` contract (from `../build/oracle-tok`): `whoami`, shielded and unshielded mints to the wallet, a deposit the wallet pays for, mints to and an unshielded send from the contract; prints what the wallet and the indexer show (see "Tokens" in DEPLOY-NOTES.md) |
| `src/hold.mjs` | a contract holding a coin: `mint` to the wallet, `keep` (store a received coin with `writeCoin`), `spend` (`sendShielded` of it, change stored), `mergeHeld`; `node src/hold.mjs compact` runs compactc's build (`hold.compact`, `artifacts/compact-hold`) for comparison (see "Holding a coin" in DEPLOY-NOTES.md) |
| `src/vault.mjs` | the `vault` contract: deploy with constructor args `(persistentHash(key), 40)`, `spend(30)`, `spend(5)`, then `spend(6)`, which must fail with "over limit" |
| `scripts/all.sh` | runs everything against a fresh network |
| `scripts/refresh-artifacts.sh` | copies `../build/oracle` output into `artifacts/` |
| `artifacts/` | copies of `build/oracle/{lean,compact}/{counter,vault}` (taken 2026-11-16 16:27, format `damp-contract/4`) |
| `build/` | bundles the adapter generates. Throwaway: they are rebuilt on every run |
| `out/` | logs and `*-result.json` from the latest run |
| `DEPLOY-NOTES.md` | what midnight-js requires of a contract module, the obstacles, and the evidence |

## Packaged contracts

`node src/run.mjs packaged` deploys the counter from a directory produced by
`../executor/bin/damp-package.mjs`, loading `contract/index.js` directly with
no adapter. `node src/more.mjs` does the same for `extras` and `shapes`,
reading them from `../build/oracle-main/lean` (set `DAMP_OUT` to change).
The adapter in `src/damp-adapter.mjs` remains for the tracing and
negative-control scenarios.
