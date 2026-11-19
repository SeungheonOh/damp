# Cross-contract calls

A circuit of one contract calling a circuit of another, as Compact's contract
types allow, including nested calls (A calls B, B calls C) and, beyond Compact,
calls to a contract whose address is chosen at run time and cast to a contract
type. The pieces:

- `Damp/Lang/Calls.lean`: `Interface`, `ContractType`, `entryPoint`, `contractCall`;
  `Kernel.claimContractCall` in `Damp/Lang/Ledger.lean`;
- `interface T where …` in `Damp/Lang/Syntax.lean`; `contract` records the
  contract types in `Contract.interfaces` (`Damp/Compile/Export.lean`), written to
  `contract.json` as `interfaces` (only when there are some);
- the executor's call witness (`callWitness` in `executor/src/executor.mjs`),
  `contractModule`, `circuitSignatures`, `declarationOf`; `package.mjs` writes
  `circuitSignatures`, `expectedVk` and `declaredInterfaces` into
  `contract/index.js`;
- tests: `test/oracle/{adder,rich,caller,relay,top,picker}.compact` and
  `Examples/Calls.lean`, the call table in `executor/test/calls.mjs`, the
  simulated chain in `executor/test/world.mjs`, `deploy/src/calls.mjs`.

No IR form, no `Impact.Op` constructor and no proof file was added or changed.
Every encoding below was observed in compactc 0.36.1 output (`.zkir` and
`contract/index.js`), or in the runtime it calls (`@midnight-ntwrk/compact-runtime`
0.21.0, `dist/contract.js`); the 0.33 compiler source was read for intent only.

## Surface

```lean
interface Adder where
  addTo (x : Field) : Field
  clear : Unit

ledger
  adder : Cell Adder

constructor (a : Adder) := adder.write (disclose a)

circuit bump (x : Field) : Field := do
  const r ← (← adder.read).addTo (disclose x)
  return r
```

`interface T where` declares Compact's `contract T { circuit f(…): R; … }`:

- `T`, a structure with one field `bytes : Bytes 32`, shape
  `struct "T" ["bytes"] [bytes 32]` (in JS `{ bytes: Uint8Array(32) }`, as
  compactc's `_ContractAddress_0` descriptor). It is a circuit or constructor
  argument, a witness result, ledger content, and compares with `==.`;
- `T.f (self : T) (a : A) … : CircuitM R` per declared circuit;
- `T.declaration : Interface`, registered so that `contract` puts it into
  `contract.json`;
- `T.ofAddress : Bytes 32 → T`, `T.address : T → Bytes 32`, and an instance of
  `ContractType T` (`castContract T b`, `contractAddressOf r`): see "Casting an
  address".

## The mechanism, piece by piece

Evidence is `test/oracle/caller.compact` against `Examples/Caller` (in
`Examples/Calls.lean`); Damp's ZKIR below is `test/golden/caller/bump.zkir`,
instruction for instruction compactc's but for register names, and every
verifier key is byte-identical to compactc's.

### A contract value is its address

| Where | compactc 0.36.1 |
|---|---|
| ledger cell `adder: Adder` | read `0x30 | 0x50 0x01 0x01 0x00 | 0x0c 0x01 0x20 %t.1 %t.2`: alignment `bytes 32` |
| circuit argument `a: Adder` (`via`) | inputs `%a.0 %a.1`, `constrain_bits` 8 and 248: a `Bytes<32>` |
| JS | `a_0.bytes … length === 32`; `__compactRuntime.decodeContractAddress(….bytes)` gives the callee address |
| the claim | the address limbs as a `bytes 32` atom (below) |

### The call

```compact
const r = adder.addTo(disclose(x));
```

compactc (`caller/zkir/bump.zkir`) and Damp emit:

```
public_input %t.1 ; public_input %t.2            -- the reference, read from the ledger
impact 0x30 | 0x50 0x01 0x01 0x00 | 0x0c 0x01 0x20 %t.1 %t.2
private_input %r.3                                -- the callee's result
private_input %cc-rand.4                          -- the commitment's opening
transient_hash %comm.5 = [%cc-rand.4, %x.0, %r.3] -- opening, arguments, results
impact 0x40                                       -- swap 0: the effects to the top
impact 0x80 0x01 0x01 0x03                        -- idx cached pushPath [slot 3]: claimed contract calls
impact 0x30                                       -- dup 0
impact 0x04                                       -- size: the call's sequence number
impact 0x10 0x01 0x03 0x20 0x20 -0x02 %t.1 %t.2 0xdb 0x38e61d…ae5 %comm.5
                                                  -- push (address, entry point, commitment): [b32, b32, field]
impact 0x17 0xa0                                  -- concat cached 160
impact 0x10 0x00                                  -- push null
impact 0xa2                                       -- ins cached 2
impact 0x40                                       -- swap 0
```

The runtime's hand-written copy of the claim (`kernelClaimContractCall` in
`compact-runtime/dist/contract.js`) has the same nine instructions. All are
existing `Impact.Op`s (`size` and `concatCached` were there already), so the
claim is `Kernel.claimContractCall address entryPoint comm` in
`Damp/Lang/Ledger.lean`, an ordinary ledger statement that passes
`IR.Circuit.checkLedger`.

Damp (`contractCall`, `Damp/Lang/Calls.lean`):

| compactc | Damp IR |
|---|---|
| `private_input` results, `private_input cc-rand` | `witness guard "call:Adder.addTo" (address limbs ++ argument fields) outs (tuple [result, field])`: the results' variables with their ranges, then the opening's |
| `transient_hash [rand, args…, results…]` | `bind comm (hash (disclose rand :: args ++ results))` |
| the claim | `ledger guard [] (Kernel.claimContractCall …)` |

The witness's arguments are not emitted (witness arguments never are); they
are for the executor.

**Several values.** Arguments and results are flattened as everywhere else:
argument order, structure fields in order, `Bytes` as limbs, most significant
first. `fancy` calls `rich.mix(p: Pt, b: Bytes<32>, k: Uint<16>): [Pt, Bytes<32>]`:

```
private_input %…7                       -- q.x (Field: no check)
private_input %…8 ; constrain_bits 8    -- q.y
private_input %…9 ; constrain_bits 8    -- bb, top byte
private_input %…10; constrain_bits 248  -- bb, low 31 bytes
private_input %cc-rand.11
transient_hash [%cc-rand.11, %p.0, %p.1, %b.2, %b.3, %k.4, %…7, %…8, %…9, %…10]
```

So a call's results are range-checked like any witness result; Damp's
`askWitness (ρ × Field)` gives exactly these checks (the opening, a `Field`,
none). The runtime's `communicationCommitment(input, output, rand)` is
`transient_commit(ValueRepr(input ++ output), rand)` (`midnight-onchain-runtime`
`lib.rs`), i.e. the same hash of the callee's input and output field
elements: the test checks that every claimed commitment is
`communicationCommitment` of the callee's recorded input, output and opening.

**Under a condition** (`maybe`): the two `private_input`s and every `impact`
(the reference's read and the claim) are guarded by the condition; the
`transient_hash` is not. That is Damp's guarded witness (zeros when not
asked) and guarded ledger statement.

**Two calls** (`twice`): two complete copies; the reference is read twice
(`(← adder.read)` twice in Damp); the second claim's key gets the next
sequence number from `size`.

**Nested** (`top → relay → adder`): `relay`'s circuit contains its own call
in the same form; `top`'s circuit knows nothing of it.

**No arguments, no result** (`reset` calling `clear(): []`): one
`private_input` (the opening), `transient_hash [rand]`.

### The entry point

The second `bytes 32` of the claim names the circuit: the ledger's
`EntryPointBuf::ep_hash` (`midnight-onchain-state` 4.0.1, `state.rs`), a
`persistent_commit` of the name's bytes with opening
`"midnight:entry-point"` padded to 32 bytes, which is

    entryPoint(name) = SHA-256("midnight:entry-point" ‖ 0x00 × 12 ‖ UTF-8(name))

read as 32 bytes, first byte least significant (`Bytes.ofBytes 32`). Checked
against the runtime's `entryPointHash` and against every constant compactc
emitted:

| circuit | compactc's constant | SHA-256 above |
|---|---|---|
| `addTo` | `0xdb 0x38e61d549e290af27aa4ea370cf78dd3a2dfa9ff73fe6cf7826f7a50a69ae5` | `38e61d54…a69ae5db` |
| `clear` | `0x04 0x7f0341be537129141fc2f010ba438505a1b41b92b146bb85e40873d1fed1bc` | (verifier keys equal) |
| `mix` | `0x92 0xc19efc9bc7c1a6be…b41470` | (verifier keys equal) |
| `relay` | `0x95 0x318bf152e6e6dc65…eb068c` | (verifier keys equal) |

Damp computes it while the circuit is built, with `Damp/Crypto/Sha256.lean`.

## The JavaScript side

compactc's module makes the call with

```js
const r_0 = await __compactRuntime.crossContractCall({
  context, interfaceName: 'Adder', declaration: declaredInterfaces['Adder'],
  calleeCircuitId: 'addTo', calleeAddress: decodeContractAddress(<reference>.bytes),
  partialProofData, args: [x_0] });
```

and exports `circuitSignatures` (per circuit `{pure, provable, argumentTypes,
resultType}`), `declaredInterfaces` and `expectedVk` (per provable circuit, the
SHA-256 of `keys/<circuit>.verifier` in lowercase hex; `{}` with `--skip-zk`).
compactc 0.36.1's output has no `contractReferenceLocations` (the 0.33 source
has it, for finding references at static ledger locations); runtime 0.21.0 does
not use one.

`crossContractCall` (runtime 0.21.0): checks the circuit is declared; refuses
the default address; asks `context.moduleProvider.resolve(address)` for the
module and `context.stateProvider.getContractState(parentBlockHash, address)`
for the deployed state; refuses re-entry (`activeContracts`); checks the
module against the declared contract type (`checkConformance`: every declared
circuit exists, is provable, and has exactly the declared argument and result
types); checks the **verifier-key guard**: the deployed operation must have a
verifier key and its SHA-256 must equal the module's `expectedVk` for the called
circuit, and for every other circuit both sides have; then runs the callee's
`provableCircuits[c]` on a fresh query context for that address (with witnesses
that throw: a callee may not call witnesses), samples the opening, pushes the
callee's output and the opening onto the caller's `privateTranscriptOutputs`,
and runs the claim on the caller's query context. The callee's proof data,
with `commCommData {commComm, commCommRand}`, goes onto
`context.callProofDataTrace`, callees before their caller.

### Damp's executor

To the definition (`Damp/Executor/Spec.lean`, unchanged) the call is a witness:
`Exec.step` asks `O.witness "call:Adder.addTo" args` and gets the result's
field elements and the opening. The executor answers it (`callWitness`):

1. rebuilds the address and the JS arguments from the field elements with the
   declared shapes (they must convert back to exactly those elements);
2. calls `rt.crossContractCall` with the contract type from `contract.json`
   (`declarationOf` gives the runtime's `InterfaceDescriptor`), on the call's
   context, with a scratch proof-data object;
3. undoes the claim the runtime just made on the caller's query context (it
   restores the caller's query context, gas cost and their per-address cells
   from before the call): the circuit's own ledger statement makes the claim
   next, with the same instructions and operands, so the transcript and state
   are the runtime's;
4. answers with the result's field elements (checked to be the callee's
   recorded output) and the opening; when the statement commits, pushes the
   two aligned values the runtime recorded.

The callee is whatever the module provider returns: a compactc module, a Damp
contract packaged by `package.mjs` (its `contract/index.js` now exports
`circuitSignatures`, `expectedVk` from its keys, and `declaredInterfaces`), or a
`contract.json` given to `contractModule(spec, expectedVk)`. Implementations are
supplied as midnight-js supplies them: a `ContractModuleProvider` from address
to module, and a `ContractStateProvider` (midnight-js reads it from the indexer).
`executor/test/world.mjs` has `directoryModuleProvider(root, names)`, which
follows compactc's documented convention (`<root>/<T>/contract/index.js`).
The runner became `async` (`step`, `execBody`), since the runtime's call is.

`makeContract` refuses user witnesses named `call:…`; `damp-dts` leaves them
out of `Witnesses`. A Damp enum shape has no names, so a signature with an enum
is written `{tag: 'Enum', name: 'enum', elements: ['0', …]}`: it conforms to a
Damp contract's, not to compactc's.

## Casting an address

Damp, unlike Compact, converts any `Bytes 32` to any contract type and back:
`Adder.ofAddress b`, `castContract Adder b`, `r.address`. Since a contract value
*is* its 32-byte address in all three places compactc uses it (table above),
the cast is free: no instruction, no check. So the callee can come from a
circuit argument, a witness, a `Map` value, a hash or a constant, and one
address can be used as several contract types.

`test/oracle/picker.compact` vs `Examples/Picker` (verifier keys equal). Compact
cannot express the casts, so the oracle is the nearest Compact program, which
receives or stores the same bytes already contract-typed:

| Damp | compactc counterpart |
|---|---|
| `viaArg (a : Bytes 32)`: `(Adder.ofAddress (disclose a)).addTo …` | `viaArg(a: Adder, …)`: `disclose(a).addTo(…)` |
| `refs : Map Field (Bytes 32)`, `register (k) (a : Bytes 32)`, `viaMap`: `(Adder.ofAddress (← refs.lookup k)).addTo …` | `refs: Map<Field, Adder>`, `register(k, a: Adder)`, `refs.lookup(k).addTo(…)` |
| `both (a : Bytes 32)`: `Adder.ofAddress a` and `castContract Clearer a`, both called | `both(a: Full)`, `Full` declaring both circuits (the contract type's name is in neither circuit) |
| `wrongSig`: `Wrong.addTo (x : Uint16)` | `contract Wrong { circuit addTo(x: Uint<16>): Field; }` |

The JS arguments differ (`Uint8Array` against `{ bytes }`); the test passes
each implementation its own form, and everything else is compared as for the
other calls.

**Disclosure of a cast address.** The address is an operand of the claim, so a
private one (an argument, a witness result) needs `disclose`, exactly as compactc
demands of a contract-typed argument that is called ("contract call contract
reference might disclose the witness value"); a ledger value or a constant
needs nothing. `Examples/CallDiagnostics.castLeak` is the error.

**What resolves the callee.** Only the run-time address: `crossContractCall`
asks the module provider for that address and the state provider for that
address's deployed state. There is no static per-field location to consult and
none is needed: `expectedVk` is a property of the module, compared with the
verifier keys of the state deployed at the address. Checked before the callee
runs (off chain, by the runtime): that the address has a deployed state, that a
module is registered for it, that the module implements every circuit of the
contract type with exactly the declared types, and that its verifier key
fingerprints match the deployed keys. Observed failures (all fail identically
in compactc's module and Damp's executor):

| call | error |
|---|---|
| no module for the address (`ghost`) | `…could not be bound to an implementation: the module provider has no binding for this address.` |
| address of a contract without `addTo` (`rich`) | `…the resolved module does not implement the contract type: it does not implement circuit 'addTo'.` |
| `addTo` with another argument type (`wrongSig`) | `…circuit 'addTo' argument 0 has a different type.` |
| verifier key differs (`impostor`) | `…the verifier key for circuit 'addTo' is '0f0d…' in the resolved module but '…' on chain` |
| nothing deployed (`nobody`) | `Expected contract state for callee 'b2b2…' to be defined` |

**A cast is unchecked.** Nothing in the caller's circuit proves that the
contract at the address has the circuit, or the types. What happens on chain
when it does not: the caller's proof is valid regardless (it only claims
`(address, entryPoint, comm)` among the effects); the ledger's effects check
(`midnight-ledger` v9 `verify.rs`, `effects_check`: "Any claimed call must also
exist within the same segment", `RealCallsSubsetCheckFailure`) requires a call
in the same transaction with that address, entry-point hash and communication
commitment, and that call must carry a proof against the verifier key deployed
for that entry point at that address. If the contract has no such entry point,
no such call can be made and the transaction is rejected as malformed. If it
has one whose types differ, only field elements are compared: the callee's
proof commits to its own input and output field elements, so a call whose
field-element layout happens to coincide is accepted on chain with the values
reinterpreted. The runtime's conformance check refuses it before a
transaction is built, but that check is off chain.

## Disclosure

compactc 0.36.1's verdicts (one-circuit variants):

| Variant | compactc |
|---|---|
| `adder.addTo(x)`, `x` an argument | error: "contract call argument 1 might disclose the witness value" |
| `adder.addTo(w())` | error (same) |
| `a.addTo(…)`, `a: Adder` an argument | error: "contract call contract reference might disclose the witness value" |
| `if (go) { adder.addTo(…) }` | error: "making this contract call might disclose the boolean value of the witness value" |
| `last = adder.addTo(…)`, `return adder.addTo(…)`, `adder.addTo(adder.addTo(…))` | accepted |

Decision: a call's results are public (wrapped in `disclose` inside
`contractCall`, as `ownPublicKey`'s result is), and so is the opening; the
commitment is therefore tainted exactly by the arguments, and the claim's
operands by the arguments and the reference. Damp's check then demands
`disclose` exactly where compactc does: `Examples/CallDiagnostics` (`argLeak`,
`refLeak`, `condLeak`, `witnessArg`, `castLeak`; `resultPublic` and
`castConst` accepted). The messages are Damp's ("a ledger operation stores or
looks up a value that depends on argument `x`…").

## Tests

| Suite | What it adds |
|---|---|
| `DAMP_OUT=build/oracle-cc ./test/all.sh` | verifier keys of all 16 new circuits equal compactc's (`ok`); the calls of `executor/test/calls.mjs` in a simulated chain (`world.mjs`) in four set-ups: all Damp, all compactc, Damp callers with compactc callees, compactc callers with Damp callees loaded from `package.mjs` directories by compactc's `<root>/<T>/contract/index.js` convention. Per call: the proof data of the call and of every nested call (the whole `callProofDataTrace`) equal compactc's, results and every contract's Zswap local state equal, every trace entry (Damp's and compactc's) accepted by the ZKIR checker against the Damp circuit of its contract, a tampered value rejected; at the end the ledger state of every contract equal in all four; one real proof of `caller.bump` |
| `./test/executor.sh` | the calls replayed through `Damp.Exec`; a callee's run is traced and replayed as a call of its own (`… > adder.addTo (run 1 of 3)`) |
| `./test/golden.sh` | `test/golden/{adder,rich,caller,relay,top,picker}` added; no existing file changed |
| `./test/opt.sh`, `./test/semantics.sh` | the new circuits built both ways; round-tripped through the Lean ZKIR reader |

The opening is random, sampled by the runtime in every run, so the comparison
replaces it (and the commitment, which depends on it) by placeholders after
checking, in every run, that the claimed commitment is
`communicationCommitment(callee input, callee output, opening)` and that the
opening follows the callee's output among the caller's private outputs
(`normalizeTrace`). In the conformance test the deployed verifier keys are
stand-ins (the conformance build has no keys; the runtime only fingerprints
them).

Failing calls, each failing in every set-up: the callee's assert (`bump(13)`,
also as the second of two calls and innermost of a nested call), an argument
out of range (`fancy` with `y: 300`, refused at the caller's boundary), a
contract without the contract type, no implementation, a verifier key that
does not match, nothing deployed, and the `picker` cases above.

## What the theorems say about a call

`Exec.run_accepted` / `run_accepted_by_zkir` (`Damp/Proofs/Executor.lean`):
if the executor completes the caller's call, the caller's ZKIR accepts its
inputs with the private transcript the executor recorded, which includes the
callee's results and the opening, and yields the recorded public inputs, which
include the claim `(address, entryPoint, transient_hash [opening, args,
results])`. `run_groups_fromLedger` (`Damp/Proofs/LedgerAgreement.lean`): those public
inputs are the instructions sent to the ledger, the claim included.
`run_none`: the executor fails only where the definition must, the call
witness's refusal (a failed callee) being an oracle refusal. These hold for every
oracle, so for every answer a callee could give.

They say nothing about the callee: its run is not part of the caller's
statement. What ties the two together is on chain, outside Damp's proofs: the
callee's call in the same transaction carries its own proof, whose public
inputs include its communication commitment, which the callee's ZKIR (with
`do_communications_commitment`) requires to be `transientCommit(callee inputs
++ callee outputs, opening)` (`IrSource.preprocess`, TC2, in
`Damp/Zkir/Semantics.lean`); and the ledger's effects check requires every
claimed `(address, entry-point hash, commitment)` to be a call of the same
segment, after the caller (`call_sequencing_check`). Equal commitments mean,
under Poseidon's collision resistance, that the caller's arguments and results
are the callee's inputs and outputs. That last step is a cryptographic
assumption, not a theorem here.

## Limitations

From Compact and its runtime: a callee may not call witnesses (its witnesses
throw); no re-entry (a contract already on the call stack cannot be called
again); the callee runs on the caller's machine with code the caller supplies;
a call is all-or-nothing: if the callee fails, so does the caller.

Damp's own: an enum in a contract type's signature does not conform to a
compactc contract's (Damp's enum shape has no names); calls are not offered in
a constructor (the constructor context has no providers); Damp's error
messages differ from compactc's (the outcomes do not); the casts are unchecked
(above); `test/semantics.sh` round-trips the new circuits but its call table
(`semantics-vectors.mjs`) has no cross-contract calls.

## On the network

`deploy/src/calls.mjs` against the local network (midnight-js 5.0.0, real
proofs; logs and `out/calls-*-result.json`). midnight-js 5.0.0 supports
cross-contract calls: `providers.contractModuleProvider` (address → module)
and a `ZKConfigRegistry` behind the proof provider, which finds each call's
prover key by its verifier key's hash.

First attempt, with the registry also as `zkConfigProvider`:
`CALL caller.bump("5") FAILED: source.getArtifactRuntimeVersion is not a function`
(midnight-js reads the contract's runtime version from `zkConfigProvider`;
`ZKConfigRegistry` has no such method). With the caller's own
`NodeZkConfigProvider` as `zkConfigProvider` and the registry only behind
`httpClientProofProvider`, everything succeeded:

- **Simple.** `adder`, `rich`, `caller(adder, rich)` deployed; ledgers before:
  `{"adder":{"total":"0"},"caller":{…,"last":"0",…}}`.
  `CALL caller.bump("5") result="5" tx=56285acf…ec49 block=72 status=SucceedEntirely`;
  after: `{"adder":{"total":"5"},"caller":{…,"last":"5",…}}`. The indexer's
  latest action of each contract is a `ContractCall` in that transaction
  (`"entryPoint":"addTo"` for the adder, `"entryPoint":"bump"` for the caller),
  and the transaction shows `"status":"SUCCESS"` with two contract actions,
  `bump` on the caller and `addTo` on the adder.
- **Nested.** `relay(adder)`, `top(relay)` deployed;
  `CALL top.go("9") result="14" tx=bd1219fd…42d0 block=81 status=SucceedEntirely`
  (the adder held 5 from the simple call); ledgers after:
  `{"adder":{"total":"14"},"relay":{…,"hops":"1"},"top":{…,"got":"14"}}`; the
  transaction has three `ContractCall`s: `go`, `relay`, `addTo`.
- **A cast address.** `adder`, `picker` deployed. `picker.viaArg(<adder's
  address as 32 bytes>, 3)`: `result="3" … block=139 status=SucceedEntirely`;
  `register(1, <same bytes>)`: `block=142 status=SucceedEntirely`;
  `viaMap(1, 4)` (the address read from the `Map` and cast):
  `result="7" tx=2b200d05…2d08 block=145 status=SucceedEntirely`; the adder's
  ledger `{"total":"7"}`; the transaction shows `"status":"SUCCESS"` with
  `ContractCall`s `viaMap` on the picker and `addTo` on the adder.

The network was taken down afterwards (`docker compose -p damp-local -f
compose.yml down`).
