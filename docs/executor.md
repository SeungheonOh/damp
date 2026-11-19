# The executor and its definition

The JavaScript executor (`executor/src/executor.mjs`) runs a call on the
user's machine: it evaluates the circuit IR from `contract.json`, asks the
witnesses, runs the ledger instructions through `@midnight-ntwrk/compact-runtime`
and records the proof data. What it must do is **defined** in Lean by
`Damp.Exec.run` (`Damp/Executor/Spec.lean`), on top of `Expr.eval`, `Range.holds`
and `ledgerGroups` from `Damp/IR/Semantics.lean`; `Damp/Proofs/Executor.lean`
proves that every call this definition completes is accepted by the circuit.

That proof covers the JavaScript only as far as the JavaScript does what the
definition says. This document records how the two correspond, what was
changed to make them correspond, and how `test/executor.sh` checks it.

## Correspondence, clause by clause

The section "the definition" of `executor.mjs` mirrors the Lean. A Lean
`none` is a thrown `Failure`; evaluation is left to right through each `do`
block, so the first failure JS meets is the one Lean meets. Every case carries
a comment quoting the clause it mirrors.

| Lean | JavaScript |
|---|---|
| `asBool` (0 false, 1 true, else `none`) | `asBool` |
| `Zkir.fitsBits x n` (`n < 255 && x < 2^n`) | `fitsBits` |
| `Fr.ofInt` | `frOfInt` |
| `Expr.eval`: `var` (environment starts as `fun _ => 0`) | `evalExpr` `'var'`: unbound reads `0n` |
| `const`, `invalid`, `add`, `mul`, `neg`, `eq` | `evalExpr`, same cases; operands left to right |
| `lt bits a b`: both operands evaluated, then both must fit `bits` | `evalExpr` `'lt'` |
| `select c a b`: `c`, `a`, `b` all evaluated, then `asBool c` | `evalExpr` `'select'` |
| `hash xs` → `Prims.transientHash` | `transientHash` (runtime's Poseidon) |
| `phash high align xs` → `Prims.persistentHash` = SHA-256 of `Crypto.binaryRepr` (`parseAtom`: `compress` fails, `field` takes one element, `bytes n` takes `n/31` chunks below 2^248 plus a stray element below 2^(8·(n%31)), surplus ignored) → `bytesToNatives` → `[lo, hi]` | `evalExpr` `'phash'`, `parseAligned` (the same parse, building the AlignedValue the runtime hashes), `persistentHash`, `bytesToNatives` |
| `disclose e` | not in contract.json: `Export.expr` writes `e` |
| `Expr.evalList` | `evalList` |
| `Range.holds`: `zero`, `bool`, `bits n` (`fitsBits`), `below bound width` (`x` and `Fr.ofInt bound` fit `width`, `x < bound`) | `rangeHolds` |
| `bindInputs (fun _ => 0)`: counts must match | `bindInputs` |
| `Exec.assign`: per variable, range check then bind; counts must match | `assign` |
| `Op.mapM`, `Op.encode`, `atomCode` (Damp/IR/Impact.lean) | `mapOp`, `encodeOp`, `atomCode` |
| `Exec.blank`, `Exec.request` | `blank`, `request` |
| `ledgerGroups` | `ledgerGroups` |
| `Exec.step` `.bind`, `.assert`, `.constrain` | `step` `'bind'`, `'assert'`, `'constrain'` |
| `Exec.step` `.witness`: guard; nothing to read → done; `asBool`; active: args, `O.witness`, `assign outs vals`, `priv ++ vals`; inactive: `assign outs zeros` | `step` `'witness'` |
| `Exec.step` `.ledger`: guard; nothing to run → done; `asBool`; active: `request`, `O.ledger`, `assign reads vals`, `ledgerGroups … true` (with the reads bound); inactive: `assign reads zeros`, `ledgerGroups … false` | `step` `'ledger'` |
| `Exec.steps` | the loop in `execBody` |
| `Exec.run`: `bindInputs`, `steps`, `evalList outputs` | `execBody` |
| `Oracles.witness name argVals ω` | `oracles(…).witness`: the user's witness, its JS result converted to field elements; for a built-in witness, `builtinWitness` (below) |
| `Oracles.ledger req σ` | `oracles(…).ledger`: the instructions converted to runtime ops, `queryLedgerState`, the `popeq` results read back as field elements |

The private state `ω` and ledger state `σ` live in the runtime's circuit
context. An oracle returns its answer and a `commit` that installs the new
private state (and the transcript entry) once the statement has succeeded, as
the Lean step returns the new state only on success. A failed call never
reaches the caller's state: `runCircuit` works on a copy of the context.

Around `Exec.run` sit the boundary conversions, which the definition does not
describe (it takes and returns field elements): JS arguments to circuit
inputs (`flatten`, the runtime's type descriptors, `toFields`), JS witness
results to field elements, field-valued instructions to runtime ops
(`runtimeOp`, `alignedOfFields`), `popeq` results back to field elements
(`fieldsOfAligned`), and outputs to a JS result (`build`, `fromFields`).

### Built-in witnesses

`ownPublicKey`, `createZswapInput` and `createZswapOutput` (Compact's, used by
the token functions of `Damp/Lang/Tokens.lean`) are witnesses to the definition
like any other: `Exec.step` asks `O.witness` and records what it answers. The
executor answers them itself instead of calling a user function
(`builtinWitness`): the argument field elements are rebuilt into the JS
values the runtime expects, with the argument shapes fixed in the executor
(`QualifiedShieldedCoinInfo`; `ShieldedCoinInfo` and
`Either<ZswapCoinPublicKey, ContractAddress>`), and must convert back to
exactly the same elements; then, at commit (when the statement has
succeeded), `rt.createZswapInput(context, coin)` /
`rt.createZswapOutput(context, coin, recipient)` run on the call's context,
which extends `context.callContext.currentZswapLocalState` (and records the
output's commitment in the query context) as compactc's module does.
`ownPublicKey` answers `rt.ownPublicKey(context)`, the coin public key of the
Zswap local state. Each pushes its result's aligned value (empty for the two
`create*`) onto `privateTranscriptOutputs`, as compactc's module does. The
names are reserved: `makeContract` refuses user witnesses called so, and
`damp-dts` leaves them out of `Witnesses`. The trace records them as
witnesses (name, argument field elements, answer), so `test/executor.sh`
replays them through the definition like the rest; `test/all.sh` compares
the Zswap local state after every call with compactc's.

### Failure locations

A failed call throws a `CompactError` saying where and why:
`<circuit>: statement <i> (<kind>): <reason>`, `<circuit>: inputs: …`,
`<circuit>: outputs: …`, or a boundary stage, `arguments` (a JS argument is
not a value of its type) or `result` (the outputs are not a value of the
result type).

## The trace hook

`makeContract(spec, witnesses, { trace })`: when `trace` is given (it is off
by default), it is called with one record per circuit call, and one for the
constructor run by `initialState`, when the call completes or fails:

```
{ circuit,          // name; 'constructor' for the constructor
  inputs,           // circuit inputs as field elements (bigint[]); null, or null entries,
                    // where the arguments do not convert
  steps: [ { index, kind,                                 // each statement, as it starts
             witness?: { name, args, answer, error? },    // a witness was asked: its arguments
                                                          // and answer (field elements), or
                                                          // answer null and why it refused
             ledger?:  { request, answer, error? } } ],   // the ledger was asked: the
                                                          // instructions' public-input
                                                          // encoding (popeq results blank),
                                                          // and the field elements read
  groups,           // public inputs declared: [{ active, vals }]
  outputs,          // output field elements, or null
  failure,          // null, or { at, reason }; at = statement index, 'inputs', 'outputs',
                    // 'arguments', 'result' or 'runtime'
  proofData }       // the proof data recorded (partial on failure)
```

## Divergences found and fixed

Each is shown by a call in `test/executor.sh` (the label is the line it
prints). "Laxer" means the old JS completed calls the definition (and so the
circuit) rejects, producing proof data the prover refuses; "stricter" means
the old JS failed where the definition completes.

Expressions:

1. **Unbound variables.** The definition's environment starts at 0; the old
   JS threw. This matters for real circuits: `request` evaluates the operands
   of `popeq`, which are the very variables the read is about to bind
   (`counter.bump(12, true, false)` and 80 other calls fail if JS throws).
   The old JS never evaluated `popeq` operands at all. Case
   `synthetic 1: var_unbound`. (stricter)
2. **`select` evaluated only the chosen branch, and took any condition other
   than 1 as false.** Now all three operands are evaluated and the condition
   must be 0 or 1. Cases `synthetic 28/29: select on 2 / p-1`,
   `30: select_bad_else`, `31: select_bad_then`. (laxer)
3. **`lt` ignored its width.** Both operands must fit and the width must be
   below 255. Cases `synthetic 15–17, 20, 21`. (laxer)
4. **`phash` did not check that the elements fit the alignment.** Limbs too
   large for their bytes, a `compress` atom, or too few elements were hashed
   anyway; a zero-length bytes atom consumed an element (the definition
   consumes none) and then crashed on the next atom. Cases
   `synthetic 39, 40, 42, 43, 45, 46` (laxer), `48: phash_b0` (stricter).
5. **`invalid`** threw a plain `Error` with no location; it is now a located
   failure (same outcome).

Statements:

6. **Witness guard other than 0/1 was a silent skip.** It now fails when there
   is anything to read. Case `synthetic 83: w_ok: witness, guard 2`. (laxer)
7. **A witness with nothing to read was asked anyway** (when its guard was 1),
   with an empty transcript entry recorded. The definition does not ask it.
   Case `synthetic 85: w_none: … guard 1: not asked`. (different transcript)
8. **A skipped witness bound zeros without range checks.** Case
   `synthetic 82: w_skip_range`. (laxer)
9. **Witness results were not checked against `outs`**, neither the count nor
   the ranges (only the JS type descriptors). contract.json did not even
   carry the ranges. Cases `synthetic 77` (out of range), `79`, `80` (wrong
   count). (laxer)
10. **Ledger guard other than 0/1 was a silent skip.** Case
    `synthetic 98: ledger_guarded: ledger, guard 2`. (laxer)
11. **A skipped ledger statement did not evaluate its operands**, which the
    circuit does (it declares zeroed public inputs for them). Cases
    `synthetic 102, 103`. (laxer)
12. **A run ledger statement did not evaluate `popeq` operands**, neither in
    the request nor in the public inputs after the read is bound. Cases
    `synthetic 105: l_popeq_bad`, `107: l_popeq_late`. (laxer)
13. **`Range.holds`.** `bits n` accepted n ≥ 255; `below bound width` ignored
    the width (the bound and the value must both fit it), which was not in
    contract.json. Cases `synthetic 65, 70, 71, 72`. (laxer)
14. **Input count.** A circuit with more input variables than argument field
    elements left the extra ones unbound. Case `synthetic 112`. (laxer)
15. **`assert`** treated 0 and 2 alike; same outcome, the message now says
    which.

Boundary (not part of the definition, made to agree with it):

16. **Outputs not of the result type** (a Boolean output of 2, a bytes limb
    that does not fit) were silently converted (2 became `false`, limbs
    truncated), so the proof data claimed different outputs from those the
    circuit computes. The executor now requires the JS result to convert back
    to exactly the output field elements, and fails at `result` otherwise.
17. **Witness results that are not field elements** (negative or ≥ p values
    the descriptors let through) are now a refusal of the witness oracle.
18. The constructor body now records into proof data of its own (the field
    defaults are installed with a separate one), so its trace and preimage
    can be compared like any other call's.

The conformance test was itself checked by putting each old behaviour back
into a copy of the executor: every one of items 1–4, 6–14 (16 variants) makes
`test/executor.sh` report disagreements.

## contract.json format: `damp-contract/5`

`Export.range` now writes the comparison width of a `below` range
(`{"kind": "below", "bound": "21", "width": 6}`), and a witness's `outs` are
objects `{"var": n, "range": <range> | null}` instead of bare variable numbers.
The executor reads only `damp-contract/5`. The emitted `.zkir` files are
unchanged; `test/golden/*/contract.json` were regenerated. Copies of older
builds (e.g. `deploy/artifacts/`, format 4) must be rebuilt.

## The conformance test (`test/executor.sh`)

1. `lake exe damp-executor-test export build/executor` (`Test/Executor.lean`)
   writes `contract.json` for every example contract, optimized
   (`Contract.optimize`, then `Export.contract`, exactly what `Contract.build`
   writes), and for the synthetic contract, plus `synthetic.json`.
2. `executor/test/conformance.mjs` runs, with the trace hook on, every call of
   the call table shared with `executor/test/run.mjs` (`executor/test/calls.mjs`)
   plus three `tuned` calls, chained on each contract as `run.mjs` chains them,
   with the constructor; then every synthetic call. For a completed call it
   serializes the proof data with the runtime's own
   `proofDataIntoSerializedPreimage` and parses it with `preimage.mjs`
   (independently of Damp's encoder), and takes the runtime's field encoding
   of the result the same way.
3. `lake exe damp-executor-test check build/executor` replays every call
   through `Damp.Exec` with `Damp.Crypto.prims` (the real hashes) and scripted
   oracles that give back, in order, the witness and ledger answers JS
   recorded (`none` where JS's oracle refused). It runs `Exec.step` one
   statement at a time, logging every question the oracles are asked (also
   by a step that then fails), and `Exec.run` in one piece, which must agree.
   A call agrees when:
   * both complete, or both fail at the same place (statement index, inputs,
     outputs);
   * at every statement, the definition asks an oracle exactly when JS did,
     the same witness with the same arguments, or the ledger with the same
     instructions (public-input encoding of the blanked request); so a
     scripted oracle asked for an answer JS never produced is a disagreement;
   * on completion: the outputs equal JS's and the runtime's encoding of JS's
     result; the inputs equal the preimage's; the private transcript and the
     ledger reads equal the preimage's; the active groups' values equal the
     preimage's public-transcript inputs; the groups equal those JS computed;
     and no scripted answer is left unused;
   * for a synthetic call, the definition's outcome is the one the case was
     written for.

   Calls whose JS arguments are not values of their types never reach the
   definition (it takes field elements); where they have a field form, the
   definition must reject that too before asking any oracle (e.g.
   `shapes.move({x:5,y:300}, …)` fails at its input range check, statement 0).

It prints one `ok`/`FAIL` line per call, the clauses the synthetic calls
exercised (each statement form with its guard class, each expression form,
each range form, both succeeding and failing), and a summary; it exits
non-zero on any disagreement. Current result: 240 calls (125 on the example
contracts, 115 synthetic), all agree.

The synthetic contract (raw IR in `Test/Executor.lean`) has two Field cells
and a counter, and circuits that exercise every clause of `Exec.step` and
`Expr.eval` in succeeding and failing form: non-boolean guards with and
without anything to read, a guard that fails, skipped witnesses whose zero
fails its range, witness arguments that fail only when asked, witness
refusals, wrong result counts and shapes, skipped and run ledger statements
with failing operands (in the request, or only once the read is bound), a
read count mismatch, a ledger refusal, `select` with a failing unchosen
branch and on 2 and p−1, `lt` out of width and at widths 0, 254, 255, every
`Range` form on its boundary values, `assert` on 0, 1, 2, every hash
alignment case, input and output failures.

### What it does not cover

* **The boundary conversions** between JS values and field elements: of
  arguments, witness results, ledger instructions and `popeq` results, and
  outputs. The test takes JS's field elements as given. It does compare them
  with the runtime's own encoding where the runtime produces one (inputs,
  private transcript, ledger reads, public-transcript inputs, outputs), so a
  conversion that disagrees with the runtime is caught; one that agrees with
  the runtime but not with what the user meant is not.
* **The runtime itself**: that `queryLedgerState` runs the instructions as
  Midnight's ledger does, and that its hashes are the real ones (the latter is
  checked by `test/semantics.sh`).
* **The witnesses**: they are oracles. The scripted oracles replay what the
  JS witnesses answered. A JS witness also sees the current ledger state and
  contract address (the Lean `Oracles.witness` sees neither); any single run
  is still an instance of the definition for the oracle that answers what the
  witness answered, which is all the correctness theorem (quantified over all
  oracles) needs.
* Proof data finalization (`finalizeCallProofData`) and the shape of the
  returned object; `test/all.sh` checks the proof data against compactc's
  module and the ZKIR checker.

## Remarks on the Lean definition

Nothing in `Damp/Executor/Spec.lean` had to be worked around; the JS now does what
it says in every case tested. Three points worth knowing:

1. **A witness with nothing to read** is asked only when its guard is
   exactly 1, and must answer nothing; nothing is recorded in the private
   transcript by the definition (JS pushes the empty aligned value compactc
   pushes, which adds no field elements). `createZswapInput` and
   `createZswapOutput` are such witnesses: they exist for their effect on the
   Zswap local state.
2. **`request` evaluates the operands of `popeq` before the read binds them**
   (they are the read's own variables, so under the environment before the
   statement they are 0 or stale), and discards the values. If such an operand
   could fail on those values but not on the read values, the definition
   would fail a call the circuit accepts (the circuit evaluates them only
   after the read, in `ledgerGroups`). Damp only emits plain variables there,
   which cannot fail, so this is incompleteness in principle only. (It is also
   why unbound variables must read 0 in JS; see item 1 above.)
3. **The boundary is outside the definition.** `Exec.run` takes field
   elements and returns field elements; the JS also rejects arguments that are
   not values of their types (`arguments`) and outputs that are not values of
   the result type (`result`). The first is checked by the test to reject
   only what the definition rejects; the second cannot arise from circuits
   built by the `Contract` interface (outputs are values of the declared
   type), but the definition does not say so.
