# Damp/ZkirSemantics.lean against the real ZKIR evaluator

`Damp/ZkirSemantics.lean` is a Lean port of `IrSource::preprocess` from
midnight-zkir 3.2.1 (`zkir/src/ir_vm.rs`): the function the proof server runs
to decide whether a call satisfies a circuit. Damp's correctness theorems are
stated against it. This document describes how it was made executable with
Midnight's real cryptography, how it is tested against the real evaluator, what
the test found, and what remains unvalidated.

Run it with `./test/semantics.sh` (about 30 s; `SEM_REUSE=1` skips rebuilding
the example contracts). It prints one `ok`/`FAIL` line per check and a
summary, and exits non-zero on any `FAIL`. Last run (2026-11-16):

```
crypto: 111 ok, 0 FAIL
zkir reader and round trip: 182 ok, 0 FAIL
vectors: 2725 ok, 0 FAIL
semantics: all 3018 checks passed
```

## 1. Discrepancies found, and the fixes

The test found three places where `Damp/ZkirSemantics.lean` disagreed with
the real evaluator, and one in the new JSON reader. **None of them affects a
circuit Damp emits**: every vector built from the example contracts agreed
before the fixes. All three are in circuits outside Damp's current output, and
were found with synthetic circuits (`synthetic edge` vectors). Each changed
line in `ZkirSemantics.lean` carries a comment starting
`-- checked against the real evaluator:`.

1. **`output` arity and types were not checked (Lean accepted, Midnight
   rejects).** The Rust `Output` case checks that the instruction lists exactly
   as many values as the circuit declares, and that each value's runtime type
   is the declared type. The Lean `output` step appended whatever it was given.
   Evidence: `output fewer than declared`, `output more than declared`,
   `output none, one declared`, `output a native where Bytes<32> is declared`;
   the real error is e.g. `Output: signature declares 2 return values but
   instruction has 1`. This is the soundness direction: a circuit with a
   mismatched `output` would have had preimages accepted by the Lean evaluator
   and rejected by the prover.
   *Fix:* `IrSource.outputsDeclared` (every `output` lists exactly the declared
   outputs, all declared native, since Lean's `output` only takes native
   values), required at the start of `IrSource.run`. The Rust checks each
   `output` when it runs it; as every instruction runs unless an earlier one
   fails, checking up front accepts and rejects the same preimages.
   (Two `output` instructions, and no `output` instruction at all, are
   accepted by both; vectors `two output instructions` and
   `no output instruction, one declared`.)
2. **`cond_select` between two byte strings (Midnight accepts, Lean
   rejected).** `select_offcircuit` (`ir_instructions/select.rs`) only requires
   both values to have the same `IrType`. Lean required native operands.
   *Fix:* native/native as before; two byte strings of the same length select
   one of them; anything else fails. Vectors: `cond_select between byte
   values` (accept), `cond_select between a byte value and a native` (reject).
3. **`test_eq` between two byte strings (Midnight accepts, Lean rejected).**
   `test_eq_offcircuit` (`ir_instructions/eq.rs`) compares two `Bytes` values
   (of any lengths). *Fix:* native/native as before; bytes/bytes give
   `Fr.ofBool (us = vs)`; mixed fails. Vectors: `test_eq between byte
   values` (accept), `test_eq between a byte value and a native` (reject).

The native cases of 2 and 3 are written exactly as before, so proofs about
emitted circuits only see an extra `resolve` step (`resolve_of_native`). Fix 1
adds the decidable side condition `src.outputsDeclared = true` to anything
proved about `IrSource.run`.

In the new reader (`Damp/ZkirJson.lean`), an immediate with more than 32 bytes
(`0x05` followed by 32 zero bytes) was accepted; the Rust loader rejects it,
because `Fr::from_le_bytes` takes at most 32 bytes. Fixed before release.

## 2. What is modelled

| | modelled | source |
|---|---|---|
| instructions | `assert`, `cond_select`, `constrain_bits`, `constrain_eq`, `constrain_to_boolean`, `copy`, `test_eq`, `add`, `mul`, `neg`, `not`, `less_than`, `transient_hash`, `persistent_hash`, `bytes_into_natives`, `private_input`, `public_input`, `impact`, `output` | `ir_vm.rs` `preprocess` |
| values | native field elements; byte strings (only `persistent_hash` makes them) | |
| checks after the run | transcripts used up (TC1), active-`impact` inputs equal the claimed public transcript inputs, communications commitment (TC2) | `ir_vm.rs` |
| `transient_hash` | Poseidon, `Damp/Crypto/Poseidon.lean` | see §3 |
| `transient_commit` | `transient_hash(opening :: values)` | transient-crypto 3.0.1 `hash.rs` |
| `persistent_hash` | `parse_field_repr`, `binary_repr`, SHA-256, `Damp/Crypto/Prims.lean` | see §3 |

Not modelled (the Lean evaluator rejects where the Rust may accept): every other
instruction (`inv`, `encode`, `div_mod_power_of_two`, `reconstitute_field`,
elliptic-curve and byte-string instructions, `bytes_from_natives`, ...), every
type other than `Scalar<BLS12-381>` for inputs, `private_input` and
`public_input`, and `Option` alignment segments (`Zkir.Alignment` has none).
The binding input is not modelled; `preprocess` only passes it through.

Two differences in *when* a failure is noticed, which never change the verdict:
the Rust compares each active `impact`'s inputs with the transcript as it runs
it, while `IrSource.preprocess` compares all of them after the run; and the
Rust checks that a commitment is present before running, Lean after. A
transcript that runs out makes the Rust index past the end of a slice and
panic (in wasm: `RuntimeError: unreachable`, which kills the process); Lean's
`readOne` fails. Both are rejections.

## 3. Cryptography (`Damp/Crypto/`)

All functions are total; `#print axioms Damp.Crypto.prims` lists only
`propext` and `Quot.sound`. The sources below were read in the crates in
`~/.cargo/registry` (the versions the installed npm packages are built from:
onchain-runtime 4.0.1 → midnight-transient-crypto 3.0.1 → midnight-circuits
^7.3.0; midnight-zkir 2.2.0 → the same) and in the midnight-zkir repository at
tag `zkir-3.2.1`. Every function is then checked against the JS runtime.

- **SHA-256** (`Sha256.lean`): FIPS 180-4. The 64 round constants and the
  initial hash value are *computed* from their definition (fractional parts of
  cube and square roots of the first primes), not typed in. Checked against
  Node's `crypto` on 18 lengths (0, 1, 3, 31, 32, 33, 55, 56, 57, 63, 64, 65,
  100, 119, 120, 128, 200, 1000 bytes).
- **Poseidon** (`Poseidon.lean`, constants in `PoseidonConstants.lean`):
  width 3, rate 2, 8 full and 60 partial rounds (`constants/mod.rs`); x^5
  S-box, applied to all cells in full rounds and to cell 2 in partial rounds;
  "shifted" rounds (add `ROUND_CONSTANTS[0]` first, then each round adds the
  next round's constants after the MDS product, zero after the last), as in
  `poseidon_cpu.rs` (`permutation_cpu`, `full_round_cpu`,
  `partial_round_cpu_raw`); the CPU code batches partial rounds and we
  implement the unbatched permutation. Sponge (`SpongeCPU for PoseidonChip`):
  state `[0, 0, len]`, inputs added two at a time into cells 0 and 1 (an odd
  last one into cell 0), permute after each chunk, output cell 0; no padding,
  and the empty input is never permuted (its hash is 0, which the runtime
  confirms). The 204 round constants and 9 MDS entries were extracted
  mechanically from `midnight-circuits-7.3.0/src/hash/poseidon/constants/blstrs.rs`
  (`Fq::from_raw([l0,l1,l2,l3])` = `l0 + l1·2^64 + l2·2^128 + l3·2^192`); the
  file is byte-identical to 6.3.0 apart from the copyright line.
- **transient_hash / transient_commit**: checked against the runtime's
  `transientHash` on 18 inputs (0 to 33 elements, zeros, `p-1`, random), against
  `communicationCommitment` on 15 (input, output, opening) triples (openings 0,
  1, random), against the real evaluator through `thash*` synthetic circuits
  (36 vectors), and implicitly by every contract vector, since the real
  communications commitment must open under Lean's `transientCommit` for an
  honest vector to be accepted.
- **persistent_hash** (`Prims.lean`): `Alignment::parse_field_repr`
  (transient-crypto `fab.rs`): atoms in order; `field` takes one element whose
  binary form is its 32 little-endian bytes; `bytes n` is
  `bytes_from_field_repr` (`repr.rs`): `n % 31` "stray" bytes from the first
  element (which must be below `2^(8·stray)`) become the *last* bytes, then
  `n / 31` elements below `2^248`, most significant chunk first; `compress`
  cannot be parsed. **Surplus elements are ignored** (upstream does not check
  that all are used; confirmed by the real evaluator: vectors `f on 1,2`,
  `b1 on 7,8,9`, `b32 on 3,4,5`, ` on 1`). Checked on 60 (alignment,
  value) pairs whose field form and digest both come from the runtime
  (alignments: `f`, `b1 b2 b8 b30 b31 b32 b33 b62 b63 b64 b100`, `f,f`,
  `b1,f,b32`, `b32,b32,b32`, `f,b33,b1,f`, `b64,f,b31`, empty, `b0`, `b0,f`;
  each with zero, all-0xff/`p-1` and random values), and through the real
  evaluator on the same 60 plus 14 non-fitting or surplus cases.

## 4. The JSON reader (`Damp/ZkirJson.lean`)

`IrSource.parse` reads the `.zkir` JSON Damp and compactc write. Operands follow
the Rust loader: `%name` is a register (`%hint.id`; other names are rejected,
because `Zkir.Ident` cannot represent them, though the Rust accepts any
`%...`), `0x`/`0X`/`-0x` + an even number of hex digits, at most 32 bytes,
little-endian, below the modulus, is an immediate. Tested by (a) parsing and
re-printing with `IrSource.toJson` every emitted `.zkir` (25 from Damp, which
must also pass `checkSingleAssignment`; 24 from compactc; 113 synthetic) and
comparing JSON values, and (b) 20 operand strings accepted or rejected by the
real `jsonIrToBinary`.

## 5. How the differential test works

`executor/test/semantics-vectors.mjs` (Node, run from `executor/`):

1. Runs 81 calls on the ten example contracts through the generic executor
   (`src/executor.mjs` on `contract.json`), chained as in `test/run.mjs`: the
   78 calls of `test/run.mjs` and three of `tuned.settle`. 68 succeed; 13 fail
   in JS.
2. For each successful call, serializes the proof data with the runtime's own
   `proofDataIntoSerializedPreimage` and parses the bytes
   (`executor/test/preimage.mjs`; layout from `ProofPreimage` in
   transient-crypto 3.0.1 and `ScaleBigInt` in midnight-serialize 1.2.1). This
   gives exactly what the real checker consumes: inputs, private transcript,
   public transcript outputs, public transcript inputs, and the communications
   commitment with its opening (the runtime uses opening 0). The codec is
   checked to reproduce the runtime's bytes exactly for every call.
   The expected outputs are the runtime's field form of the call's output
   value (obtained the same way, serializing it as a preimage input).
3. Derives tampered preimages: for each of the four streams, +1 at up to 12
   (inputs) or 5 positions, set to 2 (a boolean that is 2) and to `p-1`
   (exceeds every range) except for the public transcript inputs, drop the
   last entry, drop the first, append 0; the claimed output changed (the
   runtime recomputes the commitment); the opening +1. Identical preimages are
   dropped.
4. For each call that fails in JS, claims it anyway: its arguments in place of
   the inputs of the nearest successful call of the same circuit, with the
   runtime computing the commitment.
5. Adds synthetic circuits (written to `build/semantics/synthetic/`) for what
   the examples do not emit (`copy`, `not`, `constrain_eq` on natives and byte
   strings, negative immediates, `less_than`/`constrain_bits` at 8, 254 and
   255 bits, computed guards), for the hashes, and for the edge cases of §1.
6. Runs every preimage through the real `check` of `@midnightntwrk/zkir-v3`
   3.2.1 (`semantics-check.mjs`, in a child process that is restarted when a
   wasm panic kills it) and records the verdict, the error, and the
   per-`impact` skip list `check` returns.
7. Writes `build/semantics/vectors.json`.

`lake exe damp-semantics-test` (`Test/Semantics.lean`) then, per vector, parses
the circuit with `ZkirJson` and runs `IrSource.preprocess` with
`Damp.Crypto.prims`. A vector passes when:

- the real checker accepts ⇒ Lean accepts, with the same outputs (where
  known) and the same skip list (which `impact`s were guarded off and their
  widths);
- the real checker rejects ⇒ Lean rejects, for the same kind of reason. The
  reason is read from the Rust error message: `premise` (an instruction's
  premise: failed assertion, non-boolean, bit bound, alignment, a wasm panic
  from reading past a transcript), `pt-mismatch` (`Public transcript input
  mismatch for input N`; the index N must match too), `unconsumed`
  (`Transcripts not fully consumed`), `commitment` (`Communications commitment
  mismatch`), `inputs` (wrong number of inputs). On the Lean side a staged run
  built from the same definitions (`outputsDeclared`, `bindInputs`,
  `Instr.step`, `Outcome.activeInputs`, `transientCommit`) finds the first
  failure in the order the Rust checks; it must agree with `preprocess` on
  every vector (accept/reject and outcome), so it only adds the reason.

### How independent is the public transcript encoding?

The public transcript inputs come from the runtime: the Rust `Op` field
encoding inside onchain-runtime-v4's `proofDataIntoSerializedPreimage`, read
back by parsing its output bytes. Nothing in the vector generation imports or
reimplements `Damp/Impact.lean`; the only thing on the JS side that knows the
preimage format is the 80-line codec, which must round-trip the runtime's bytes
exactly. What is *not* independent of Damp: the transcript *operations* are
recorded by Damp's executor interpreting Damp's `contract.json`. To close that,
every call is also run on compactc's generated module for the equivalent
Compact source, and for all 65 calls that have one the proof data is
identical (the three `tuned` calls have no Compact counterpart). The honest
vectors are also run against compactc's own `.zkir` (65 more vectors, all
agree). The claims of failing calls use a small JS function mirroring the
executor's argument flattening, but there the real checker is the judge.

## 6. Coverage

Instructions run by the Lean evaluator over all vectors (successful steps, and
steps whose premise failed):

| instruction | ran | failed |
|---|---:|---:|
| `add` / `mul` / `neg` | 1330 / 192 / 86 | 2 / 0 / 0 |
| `assert` | 796 | 21 |
| `bytes_into_natives` | 1071 | 2 |
| `cond_select` | 3081 | 1 |
| `constrain_bits` | 5129 | 152 |
| `constrain_eq` | 156 | 80 |
| `constrain_to_boolean` | 1524 | 98 |
| `copy` | 15 | 0 |
| `impact` guard true / false | 42421 / 5933 | 1 |
| `less_than` | 895 | 6 |
| `not` | 6 | 1 |
| `output` | 601 | 5 |
| `persistent_hash` | 1096 | 10 |
| `private_input` no guard / true / false | 729 / 23 / 22 | 25 |
| `public_input` no guard / true / false | 3994 / 55 / 131 | 73 |
| `test_eq` | 991 | 1 |
| `transient_hash` | 176 | 1 |

Every instruction `Instr.step` handles is exercised in both directions, on all
ten example contracts (including the byte-string, hash, Map/Set/List/Merkle
and nested-ledger examples) and synthetic circuits. Not exercised:

- the `| _ => none` fallback (instructions not modelled; see §2), and
  `private_input`/`public_input`/inputs of non-native type;
- `bytesToNatives` on lengths other than 32 (only the persistent-hash digest
  reaches it); `cond_select` on byte strings of different lengths (no
  instruction in the model makes one);
- a circuit with a commitment and a preimage without one (the runtime always
  supplies it).

## 7. All vectors and outcomes

Per call (real outcome; the Lean evaluator agreed on every vector). An honest
call contributes two accepted vectors: against Damp's circuit and against
compactc's. Calls listed once at the end, with one vector, are the claims of
calls that fail in JS.

| group | vectors | accept | premise | pt-mismatch | unconsumed | commitment | inputs |
|---|---:|---:|---:|---:|---:|---:|---:|
| `step.step(5n, true, 42n)` | 29 | 2 | 5 | 12 | 3 | 4 | 3 |
| `step.step(5n, false, 42n)` | 26 | 2 | 4 | 10 | 3 | 4 | 3 |
| `counter.bump(12n, true, false)` | 29 | 2 | 6 | 13 | 3 | 2 | 3 |
| `counter.bump(12n, true, true)` | 28 | 2 | 6 | 12 | 3 | 2 | 3 |
| `counter.bump(12n, false, false)` | 30 | 2 | 6 | 11 | 3 | 5 | 3 |
| `counter.arith(4n, 4n, 100n)` | 34 | 2 | 7 | 17 | 3 | 2 | 3 |
| `shapes.move({x:5n,y:2n}, [1n,2n,3n], true, true)` | 49 | 2 | 13 | 26 | 3 | 2 | 3 |
| `shapes.move({x:5n,y:2n}, [1n,2n,3n], true, false)` | 50 | 2 | 13 | 27 | 3 | 2 | 3 |
| `shapes.move({x:5n,y:2n}, [1n,2n,3n], false, true)` | 50 | 2 | 13 | 26 | 3 | 3 | 3 |
| `shapes.pay(77n, 10n, 3n, 2n)` | 38 | 2 | 4 | 23 | 3 | 3 | 3 |
| `shapes.pay(77n, 5n, 2n, 2n)` | 39 | 2 | 4 | 24 | 3 | 3 | 3 |
| `shapes.pay(78n, 1n, 7n, 9n)` | 38 | 2 | 4 | 23 | 3 | 3 | 3 |
| `shapes.pay(77n, 1n, 7n, 9n)` | 41 | 2 | 4 | 26 | 3 | 3 | 3 |
| `loops.tally([1n,2n,3n,4n], [true,false,true,true], 3n)` | 43 | 2 | 10 | 19 | 3 | 6 | 3 |
| `loops.tally([1n,2n,3n,4n], [false,true,false,false], 200n)` | 45 | 2 | 10 | 16 | 3 | 11 | 3 |
| `bytes.claim(0x61646d696e000000000000000000000000000000000000000000000000000000, 0x0300000000000004, true)` | 50 | 2 | 14 | 26 | 3 | 2 | 3 |
| `bytes.claim(0x61646d696e000000000000000000000000000000000000000000000000000000, 0x0500000000000006, false)` | 51 | 2 | 14 | 25 | 3 | 4 | 3 |
| `bytes.store(0x090000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c8, 12345n)` | 46 | 2 | 4 | 29 | 3 | 5 | 3 |
| `extras.advance(0, 0x0100000000000000000000000000000000000000000000000000000000000001, {is_some:true,value:500n}, 42n)` | 55 | 2 | 11 | 33 | 3 | 3 | 3 |
| `extras.advance(1, 0x0200000000000000000000000000000000000000000000000000000000000002, {is_some:true,value:50n}, 43n)` | 53 | 2 | 11 | 32 | 3 | 2 | 3 |
| `extras.advance(2, 0x0300000000000000000000000000000000000000000000000000000000000003, {is_some:false,value:0n}, 44n)` | 57 | 2 | 12 | 34 | 3 | 3 | 3 |
| `vault.spend(30n)` | 40 | 2 | 10 | 22 | 3 | 1 | 2 |
| `vault.spend(5n)` | 40 | 2 | 10 | 22 | 3 | 1 | 2 |
| `structures.tick(5n, 10n, false)` | 29 | 2 | 5 | 14 | 3 | 2 | 3 |
| `structures.tick(3n, 2n, false)` | 29 | 2 | 5 | 14 | 3 | 2 | 3 |
| `structures.tick(1n, 100n, true)` | 27 | 2 | 5 | 12 | 3 | 2 | 3 |
| `structures.books(7n, false)` | 26 | 2 | 4 | 12 | 3 | 2 | 3 |
| `structures.books(8n, false)` | 26 | 2 | 4 | 12 | 3 | 2 | 3 |
| `structures.books(9n, true)` | 26 | 2 | 4 | 12 | 3 | 2 | 3 |
| `structures.dequeue()` | 83 | 6 | 3 | 56 | 9 | 6 | 3 |
| `structures.enqueue(11n)` | 26 | 2 | 2 | 15 | 3 | 2 | 2 |
| `structures.enqueue(0n)` | 26 | 2 | 2 | 15 | 3 | 2 | 2 |
| `structures.enqueue(5n)` | 26 | 2 | 2 | 15 | 3 | 2 | 2 |
| `structures.enqueue(6n)` | 26 | 2 | 2 | 15 | 3 | 2 | 2 |
| `structures.plant(1n, 2n, 3n, 0x0400000000000000000000000000000000000000000000000000000000000005)` | 34 | 2 | 4 | 20 | 3 | 2 | 3 |
| `structures.check({field:46227755578962070530021234086654678295147756904630879000591234257058380984941n}, false)` | 26 | 2 | 3 | 13 | 3 | 2 | 3 |
| `structures.check({field:123n}, true)` | 26 | 2 | 3 | 13 | 3 | 2 | 3 |
| `structures.record(0x0100000000000000000000000000000000000000000000000000000000000002, 0x0300000000000000000000000000000000000000000000000000000000000004, 0x0500000000000000000000000000000000000000000000000000000000000006, 2n, {field:0n}, 0n)` | 48 | 2 | 9 | 29 | 3 | 2 | 3 |
| `structures.record(0x0700000000000000000000000000000000000000000000000000000000000008, 0x090000000000000000000000000000000000000000000000000000000000000a, 0x0b0000000000000000000000000000000000000000000000000000000000000c, 5n, {field:17725500008396664845907317580540913870374792085890828118332492183615453358988n}, 1n)` | 50 | 2 | 9 | 31 | 3 | 2 | 3 |
| `structures.record(0x0100000000000000000000000000000000000000000000000000000000000002, 0x0300000000000000000000000000000000000000000000000000000000000004, 0x0500000000000000000000000000000000000000000000000000000000000006, 2n, {field:99n}, 2n)` | 47 | 2 | 9 | 27 | 4 | 2 | 3 |
| `structures.stamp(0n)` | 35 | 2 | 2 | 24 | 3 | 2 | 2 |
| `structures.stamp(5n)` | 35 | 2 | 2 | 24 | 3 | 2 | 2 |
| `structures_nested.vote(1n, 5n)` | 30 | 2 | 2 | 18 | 3 | 2 | 3 |
| `structures_nested.vote(1n, 2n)` | 28 | 2 | 2 | 16 | 3 | 2 | 3 |
| `structures_nested.group(7n, 1n, 5n, false)` | 81 | 4 | 10 | 51 | 6 | 4 | 6 |
| `structures_nested.group(7n, 2n, 100n, false)` | 40 | 2 | 5 | 25 | 3 | 2 | 3 |
| `structures_nested.group(7n, 1n, 100n, true)` | 38 | 2 | 5 | 23 | 3 | 2 | 3 |
| `structures_nested.group(7n, 2n, 100n, true)` | 36 | 2 | 5 | 21 | 3 | 2 | 3 |
| `structures_nested.join(1n, 10n, false)` | 35 | 2 | 3 | 22 | 3 | 2 | 3 |
| `structures_nested.join(1n, 11n, false)` | 34 | 2 | 3 | 21 | 3 | 2 | 3 |
| `structures_nested.join(2n, 12n, true)` | 34 | 2 | 3 | 21 | 3 | 2 | 3 |
| `structures_nested.enqueue(1n, 10n)` | 37 | 2 | 1 | 26 | 3 | 2 | 3 |
| `structures_nested.enqueue(1n, 11n)` | 36 | 2 | 1 | 25 | 3 | 2 | 3 |
| `structures_nested.enqueue(1n, 12n)` | 37 | 2 | 1 | 26 | 3 | 2 | 3 |
| `structures_nested.enqueue(2n, 13n)` | 37 | 2 | 1 | 26 | 3 | 2 | 3 |
| `structures_nested.grow(1n, 10n, 5n, {field:0n}, false)` | 41 | 2 | 4 | 27 | 3 | 2 | 3 |
| `structures_nested.grow(1n, 20n, 6n, {field:22848759037293111850993476735400520139006979805121140794926791058038014516973n}, false)` | 41 | 2 | 4 | 27 | 3 | 2 | 3 |
| `structures_nested.grow(1n, 30n, 7n, {field:0n}, true)` | 40 | 2 | 4 | 26 | 3 | 2 | 3 |
| `structures_nested.hgrow(1n, 10n, 5n, {field:0n}, 0n)` | 41 | 2 | 3 | 28 | 3 | 2 | 3 |
| `structures_nested.hgrow(1n, 20n, 6n, {field:22848759037293111850993476735400520139006979805121140794926791058038014516973n}, 0n)` | 40 | 2 | 3 | 27 | 3 | 2 | 3 |
| `structures_nested.hgrow(1n, 30n, 7n, {field:26951516758127656632269013558006885550593935781507401730922620441161191373969n}, 1n)` | 39 | 2 | 3 | 26 | 3 | 2 | 3 |
| `structures_nested.hgrow(1n, 40n, 8n, {field:0n}, 2n)` | 40 | 2 | 3 | 26 | 4 | 2 | 3 |
| `tuned.settle([1n,2n,3n,4n], true)` | 32 | 1 | 7 | 15 | 3 | 3 | 3 |
| `tuned.settle([100n,2000n,30n,4n], false)` | 35 | 1 | 7 | 17 | 3 | 4 | 3 |
| `tuned.settle([65535n,65535n,65535n,65535n], true)` | 34 | 1 | 11 | 13 | 3 | 3 | 3 |
| `step.step(5n, true, 5000n)` | 1 |  | 1 |  |  |  |  |
| `counter.bump(600n, true, false)` | 1 |  |  | 1 |  |  |  |
| `counter.arith(9n, 4n, 100n)` | 1 |  |  | 1 |  |  |  |
| `counter.arith(3n, 4n, 100n)` | 1 |  | 1 |  |  |  |  |
| `shapes.move({x:5n,y:300n}, [1n,2n,3n], true, true)` | 1 |  | 1 |  |  |  |  |
| `bytes.claim(0x0100000000000000000000000000000000000000000000000000000000000002, 0x0300000000000004, true)` | 1 |  | 1 |  |  |  |  |
| `extras.advance(1, 0x0100000000000000000000000000000000000000000000000000000000000001, {is_some:true,value:500n}, 42n)` | 1 | 1 |  |  |  |  |  |
| `extras.advance(0, 0x0400000000000000000000000000000000000000000000000000000000000004, {is_some:false,value:0n}, 45n)` | 1 |  |  | 1 |  |  |  |
| `vault.spend(6n)` | 1 |  |  | 1 |  |  |  |
| `structures.tick(0n, 1n, false)` | 1 |  |  | 1 |  |  |  |
| `structures.plant(6n, 7n, 16n, 0x0800000000000000000000000000000000000000000000000000000000000009)` | 1 |  |  | 1 |  |  |  |
| `structures_nested.vote(2n, 0n)` | 1 |  |  | 1 |  |  |  |
| `structures_nested.grow(1n, 30n, 16n, {field:0n}, false)` | 1 |  |  | 1 |  |  |  |
| `synthetic misc` | 8 | 4 | 2 |  |  | 1 | 1 |
| `synthetic mixed` | 2 |  | 2 |  |  |  |  |
| `synthetic bits8` | 5 | 3 | 2 |  |  |  |  |
| `synthetic bits254` | 4 | 2 | 2 |  |  |  |  |
| `synthetic bits255` | 1 |  | 1 |  |  |  |  |
| `synthetic guards` | 5 | 2 | 1 |  | 2 |  |  |
| `synthetic edge` | 19 | 7 | 12 |  |  |  |  |
| `synthetic transient_hash` | 36 | 18 | 18 |  |  |  |  |
| `synthetic persistent_hash` | 134 | 64 | 70 |  |  |  |  |
| **total** | 2725 | 234 | 479 | 1442 | 208 | 171 | 191 |

By kind of vector:

| kind | accept | premise | pt-mismatch | unconsumed | commitment | inputs |
|---|---:|---:|---:|---:|---:|---:|
| claim of a call that fails in JS | 1 | 4 | 8 |  |  |  |
| honest | 68 |  |  |  |  |  |
| honest, against the circuit compactc compiled | 65 |  |  |  |  |  |
| synthetic: bits254 | 2 | 2 |  |  |  |  |
| synthetic: bits255 |  | 1 |  |  |  |  |
| synthetic: bits8 | 3 | 2 |  |  |  |  |
| synthetic: edge | 7 | 12 |  |  |  |  |
| synthetic: guards | 2 | 1 |  | 2 |  |  |
| synthetic: misc | 4 | 2 |  |  | 1 | 1 |
| synthetic: mixed |  | 2 |  |  |  |  |
| synthetic: persistent_hash | 64 | 70 |  |  |  |  |
| synthetic: transient_hash | 18 | 18 |  |  |  |  |
| tamper: inputs append 0 |  |  |  |  |  | 68 |
| tamper: inputs drop first |  |  |  |  |  | 57 |
| tamper: inputs drop last |  |  |  |  |  | 65 |
| tamper: inputs[i]+1 |  | 35 | 195 | 2 | 21 |  |
| tamper: inputs[i]=2 |  | 30 | 127 |  | 10 |  |
| tamper: inputs[i]=p-1 |  | 178 | 70 |  | 5 |  |
| tamper: opening+1 |  |  |  |  | 68 |  |
| tamper: output changed |  |  |  |  | 66 |  |
| tamper: priv append 0 |  |  |  | 68 |  |  |
| tamper: priv drop first |  | 10 |  |  |  |  |
| tamper: priv drop last |  | 12 |  |  |  |  |
| tamper: priv[i]+1 |  | 4 | 18 |  |  |  |
| tamper: priv[i]=2 |  | 4 | 18 |  |  |  |
| tamper: priv[i]=p-1 |  | 19 | 3 |  |  |  |
| tamper: ptIn append 0 |  |  |  | 68 |  |  |
| tamper: ptIn drop first |  |  | 68 |  |  |  |
| tamper: ptIn drop last |  |  | 68 |  |  |  |
| tamper: ptIn[i]+1 |  |  | 340 |  |  |  |
| tamper: ptOut append 0 |  |  |  | 68 |  |  |
| tamper: ptOut drop first |  | 7 | 36 |  |  |  |
| tamper: ptOut drop last |  | 66 |  |  |  |  |
| tamper: ptOut[i]+1 |  |  | 184 |  |  |  |
| tamper: ptOut[i]=2 |  |  | 123 |  |  |  |
| tamper: ptOut[i]=p-1 |  |  | 184 |  |  |  |

97 of the rejections are wasm panics (a transcript read past its end),
counted as `premise`. The per-vector list, with the real error message for
each, is `build/semantics/vectors.json` and the output of `test/semantics.sh`.

## 8. What remains unvalidated

- The relation between `preprocess` and the constraint system: that is the
  upstream result (`circuit-faithful`), not tested here.
- Instructions, types and alignments outside the model (§2).
- The Poseidon constants and permutation are validated only through outputs
  (33 direct comparisons with the runtime, 36 vectors through the real
  evaluator, and every communications commitment), not against the Grain LFSR
  generation script.
- `persistent_hash` with a `compress` atom is only checked to fail.
- `test/all.sh` does not run `test/semantics.sh`; run it separately.
