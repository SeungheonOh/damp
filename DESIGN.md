# Damp: Midnight contracts written in Lean

Research notes, architecture and status, 2026-11-16.

Goal: write a Midnight contract as ordinary Lean definitions, compile it to the
circuits Midnight executes, and lay the foundation for a toolchain whose
semantics are stated and eventually proved in Lean. This is the Moist idea
(Lean to UPLC for Cardano) retargeted at Midnight.

Confidence labels used below: **[checked]** means I ran it or read the source
myself; **[read]** means a research agent read it in the source and cited the
location; **[inferred]** means a conclusion nobody verified directly.

---

## 1. Findings that shape the design

### 1.1 What is written in what

| Layer | Language | Where |
|---|---|---|
| Compact compiler (source to ZKIR, JS, metadata) | Chez Scheme, nanopass | `LFDT-Minokawa/compact`, `compiler/` |
| ZKIR consumer: interpreter, key generation, proving | Rust | `midnightntwrk/midnight-zkir` (v3), `midnight-ledger/zkir` (v2) |
| Proof system | Rust | `midnightntwrk/midnight-zk` (PLONK, KZG over BLS12-381, Jubjub embedded) |
| On-chain VM (Impact) and ledger | Rust | `midnightntwrk/midnight-ledger` |
| ZKIR v3 formal spec | Agda, about 21k lines | `midnight-zkir/zkir-spec/` |

So the Lisp part is the Compact compiler, not ZKIR. ZKIR is a JSON data format
produced by Scheme and consumed by Rust. "Rewriting it in Lean" therefore means
two different things with very different costs; see section 6.

### 1.2 The target has moved to ZKIR v3

- The local checkout of `LFDT-Minokawa/compact` used for this research is compiler 0.33.111, where v2 is
  the default and v3 is behind `--feature-zkir-v3`. [read]
- The toolchain installed on this machine is compactc 0.36.1 (2026-11-11),
  language 0.28.0, runtime 0.21.0, bundled `zkir-v3` 3.2.0. It emits v3 only.
  [checked]
- Target v3 only. Update the local Compact checkout before using it as a
  reference for the back end.

### 1.3 A compiled contract is two programs that must agree

For each exported circuit that touches the ledger, the compiler emits:

1. **A ZKIR circuit**: the constraint system. The external `zkir` tool turns it
   into `.bzkir`, a prover key and a verifier key. The verifier key goes on
   chain at deploy.
2. **An executor**: today a generated JS module. It reruns the same logic on
   concrete values in the DApp, calls the user's witness functions, runs each
   ledger operation through the wasm build of the Impact VM, and records the
   proof data: inputs, outputs, the public transcript (Impact ops plus the
   values read), and the private transcript (witness results). The proof server
   proves the circuit against that data. [read]

The two must agree on the order, count and encoding of every witness read and
every Impact op, or no proof exists. Exported circuits that never touch the
ledger get no circuit at all and run only in the executor. [read]

This is the Kachina model: a contract is a program with a public-state oracle
and a private-state oracle; the proof shows some private responses exist that
yield the claimed public transcript; the chain replays the public transcript.

### 1.4 The last Compact IR before ZKIR is tiny

`Lflattened` has no control flow. A circuit is a list of guarded single
assignments and asserts over field-sized values: [read]

- every statement carries a boolean guard (the path condition)
- about a dozen pure operations: `+ - * < == select`, byte/field conversions,
  checked downcasts
- three effect forms: witness call, ledger op (carrying its Impact code), event
- all user circuits inlined, all loops unrolled, all indices constant,
  recursion rejected

Getting there takes roughly 40 nanopass passes, most of which exist to handle
Compact's surface syntax, modules, generics and type inference. Lean already
does all of that. A Lean front end can aim at an IR of this shape directly.
[inferred]

### 1.5 ZKIR v3 in one paragraph

A circuit is typed inputs, typed outputs, and a list of instructions over named
single-assignment registers (`%name.n`) and inline field immediates
(little-endian hex). 47 instructions in 3.2.1; Compact uses about 35. The
effectful ones are `private_input` (next witness value), `public_input` (next
value read from the ledger), `impact` (declare these field elements as public
inputs, zeroed if the guard is false) and `output`. Each Impact VM op is
encoded as field elements using a fixed opcode table, and the verifier rebuilds
the same vector from the transaction's public transcript. [read, sample output
checked]

### 1.6 Upstream has already formalized ZKIR, and left the compiler gap open

`midnight-zkir/zkir-spec` contains an 82 KB language spec and an Agda
mechanization. I read the spec's properties and trust-base sections; the
mechanization claims come from the spec and its README. [read]

- It defines two semantics for a ZKIR source: **preprocess** (the reference
  interpreter that consumes the transcripts) and the **constraint system**.
- It proves they coincide (`circuit-faithful`) and that any satisfying witness
  can be extracted back to a run (`statement-sound`), given decidable
  **producer obligations** on the source: single assignment, value typing, bit
  bounds.
- Its trust base is the chip contracts, the crypto primitives and the typed
  encodings.
- It is pinned to ZKIR 3.0 (34 instructions) and does not cover the 3.2
  additions.
- It states explicitly that the correctness of the compiler producing ZKIR is
  out of scope.

That last point is exactly where a verified Lean compiler fits: prove
"Lean meaning of the contract = ZKIR preprocess semantics of the output" and
discharge the producer obligations; the upstream result then carries the claim
down to the constraint system.

### 1.7 What Moist teaches

Reusable as-is [read]:

- the user surface: a tag attribute on a plain `def`, a `compile!` elaborator
  that walks the kernel `Expr` in `MetaM` and reflects the result as a Lean
  constant, `#show_*` debug commands
- erasure of types, proofs and instances; `casesOn` interception; matcher
  unfolding; a name-to-builtin map; executable Lean twins of target primitives
- inline-everything translation of non-builtin constants
- the golden-test framework and the Ptah-style embedded builder DSL

Not reusable: the IR core (closures, `Fix`, `Force`/`Delay`) and most of the
step-indexed proof machinery, which exists because UPLC has closures and
non-termination. [inferred]

Gaps in Moist to close by design here [read]:

- The Lean-to-IR step is trusted; nothing relates the compiled term to the Lean
  function.
- The pipeline that `compile!` ships is the unverified one; the proofs cover a
  separate optimizer and a separate total lowering.

### 1.8 Verifier keys as a test oracle [checked]

Midnight's `zkir-v3` tool produces byte-identical prover and verifier keys from
a Lean-emitted circuit and from compactc's circuit for the equivalent Compact
source. "Same verifier key as compactc" is therefore a usable differential
test, and `test/oracle.sh` runs it.

---

## 2. Architecture

Decisions taken (2026-11-16):

- Contracts are ordinary Lean values built through a monadic interface. There
  is no elaborator and no traversal of Lean `Expr`. `MetaM` and macros are
  reserved for syntactic convenience.
- The ZKIR-to-circuit step stays in Rust. Lean describes and emits ZKIR; key
  generation and proving call Midnight's `zkir` tool.
- One generic executor interprets exported contract data.
- Numeric rules mirror Compact, with explicit escape hatches.
- The compiler uses core Lean only. Mathlib may be used later for proofs.

```
  Lean definitions in CircuitM over Field / Boolean / Uint
        │  ordinary Lean evaluation (no MetaM)
        ▼
  Circuit IR   pure expressions + guarded statements   Damp/IR/Basic.lean
        ├──► ZKIR v3 JSON ──► zkir tool (Rust) ──► bzkir, keys   Damp/Compile/Emit.lean
        ├──► contract.json ──► generic JS executor + runtime     Damp/Compile/Export.lean
        └──► reference semantics in Lean                         Damp/IR/Semantics.lean
```

### 2.1 Why a deep embedding

`Field`, `Boolean`, `Uint max` and `Bytes n` are thin wrappers around IR
expressions, with the usual operators. A circuit such as

```lean
ledger
  total : Cell Field

witness hint : Uint 9

circuit step (a : Field) (b : Boolean) (n : Uint16) : Field := do
  const h ← if% b then hint else pure 0
  const r := a * a + h.toField - transientHash a
  total.write r
  require (n <. 1000) "n too big"
  return r

contract step
```

evaluates, as plain Lean, to a `Circuit` value. That value is what the emitter
turns into ZKIR, what the executor interprets, and what `Circuit.run` gives
meaning to. A theorem about `Circuit.run step.circuit` is a theorem about the
compiled object, with no translation step in between to trust.
`Examples/Semantics.lean` has a first one, proved by `rfl`.

Lean is the compile-time language: recursion, lists, `for` loops, `let mut`,
higher-order functions, type classes and dependent types are all usable and
all vanish on evaluation.

### 2.1a The syntax layer

`Damp/Lang/Syntax.lean` is notation only. Every form is a macro onto plain
functions, and a contract can be written without it.

| Form | Expands to |
|---|---|
| `circuit f (a : A) … : R := body` | `def f : A → … → CircuitM R`, plus `f.circuit` built with the argument names |
| `witness w (a : A) … : R` | `def w` calling `askWitness "w"` |
| `ledger` + `name : Type` lines | one definition per field, numbered in order, and `ledgerFields` |
| `struct S where` + fields | a `structure` with its `Value` and equality instances |
| `enum E where` + `\| variant` lines | a wrapper type, `E.variant` constants, equality |
| `const x := e`, `const x ← m` | `let x ← val e "x"`: computed once, here, named after the binder |
| `contract Name` | `def contract : Contract` from the ledger and circuits declared in the namespace |
| `<.` `<=.` `>.` `>=.` `==.` `!=.` `&&.` `\|\|.` `!.` | comparison and boolean functions |
| `if% c then t else e` | `cond c t e` |
| `#zkir f`, `#circuit_info f` | prints the ZKIR for `f`, or a summary of it |

No name is written twice or as a string: argument names, witness names, ledger
field names, value names and the contract's circuits all come from the
declarations.

Three places use an elaborator, all narrowly:

- **Plain `if`.** With `open Damp`, `if c then t else e` means `cond` when `c`
  is a circuit `Boolean` and Lean's `ite` otherwise. The elaborator looks only
  at the type of the condition. This is what lets `let mut` variables be
  assigned under a circuit condition, including inside `for`.
- **Checking at the declaration.** `circuit` evaluates and emits the circuit it
  just defined and reports any problem on its name, so mistakes show in the
  editor. It runs the ordinary compiler; it reads nothing from the syntax.
- **Collecting circuits.** `circuit` records its name against the namespace in
  an environment extension, and `contract` reads that list.

One trap, and how it is handled. `do` notation moves the statements after an
`if` into both branches. With a circuit condition both branches are built, so
everything after the `if` would be built twice. Lean 4.36 hands the branches to
the elaborator already elaborated, so this cannot be seen in the syntax.
Instead a plain `if` checks, when the circuit is built, whether both branches
end with the same effect, and reports an error telling the author to use
`if%`. `if%` is an ordinary term, so nothing is moved into it. A plain `if`
whose continuation has no effects is still built twice, but that only repeats
pure expressions, which the emitter shares.

Remaining costs of avoiding `MetaM` in the core:

- Sharing is explicit: `const` computes a value at that point, where a plain
  `let` is computed at its first use. The emitter also shares syntactically
  equal expressions and drops unused bindings.
- A numeral is accepted wherever a `Uint` is expected, but Lean's instance
  search cannot decide whether it fits the bound. One that does not becomes an
  `invalid` expression in the IR, which the emitter rejects, so the error
  appears at the circuit's declaration, not at the literal.

### 2.2 The circuit IR

- `Expr`: variables, constants, `add`, `mul`, `neg`, `lt`, `eq`, `select`,
  `hash`. Pure, so sharing and reordering are safe.
- `Stmt`: `bind`, `assert`, `constrain` (range), `witness` (guarded, private
  oracle), `ledger` (guarded, Impact instructions and the variables bound by
  its reads).
- No control flow. Effects under a branch carry the branch condition as their
  guard; asserts under a branch become "guard implies condition".

`Damp/IR/Impact.lean` holds the Impact instructions and their field-element
encoding, generic in the operand type so the emitter, the semantics and the
exporter share one definition. Only instructions whose encoding was checked
against compactc are included.

### 2.3 ZKIR emission

One instruction per operation, operands first and left to right, which is the
order compactc uses. Each ledger statement becomes its reads as `public_input`s
and one `impact` per VM instruction. Every emitted circuit is checked for
single assignment and scoping, the first of the three producer obligations the
upstream soundness result assumes.

### 2.4 Executor

When a user calls a circuit, something on their machine runs it for real:
evaluates the expressions, asks the witnesses, runs the ledger operations
against the current public state, and records what the prover needs.

- **The definition** is `Exec.run` in `Damp/Executor/Spec.lean`, with the witnesses
  and the on-chain VM as parameters.
- **The code that ships** is `executor/src/executor.mjs`, a generic
  interpreter of `contract.json`: per contract there is only data. It is
  written clause for clause after the definition.
- **The link** is `test/executor.sh`: every example call and 115 synthetic
  edge cases are run in JavaScript with a trace, then replayed through
  `Exec.run` with the recorded oracle answers. They must agree on whether and
  at which statement the call fails, on every oracle question, and on the
  outputs, transcripts and public inputs. Putting any of sixteen old
  behaviours back into the JavaScript makes the test fail.

Writing the definition showed the old executor was laxer than the circuit in
several places (a non-boolean guard treated as "skip", only the chosen branch
of a conditional evaluated, comparison widths ignored), so it could have
produced proof data the prover would reject. Those are fixed.

A witness that returns nothing places no constraint in the circuit but is
still run when its guard holds, as in Compact: it exists to update the user's
private state.

### 2.5 What a circuit means

There are two evaluators, and the second is the one that matters.

- **`Zkir.IrSource.run`** (`Damp/Zkir/Semantics.lean`) is a Lean port of
  Midnight's reference evaluator, `IrSource::preprocess` in midnight-zkir
  3.2.1: the function the proof server runs to decide whether a call
  satisfies a circuit and to compute its public inputs. It is partial where
  the Rust is. Its hashes are real: Poseidon with the constants of the pinned
  circuits release, SHA-256, and the persistent hash's byte layout, all in
  `Damp/Crypto/`.
- **`IR.Circuit.run`** (`Damp/IR/Semantics.lean`) gives the IR the same shape of
  meaning: inputs, private transcript and public reads in; outputs and one
  group of public inputs per on-chain instruction out, or `none`.

The first is tested against the real thing (`test/semantics.sh`): 2,725
proof-data vectors from the example contracts and synthetic circuits, honest
and tampered, run through Midnight's checker and through the Lean evaluator,
which must accept and reject the same ones for the same kind of reason and
give the same outputs. The public transcript's field encoding is parsed from
the runtime's own serialized preimage, not produced by Damp. That test found
and fixed three errors in the port, none reachable from a circuit Damp emits.

The second is tied to the first by proof (section 4), so it is no longer an
independent claim about what circuits mean.

### 2.6 Optimizer

`Damp/Optimize/`, one pass per file, put in order by `Pipeline.lean`. The
passes rewrite the IR before both the emitter and the exporter read it, so the
circuit and the executor still agree by construction.

A circuit must not start accepting inputs it used to reject, so a rewrite may
only drop a subexpression that cannot fail (or is known to have been evaluated
already), and may only drop a condition that is certainly 0 or 1. Each rule
carries that side condition.

| Pass | What it does |
|---|---|
| `Simplify` | constant folding; `x+0`, `x·1`, `−−x`; `x·0` and `x == x` for an `x` that cannot fail; a comparison of constants that fit its width; a conditional with a constant condition whose dropped branch cannot fail; constant and copy propagation; drops asserts and range checks known to hold or implied by an earlier check on the same expression; drops a witness call or ledger operation whose guard is exactly 0 when nothing dropped could fail |
| `Bounds` | carries an upper bound for each variable (from range checks, bindings, witness ranges, asserted comparisons) through sums, products, conditionals and `divmod`; drops a range check the bound implies; replaces a `divmod` of a value already below the divisor; folds a comparison the bounds decide |
| `Algebra` | reads a tree of additions, negations and constant multiples as a linear combination and rebuilds it when that is strictly smaller (`(x+3)+4`, `x+x+x`, `(x−y)+y`); moves constants across an equality; collapses a conditional nested under its own condition. Never used when it would break sharing and grow the circuit |
| `Asserts` | uses what an `assert` established: the condition is 1, a conjunction's parts are 1, a negation's operand is 0, an asserted `e == k` makes `e` the constant; duplicate and implied asserts are dropped; an expression already evaluated counts as unable to fail |
| emitter | shares equal expressions; drops unused bindings |

Two levels. The default (`Circuit.optimize`: `Simplify`, `Bounds`,
`Simplify`, `Algebra`) leaves every circuit written to mirror a Compact
program exactly as compactc produces it, so verifier keys stay comparable.
`--O2` (`Circuit.optimizeFull`) adds `Asserts`, which knows things compactc
does not use: `counter.arith` goes from 32 to 29 instructions (146 to 137
rows) and no longer has compactc's verifier key. `--no-opt` turns everything
off.

Every pass is proved sound (`Pass.Sound`, `Damp/Proofs/Optimize/Sound.lean`):
for every circuit, with no hypothesis on it, the pass changes neither what a
run produces that anyone can observe nor what the executor does, whatever its
oracles answer. Soundness composes, so both pipelines are sound
(`Circuit.optimize_sound`, `Circuit.optimizeFull_sound`), and each pass keeps
the ledger-statement check passing. An earlier version of the optimizer was
"proved" against a semantics that was total and wrong; under the real one
several of its rules were unsound and have been restricted as above.

Measured with `test/opt.sh`: circuits written to mirror Compact are unchanged
at the default level, because they were already what compactc's own optimizer
produces. The `tuned` example goes from 33 to 22 instructions and from 170 to
145 rows of the proof system's table. `Bounds` and `Algebra` change none of
the example contracts; they pay off on code the static types and Compact-style
writing miss (`Examples/OptBounds.lean`: `require (x <. 10); x.castTo 9` from
6 to 4 instructions; `Examples/OptAlgebra.lean`: 20 to 15). Instruction count
is a weak proxy for cost: hashes and range checks dominate.

### 2.7 Disclosure check

`Damp/IR/Disclosure.lean` is Compact's rule that private data must be marked
before it becomes public. Circuit arguments and witness results are tracked
through the IR; reaching a ledger operand, a ledger operation's guard, or (for
witness results) the circuit's result without passing through `disclose` is an
error naming where the data came from. Hashing keeps the mark; a commitment
clears it. `disclose` is a marker node in the IR with the value of its
argument, so the circuit is unchanged by it.

It runs when a circuit is declared and again when a contract is built. It is a
lint for the author: no proof depends on it.

---

## 3. Status

Working and tested:

- **Verifier keys identical to compactc 0.36.1** for 25 circuits in ten
  contracts (`test/oracle.sh`). Together they cover:
  - witnesses, including under a condition and returning structures
  - nested conditionals, guarded asserts, conditional assignment in a loop
  - `Uint` add, multiply, checked subtract, all six comparisons, boolean
    connectives
  - structures, vectors, tuples, enumerations and `Maybe` as arguments,
    results and ledger contents; equality on all of them
  - `Bytes n` for 8, 32 and 64 bytes: inputs, equality, constants, ledger
  - the transient and persistent hashes and commitments
  - `Cell`, `Counter`, `Map`, `Set`, `LedgerList`, `MerkleTree`,
    `HistoricMerkleTree`, and maps whose values are themselves ledger types
  - kernel operations: `self`, `checkpoint`, the block-time checks
  - a constructor
- **The generic executor** produces proof data, results, initial ledger state
  and a decoded ledger view identical to compactc's generated module, across
  chained calls (`test/all.sh`, 344 checks), and agrees with its Lean
  definition on 200 calls (`test/executor.sh`). Midnight's ZKIR checker accepts
  that proof data against the Lean-emitted circuit and rejects it when a value
  is altered. One real proof was generated from a Lean-emitted circuit's
  prover key.
- **Deployed and called on a local Midnight network** (`deploy/`): node,
  indexer and proof server in Docker, driven through midnight-js 5.0.0 with
  real proofs. Damp-compiled `counter`, `vault` (constructor arguments),
  `extras` and `shapes` were deployed and called, with the resulting ledger
  read back from the indexer. A contract deployed from compactc's output
  accepted calls from the Damp build and the reverse. Two negative controls
  with a wrong verifier key were rejected, one by the proof server and one by
  the node. Contracts are packaged for midnight-js by
  `executor/bin/damp-package.mjs`; no adapter code is needed.
- **The Lean ZKIR evaluator agrees with Midnight's** on 3,018 checks
  (`test/semantics.sh`), and the compiler is proved correct against it
  (section 4).
- **The optimizer** leaves every Compact-mirroring circuit's key unchanged and
  shrinks the `tuned` example; optimized and unoptimized builds give the same
  results and are both accepted by the checker (`test/opt.sh`).
- **Mistakes caught at the declaration** (`Examples/Diagnostics.lean`,
  `Examples/Interface.lean`): undisclosed data reaching the ledger, a guard or
  the result; `break` under a circuit condition; an `if` whose continuation
  would be built twice; a literal too large for its `Uint`; a `Uint` bound
  above 248 bits; a ledger statement whose public inputs would not be what is
  sent to the ledger.
- **Golden files** (`test/golden.sh`): the emitted ZKIR and contract data for
  every example, checked without needing anything from Midnight.
- **Tooling**: `Damp.cli` with key generation, `#zkir`, `#circuit_info`, a
  packager for midnight-js that also writes TypeScript declarations
  (`executor/bin/damp-package.mjs`).

Not done, and what it would take to call this production-ready:

- **No independent review.** Everything here was written and tested in one
  effort. A contract compiler that guards value needs an audit.
- **Local network only.** Nothing has been deployed to a public test network.
  Browser key providers, pure-circuit calls through midnight-js and
  maintenance transactions are untested.
- **Proofs.** The optimizer, the emitter, the executor's definition and the
  typed interface are proved against a tested port of Midnight's evaluator;
  section 4 lists what that does not cover, chiefly the JavaScript and
  everything below the evaluator.
- **Coins and tokens.** Compact's token library is ported (`Damp/Lang/Tokens.lean`,
  [docs/tokens.md](docs/tokens.md)): shielded and unshielded minting, sending,
  receiving, merging and balances, with the built-in witnesses run by the
  executor. Two circuits that send a shielded coin to a run-time recipient
  differ from compactc's keys by a repeated hash and a select on a copied
  constant (accounted for exactly by `test/oracle.sh`), and the coin-storing
  operations (`writeCoin`, `insertCoin`, `pushFrontCoin`) by an unfolded select
  on a constant. On the local network a contract stored a received coin and
  once spent it; `sendShielded` of a stored coin was rejected for running out of
  gas budget, for compactc's build as for Damp's.
- **Language gaps.** No general sum types. No `Bytes` to `Field` conversion or
  byte indexing. No elliptic-curve operations or Keccak. No cross-contract
  calls or events. Merkle membership proofs need the path-root circuit, which
  is not ported.
- **Known differences from compactc.** Damp shares equal hash computations
  where compactc repeats them, so a circuit hashing the same value twice gets
  a smaller circuit and a different key. Matching keys otherwise depends on
  evaluation order, which `const` controls.
- **Version pinning.** Built and tested against compactc 0.36.1, runtime
  0.21.0 and ZKIR 3.2.x only.

---

## 4. What is proved

`Contract.build` ships, for a circuit `c`, the ZKIR `Emit.circuit c.optimize`,
and the executor interprets `c.optimize`. All statements are in Lean, with no
`sorry` and only Lean's three standard axioms.

**The compiler** (`Damp/Proofs/Compiler.lean` chains these):

| Theorem | Statement |
|---|---|
| `Circuit.optimize_correct` | optimizing changes neither the outputs nor the public inputs of the on-chain instructions that ran, and rejects exactly the same runs |
| `pruned_run` | dropping unused bindings keeps every accepted run, with the same outcome |
| `circuitCore_correct` | the emitted ZKIR, under the ZKIR evaluator, gives exactly what the IR semantics gives, for every input and transcript: same outcome or both reject |
| `compile_exact` | the shipped ZKIR means exactly the shipped circuit (optimized, unused bindings dropped) |
| `compile_complete` | every run the contract's circuit accepts is accepted by the shipped ZKIR with the same observable outcome |

**The executor** (the Lean definition `Exec.run`):

| Theorem | Statement |
|---|---|
| `Exec.run_accepted` | a call the executor completes is a run the circuit accepts: the private transcript and ledger reads it recorded, the outputs and public inputs it recorded |
| `Exec.run_accepted_by_zkir` | and therefore one the shipped ZKIR accepts |
| `Exec.run_none` | a call fails only if the inputs are not the circuit's, an oracle gave no usable answer, or the circuit rejects every transcript beginning with exactly what the executor recorded and was answered |
| `Exec.optimize_correct` | on the optimized circuit the executor completes exactly when it would on the original and leaves the same outputs, transcripts, active public inputs, private state and ledger state |
| `Circuit.bounds_sound`, `Circuit.algebra_sound`, `Circuit.asserts_sound`, `Circuit.simplify_sound` | each pass is sound by itself, for every circuit; `Circuit.optimize_sound` and `Circuit.optimizeFull_sound` follow by composition, and `compile_complete_full` is the end-to-end statement at `--O2` |
| `Exec.optimize_asks_same` | and asks the witnesses and the ledger the same questions in the same order |
| `Exec.step_ledger_agrees`, `Exec.run_groups_fromLedger` | the public inputs a call records are the field encoding of the instructions it sent to the ledger, with the ledger's answers filled in |

**The interface** (`Damp/Proofs/Interface.lean`): a `Uint m` holds a number at
most `m` and a `Boolean` holds 0 or 1; `+` and `*` give the exact result with
no wrap-around; all comparison forms compare the numbers; `sub` fails exactly
when it would go negative; `castTo` and `toUint` succeed exactly when the value
fits; `require` succeeds exactly when its condition holds or its guard does
not; range checks make inputs and witness results inhabit their types.

**Checked on every emitted circuit**, not proved of the emitter: the three
producer obligations of the ZKIR specification (single assignment, value
typing, bit bounds; `Damp/Zkir/Checks.lean`), and that each ledger statement is
well formed in the sense the ledger theorems need.

Proving these found five mistakes that testing had not:

- several optimizer rewrites could make a circuit accept inputs it used to
  reject (they dropped a subexpression that could fail, or a requirement that
  a condition be 0 or 1);
- the optimizer dropped witnesses that return nothing, changing the user's
  private state without changing the circuit;
- the optimizer could change what was sent to the ledger when a read variable
  already had a known value;
- a checked cast or subtraction inside a branch not taken could fail the whole
  circuit;
- a `Uint` bound above 248 bits could be introduced by a literal, making
  equality compare field elements, not numbers.

What the proofs do not give:

- **The converse of `pruned_run`.** An unused binding whose expression would
  fail fails `Circuit.run`, which evaluates every statement, but constrains
  nothing in the emitted circuit. The exact statement is `compile_exact`.
- **Anything below the ZKIR evaluator.** That the evaluator agrees with the
  constraint system is upstream's theorem (in Agda, for ZKIR 3.0); the chips,
  the proof system and the cryptography are trusted. The Lean evaluator's
  agreement with the Rust one is tested, not proved.
- **The JavaScript.** The executor theorems are about the Lean definition; the
  JavaScript is tied to it by a conformance test. The conversion between JS
  values and field elements, the runtime and the witnesses are outside both.
- **Values read from the ledger.** They are not range-checked in the circuit,
  as in Compact: a `Uint 255` read from a cell is only as good as what was
  written. `Field.unsafeToUint` is unchecked by design.
- **That the optimizer preserves ledger well-formedness.** It is checked on
  the optimized circuit at build time, so a violation is a build error.
- **Parts of the interface:** `Bytes` beyond limb equality, `Maybe`, the
  ledger operations themselves, and per-position lemmas for circuit arguments
  after the first.
- **Instructions the Lean evaluator does not model**: elliptic-curve
  operations, `inv`, non-native inputs. Damp does not emit them.

One known difference from compactc that the interface fix introduced: a
checked cast inside a branch uses different instructions from compactc's (same
meaning, different verifier key). No example covers that case.

## 5. Next steps

1. Find why spending a stored coin runs out of gas budget on chain (it does
   for compactc's build too), so that a held coin can be sent with change.
2. Mirror compactc's instructions for checked casts inside a branch, with an
   oracle contract to compare against.
3. Interface lemmas for `Bytes`, `Maybe` and the ledger operations; that the
   optimizer preserves ledger well-formedness.
4. General sum types, byte conversions, elliptic-curve operations, the Merkle
   path-root circuit.
5. Cross-contract calls and events.

---

## 6. Risks

- Upstream moves fast: three ZKIR minor versions and a compiler that dropped v2
  within months. Versions are pinned (compactc 0.36.1, runtime 0.21.0, zkir
  3.2.x) and the differential tests will show drift.
- The Agda mechanization is pinned to ZKIR 3.0; compactc already emits a 3.2
  instruction it does not cover.
- Poseidon parameters were read from midnight-zk head, not from the pinned
  circuits release. Only matters once Lean needs an executable hash.
- The Moist study flagged two axioms there as likely inconsistent
  (`budget_exhaustion`, `pError`). Unverified, and outside this project.

---

## 7. Sources

Local:

- `LFDT-Minokawa/compact` (local checkout): `compiler/passes.ss` (driver), `compiler/langs.ss`
  (all IR grammars; `Lflattened` at 1143, `Lzkir` at 1265), `compiler.md`,
  `compiler/midnight-ledger.ss` (ledger ops as Impact code),
  `compiler/zkir-v3-passes/` (emitter), `runtime/src/` (executor runtime)
- `seungheonoh/moist` (local checkout): `Moist/Onchain/Translate.lean`, `Moist/Onchain/Compile.lean`,
  `Moist/MIR/`, `Moist/Verified/`, `docs/`
- `~/.compact/versions/0.36.1/x86_64-unknown-linux-musl/`: `compactc.bin`,
  `zkir-v3`

Upstream:

- https://github.com/midnightntwrk/midnight-zkir (`zkir/src/ir.rs`,
  `zkir/src/ir_vm.rs`, `zkir-spec/docs/zkir-v3-spec.md`, `zkir-spec/src/zkir-v3/`)
- https://github.com/midnightntwrk/midnight-ledger (`spec/zkir.md`,
  `spec/impact-opcodes.md`, `spec/onchain-runtime.md`, `onchain-vm/`,
  `proof-server/`)
- https://github.com/midnightntwrk/midnight-zk
- https://github.com/midnightntwrk/midnight-js
- Kachina: IACR ePrint 2020/543

Prior art for circuits in Lean:

- https://github.com/Verified-zkEVM/clean: monadic circuit DSL with per-gadget
  soundness and completeness theorems; BN254 gadgets, not BLS12-381. The
  theorem shapes are the ones to borrow for gadgets.
- https://github.com/Verified-zkEVM/ArkLib: proof-system level.
- https://github.com/lfglabs-dev/verity: Lean to Yul with proofs.

Run the tests:

```bash
./test/all.sh
```
