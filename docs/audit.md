# Audit: do the proofs show that the optimizer preserves what a program means?

Adversarial audit of the semantics, the soundness notions and the verification paths, at git
`ccd590e` (2026-11-23). The question was: are the definition of the semantics and the verification
paths strong enough to prove that the optimization passes preserve what the program means?

**Short answer: no, at every level.** Two findings break shipped levels:

- **F1.** `--ledger-opt` changes the results of a call whose user witness reads the ledger.
- **F2.** The shipped ZKIR accepts inputs that the unoptimized ZKIR and the source semantics reject.
  This affects the default level, `--O2` and `--O3`. At `--O3` it is a practical forgery of an
  out-of-range witness value, accepted by Midnight's real checker.

Both are confirmed by tests that fail today (`test/audit/run.sh`). Neither is a bug in a proof. In
both, the theorem is about a semantics that differs from what runs: a witness oracle that cannot
see the ledger (F1), and `Circuit.run`, which evaluates bindings the emitter never emits (F2).

Everything was run on a scratch worktree of `ccd590e`. Nothing in the shared tree was edited except
the new files listed at the end.

---

## 1. Findings, ranked

### F2 (high). The shipped ZKIR can accept what the source program and the unoptimized ZKIR reject (default, `--O2`, `--O3`)

**What is proved, and what is missing.**

- Every pass theorem (`Pass.Sound`, `Pass.SoundFor`) compares `Circuit.run` before and after the
  pass. `Circuit.run` evaluates every `bind`, used or not (`Stmt.exec`, `Damp/IR/Semantics.lean`).
- The emitter drops unused bindings (`Emit.pruneDeadBinds`). So the shipped ZKIR means
  `Emit.pruned (f c)` (`compile_exact`).
- `pruned_run` / `compile_complete` give only one direction: every run that `c` accepts, the ZKIR
  accepts.
- No theorem bounds what the shipped ZKIR accepts in terms of the source. A ZK verifier sees only
  that ZKIR, so the security-relevant direction is the one that is missing.
- DESIGN.md calls the missing direction "the converse of `pruned_run`" and treats it as harmless:
  an unused binding constrains nothing. That holds only without an optimizer. The passes are free
  to rely on a binding being evaluated, and they do. Some use the evaluation of a dead binding
  directly. Others remove the last use of a binding that can fail, which makes it dead, and then the
  emitter drops its check.

**Evidence.** `test/audit/Prune.lean` (`lake env lean`; its `#guard`s fail today). Each circuit
below has input `a`, and `v := a <₈ 0` fails for `a = 1000`. In every case the `--no-opt` ZKIR
refuses `a = 1000` and the shipped ZKIR at the named level accepts it, according to
`IrSource.run`, which `test/semantics.sh` ties to the real checker.

| # | level | pass | circuit (body ⟶ outputs) | why |
|---|---|---|---|---|
| 1 | **default** | `simplify` | `v := a<₈0` ⟶ `v*0` | `x*0 ↦ 0` for `x` that cannot fail; a variable cannot fail; `v` is now dead |
| 2 | **default** | `simplify` | `v := a<₈0` ⟶ `v==v` | `e==e ↦ 1` |
| 3 | **default** | `algebra` | `v := a<₈0` ⟶ `(a−v)+v` | the linear combination drops `v` |
| 6 | **default** | `bounds2` | `v := a<₈0` ⟶ `v <₈ 5` | `v` has the bound 1 from its binding; the comparison folds to 1 |
| 4 | `--O2` | `asserts` | `t := a<₈0` (unused), `u := (a<₈0)*0` ⟶ `u` | `evald` includes the body of `t`, which the emitter drops |
| 7 | `--O2` | `forwardAllOpt` | `v := a<₈0`, `witness w [v]` | `v` moves into the witness argument, which is never emitted; the binding becomes dead |
| 8 | `--O2` | `mergeChecks` | `b := a<₈0`, `n := sel b 0 1`, `assert (sel b c 1)`, `assert (sel n c 1)` | becomes `assert c`; `b` is dead |
| 5 | `--O3` | `hashRanges` | `w : Uint<8>` witness, `h := phash [bytes 1] [w]` (unused) | the range check of `w` is dropped because of a hash that the emitter then prunes |

From surface syntax, at the **default level** (`Audit/PruneSurface.lean` in the audit scratch dir; the
same pattern as row 2):

```lean
witness w : Field
circuit f : Field := do
  const u := Field.unsafeToUint (← w) 255
  const v := u <. 10
  c.write 1
  return (if v then (0 : Field) else 0)
```

With `w = 1000`, `--no-opt` rejects; default, `--O2` and `--O3` accept.

End to end at `--O3`, with Midnight's real checker (`test/audit/HashRange.lean` and
`executor/test/audit-o3-range.mjs`):

```lean
witness w : Uint 255
circuit f : Unit := do
  const x ← w
  const _h := persistentHash #v[x]
  c.write (disclose x.toField)
```

The honest run (w = 200) is accepted at both levels. Replacing 200 by 1000 in the private
transcript and in the public transcript's encoding:

- `--O2`: rejected, "Bit bound failed: e803 is not 8-bit".
- `--O3`: **accepted**.

A prover can write a non-`Uint<8>` value into the ledger through a circuit whose source forbids it.

**Which passes rely on "this expression is evaluated, or would fail, elsewhere".**

- **Use the evaluation of another statement:**
  - `Asserts`, through `Known.evald`: bodies of bindings, and guards of witness calls with no
    results, which are not emitted either.
  - `hashRanges`, through `Stmt.hashSlots` on `.bind`.
  - `Bounds` / `Bounds2`: they learn the bound of `v` from its binding. That bound is only about
    `v`, so they need the removal of `v`'s last use to do harm (row 6).
- **Remove the last use of a binding:**
  - `Simplify`: `x*0`, `e==e`, `select 1 a b`, `select c a a`, constant and copy propagation.
  - `Algebra`, `Bounds` / `Bounds2` (folding), `mergeChecks`, `Forward` / `InlineAll` (into
    witness arguments).
- **Not exploitable:**
  - `AssertEq` (it removes nothing) and `AssertZero` (it keeps both operands).
  - `Commute`, `shareSelects` / `shareGuarded` (they keep every operand).
  - `foldHashes` / `foldDivmod` (constants only).
  - The ledger passes: they rewrite ledger statements, which are never pruned, but they run
    `optimizeFull` again, so they inherit everything above.

**The executor path.** `Exec.run` and `executor.mjs` evaluate every binding, dead or not
(`Exec.step .bind`; `case 'bind'`). On a dead binding that fails:

- the executor refuses the call (no proof is produced),
- while the ZKIR accepts any proof data for it, at every level, `--no-opt` included.

An honest user's executor is therefore stricter than the circuit; a malicious prover does not run
it.

**What is "right": compactc as a reference.** compactc 0.36.1 does two things
(`dead.compact` in the scratch dir):

- It **keeps** a dead checked cast: `const u = x as Uint<8>; const v = u < 10;` with neither used
  still emits `constrain_bits 8`.
- It drops the dead comparison, which cannot fail once the cast is checked.

Compact has no pure expressions that can fail. Its checks are statements and are kept. Damp's IR
has partial pure expressions: `lt` on unchecked values, `select` on a non-boolean,
`divmod` > 248, `phash` alignment, `invalid`.

**The missing theorem**, in Lean:

```lean
/-- The pass does not change what the emitted circuit accepts. -/
def Pass.SoundPruned (p : Prims) (f : Pass) : Prop :=
  ∀ (c : Circuit) (inputs priv pub : List Fr),
    ((Emit.pruned (f c)).run p inputs priv pub).map Outcome.observable =
      ((Emit.pruned c).run p inputs priv pub).map Outcome.observable

/-- What the user needs: whatever the shipped ZKIR accepts, the ZKIR of the circuit as written accepts. -/
theorem compile_sound (lvl) (c : Circuit) (src src₀ : Zkir.IrSource)
    (h : Emit.circuit (buildPass lvl c) = .ok src) (h₀ : Emit.circuit c = .ok src₀)
    (inputs priv pub) (o) (hr : src.run p inputs priv pub = some o) :
    ∃ o₀, src₀.run p inputs priv pub = some o₀ ∧ o₀.observable = o.observable
```

How it composes:

- `Pass.SoundPruned` composes like `Pass.Sound`, by transitivity on the circuit `f c`.
- With `compile_exact` applied on both sides, it gives `compile_sound`.
- With `Pass.Sound` and `pruned_run` it gives today's `compile_complete`.

Two fixes:

1. Make `Circuit.run` itself lazy in bindings (a binding fails only if something emitted reads
   it). Then `Pass.Sound` is `Pass.SoundPruned`, and the rules above stop being provable.
2. Restrict the rules to "the dropped part cannot fail" (`total`), never "was evaluated
   elsewhere". Then also stop removing the last use of a binding that can fail. The simplest way
   is to require `total` of the binding's body before folding a variable away, or to turn such a
   binding into an `assert`-like statement the emitter keeps.

Option 2 matches compactc. A failing pure expression the user wrote should stay checked, as a
dead `as` cast does.

### F1 (high, `--ledger-opt`). A user witness sees the ledger mid-call; the model's witness cannot

`Exec.Oracles.witness : String → List Fr → ω → Option (List Fr × ω)` sees neither the ledger state
nor the call context. The shipped executor (`executor.mjs:661`) hands every user witness
`createWitnessContext(ledgerView(cc.currentQueryContext.state), …)`: the ledger as the ledger
statements before it left it. compactc's generated modules do the same. In real contracts this is
common: a witness looks up a Merkle path, a map entry or a counter.

The ledger passes move or drop writes across any witness except `createZswapOutput` and `call:…`:

- `ledgerDeadStore`: `overwrites`, `LedgerDeadStore.lean:63`.
- `ledgerMerge`: `lcommutes`, `LedgerMerge.lean:275`.

`Examples/OptLedgerDeadStore.lean` even `#guard`s the rewrite across a user witness (`"BAWL"`).
`Pass.SoundLedger` is true and says nothing here, because its quantified witnesses cannot observe
the difference.

**Evidence.** `test/audit/LedgerWitness.lean` and `executor/test/audit-ledger-witness.mjs`, through
the real runtime, with the same witness implementations (`peekC = ctx.ledger.c`) at `--O2` and at
`--O2 --ledger-opt`:

| call | `--O2` | `--O2 --ledger-opt` |
|---|---|---|
| `c.write 3; x ← peekC` | 3 | 3 |
| `c.write 1; x ← peekC; c.write 2` | **1** | **3** (the first write dropped) |
| `c.write v; x ← peekD; d.write (v+7)` (v = 10, then 20) | **0**, **17** | **17**, **27** (the write merged above the witness) |

The DESIGN.md text on the "witness gap" names only `createZswapOutput` and `call:`. The gap is
every witness, because every witness can read.

**Proposed fixes:**

- (a) Make `ctxWitness` true for every witness name. This is the cheapest, and is what the theorem
  can actually justify.
- (b) Or give the model's witness oracle the ledger state, (`String → List Fr → ω → σ → …`). Then
  re-prove the passes, which then must not move writes across a witness. `Calls.lean`'s
  `CallOracle` is already that shape.

Lesser consequences of the same oracle shape, at the `Pass.Sound` level:

- `Pass.SoundExec` would also accept a pass that swapped a witness call and a ledger statement:
  witness and ledger act on disjoint state, so the swap commutes in the model. No current pass
  does that, but the definition does not forbid it.
- The witness oracle is also blind to the call context and Zswap state (the `createZswapOutput`
  gap, patched syntactically), to the caller's address, and to time.

### F3 (medium). `--O3` constants are never checked end to end against the runtime

- `foldHashes Crypto.prims` changes exactly one benchmark circuit family, `adt_merkle`.
- Its benchmark calls are refused by construction ("both circuits are contradictory by
  construction; only the refusals are compared", `executor/test/bench.mjs:249`).
- So no test runs a call whose outcome depends on a folded constant.
- The only evidence for `Crypto.prims = runtime` is the crypto corpus of `test/semantics.sh`:
  18 Poseidon, 15 commitment, 74 persistent-hash and 18 SHA-256 cases, plus hashes inside the
  2,774 call vectors.

**Fix:** a test that folds the constants of a satisfiable circuit, for example a Merkle leaf of a
literal checked against a root the runtime computes, and runs it through the runtime.

### F4 (medium). `Pass.SoundLedger` is about the executor from one state; the chain replays the transcript on another

`Pass.SoundLedger` compares two executor runs from the same σ. On chain, the recorded public
transcript of the rewritten circuit is replayed against the chain's state at inclusion, which may
differ.

I found no counterexample. The facts `ledgerReuse` uses are derived from earlier instructions of
the same transcript, so they hold on any state. But no theorem states "replay of `T'` on σ′
succeeds iff replay of `T` on σ′ does".

F1 shows the danger: witness answers are fixed in the proof but were computed from σ.

Gas is not modelled. Every ledger pass removes or regroups instructions, so the rewritten call
needs at most as much gas, but that is measured, not proved. A per-request limit, if the runtime
has one, would make `ledgerMerge`'s 1024-instruction cap matter; not examined.

### F5 (low). Noninterference is proved of the circuit as written, not of what ships

`groups_noninterference` is about `c` (the disclosure check runs on the unoptimized circuit).

- `Pass.Sound` keeps the active public inputs of every `Circuit.run`, so the property transfers to
  `Circuit.run (f c)`.
- It does not transfer to the pruned ZKIR (F2) or to `--ledger-opt` (`Pass.SoundLedger` says
  nothing about the public inputs).

### F6 (low). The JS executor keeps state that nothing checks

`st.priv` in `executor.mjs` is written and never read: the proof data is built from
`ppd.privateTranscriptOutputs`. Mutation J4 below, which pushes zeros onto `st.priv` for a witness
that was not asked, passes `test/executor.sh`.

It is harmless today. But it is the variable the comments align with the Lean definition's `priv`,
so the clause-for-clause correspondence the file claims is not the one that is tested.

### Checked and found sound (positive results)

- **`IrSource.run` against Midnight's checker on operator edge cases.** 115 new vectors
  (`executor/test/audit-zkir-edges.mjs`): `cond_select` / `assert` / `not` / `constrain_to_boolean`
  on 0, 1, 2 and p−1; `less_than` at 0, 1, 248 and 253 bits on boundary values; `constrain_bits` at
  the same widths; `add` / `mul` / `neg` wrap-around; negative immediates; `div_mod_power_of_two`
  at 1 and 247 bits of p−1. All 115 agree (33 accepted, 82 rejected for the same reason).
- **`σ.WF` holds on real states.** All 27,350 starting effects and all 6,865 post-query effects
  recorded from the real runtime by `test/vm.sh` (`test/audit/WfStates.lean`).
- **Axioms.** `#print axioms` on `build_correct`, `build_contractJson`, `compile_exact`,
  `compile_complete_max`, `run_accepted_by_emitted`, `Exec.optimize_correct`,
  `optimizeFull_ledger_soundLedger`, `optimizeMax_ledger_soundLedgerFor`, `hashRanges_soundFor`,
  `ledgerMerge_soundLedger`, `groups_noninterference`, `run_none`, `circuitCore_correct` and
  `ofText_of_emitted`: only `propext`, `Classical.choice` and `Quot.sound`.
- **The CLI runs what the theorem is about.** `cli` → `Contract.build` → `Contract.buildCore`,
  which `build_correct` is about.
- **No `partial` / `unsafe` / `implemented_by` / `opaque` / `extern` in code the theorems mention.**
  The only ones are in `Damp/Lang/Syntax.lean` (macros and the declaration-time check), and
  Lean core's `Json.pretty` / `Json.parse` (documented).

## 2. The edge graph

Semantics, and what connects them:

- **T** = theorem.
- **D(n)** = differential test, n cases.
- **—** = nothing.

```
 surface Lean (CircuitM)  ──T (Interface: Uint.Means, Runs, mkCircuit_run; partial)──►  IR Circuit
        │
        └─ D (test/oracle.sh, golden.sh: verifier keys = compactc's, Examples/Bench) ─► compactc output

 IR Circuit.run (p)  ──T Pass.Sound/SoundFor──►  Circuit.run (f c)
      │                                              │
      │  !! F2: nothing relates Emit.pruned (f c) to Emit.pruned c
      │                                              │
      │                                         T pruned_run (one way) / compile_exact (Emit.pruned)
      ▼                                              ▼
 Exec.run (Spec) ──T run_accepted(_by_emitted), run_none──►  IrSource.run (Lean port of preprocess)
      │                                                         │
      │ D(307: 192 example calls + 115 synthetic;               │ D(2,774 vectors + 115 audit edge vectors;
      │   test/executor.sh)                                     │   crypto 125 cases; test/semantics.sh)
      ▼                                                         ▼
 executor.mjs (+ compact-runtime) ─── D(test/run.mjs, bench.mjs) ──► zkir-v3 `check` (off-circuit)
      │                                                         │
      │  F1: user witnesses see σ; the Spec's do not (—)        │ — (upstream Agda proof, ZKIR 3.0 only)
      ▼                                                         ▼
 Ledger model (Vm.lean, Query.lean) ── D(~27,000 vm.sh vectors) ──► onchain-runtime VM      zkir-v3 circuit + prover
      │
      └─ T Pass.SoundLedger (ledger passes, from WF σ, witnesses blind to σ)
         D(test/ledger-opt.sh: 99 calls, o2 vs lo) — no user witness in it reads the ledger
         D(test/calls-isolation.sh) for CallIsolated
```

Thin or missing edges:

- **pruned shipped ZKIR ↔ unpruned source (F2): nothing.**
- **The Spec's witness oracle ↔ real witnesses (F1): nothing.** `test/executor.sh` replays the
  recorded answers, so it cannot see that an answer depended on σ.
- **`--O3` folded constants ↔ runtime (F3): thin.**
- **`zkir-v3 check` (off-circuit `preprocess`) ↔ the constraint system the prover uses:
  trusted.** No test here runs a real proof of a forged witness; `audit-o3-range.mjs` uses
  `check`.
- **`ledgerView` / JS value conversion ↔ field elements: tested only through calls.**

## 3. Hypotheses of the top theorems

| hypothesis | where | satisfiable / witness | checked at build? | a program that violates it |
|---|---|---|---|---|
| `Emit.circuit (f c) = .ok src` | `compile_*`, `build_correct` | every example | yes, the build fails otherwise | not shipped |
| `c.checkDisclosure = .ok ()` | `build_correct`, `groups_noninterference` | examples | yes | not shipped |
| `checkLedger` | `run_groups_fromLedger` | examples; kept by passes (`*_checkLedger`) | yes | not shipped |
| `σ.WF` (`decodeEffects σ.effects = some σ.effects`) | every `Pass.SoundLedger` | 27,350 + 6,865 real states, all WF | no (a runtime property) | the theorem says nothing; none found |
| `level.SoundAt p` (p = `Crypto.prims` at `--O3`) | `ShippedOK` / `ShippedLedgerOK` | `Crypto.prims` | n/a | if the runtime's hashes differ, `--O3` constants are wrong (F3) |
| `AlignChecked Crypto.prims` | `hashRanges_soundFor` | proved (`prims_alignChecked`) | n/a | (F2 breaks `hashRanges` anyway) |
| `CallIsolated C c` | `runC_eq_run`, `Pass.SoundLedger.runC` | tested (`calls-isolation.sh`); re-entrancy refused by the runtime | no | a runtime that allowed re-entry would void it (documented) |
| witness oracle independent of σ | built into the `Oracles` type, so into every executor theorem | **false for the shipped executor** | no | F1 |
| `Text.lex text = .ok (toks …)` | `ofText`, `build_contractJson` | tested (`jsontext.sh`) | no | Lean core's `Json.pretty` |
| `Uint.Means`, builder lengths | Interface theorems | per-theorem | no | documented in DESIGN.md §4 |

## 4. Mutation testing of the verification path

Run on a scratch worktree, one mutation at a time, each reverted before the next (`git status`
clean after each batch). Columns:

- (i) a Lean proof breaks;
- (ii) a test suite catches it (`#guard`s in `Examples`, or the named script);
- (iii) nothing notices.

| id | mutation | (i) proof | (ii) test | (iii) |
|---|---|---|---|---|
| M02 | `Bounds2`: keep relational facts when a variable is rebound | **breaks** (`Proofs/Optimize/Bounds2.lean:325`) | | |
| L04 | `AssertEq`: `e == k ↦ e` for any constant `k` | **breaks** (`AssertEq.lean:51`) | | |
| L05 | `hashRanges`: drop the slot-width condition | **breaks** (`HashRanges.lean:575`) | | |
| L11 | `ledgerDeadStore`: drop `droppableValue` | **breaks** (`LedgerDeadStore.lean:130`) | | |
| L15 | `Simplify`: `0*e ↦ 0` without `total` | **breaks** (`Simplify.lean:172`) | | |
| L13 | emitter: `zeroShift` with the wrong sign | **breaks** (`Proofs/Emit.lean:1246`) | | |
| L09 | disclosure: stop checking ledger guards | **breaks** (`Proofs/Disclosure.lean:194`) | | |
| L10 | `Ty.ranges`: `Uint` bound off by one | **breaks** (`Proofs/Interface.lean:645`) | | |
| L01 | barrier: `createZswapOutput` no longer a `ctxWitness` | no | **yes**: `Examples` `#guard`s (OptLedgerDeadStore/Reuse/Hoist); `lo_barrier` in `ledger-opt.sh` (claimed, not rerun) | |
| L02 | barrier: `keepsAcrossWitness` always true | no | **yes**: `Examples.OptLedgerReuse` `#guard`s | |
| L03 | barrier: `lcommutes` ignores `ctxWitness` | no | **yes**: `Examples` `#guard`s (OptLedgerHoist, OptLedgerMergeEffects) | |
| J1 | JS: run a zero-result witness when the guard ≠ 0 (not = 1) | n/a | **yes**: `executor.sh` (1 call) | |
| J2 | JS: inactive ledger statements declare unzeroed public inputs | n/a | **yes**: `executor.sh` (59 calls) | |
| J3 | JS: `assert` accepts any non-zero condition | n/a | **yes**: `executor.sh` (1 call) | |
| J5 | JS: range checks never fail | n/a | **yes**: `executor.sh` (13 calls) | |
| J4 | JS: push zeros onto `st.priv` for a witness not asked | n/a | no | **survives** (equivalent: `st.priv` is dead, F6) |
| L14 | emitter: pruning stops counting witness arguments as live | **breaks** (`Proofs/Prune.lean:198`) | | |
| L08 | VM model: `addi` adds one too many | **breaks** (`Proofs/Ledger/Counter.lean:61`) | (`vm.sh` would too; not rerun) | |
| L06 | `lt` means `≤` in **both** the IR and the ZKIR port (consistent, so the emitter proof holds) | **breaks** elsewhere: `Proofs/Optimize/Simplify.lean:201` (constant comparison folding), `Proofs/Interface.lean:307` | (`semantics.sh` would too) | |
| L17 | zero-result witnesses never run, in **both** the Lean spec and the JS | **breaks** (`Proofs/Executor.lean:138`, `Proofs/Optimize/LedgerReuseBase.lean:153`) | | |
| J6 | JS: user witnesses see a stale ledger (the state at the first witness call, not the current one) | n/a (the Spec has no notion of it) | no: `executor.sh` 307/307 agree; no test in the repository has a witness that reads `ledger` | **survives** (F1's blind spot) |
| J7 | JS: drop the check that a callee's recorded output is its declared result | n/a | no: `executor.sh` 307/307 agree (the call suites have only honest callees; not rerun) | **survives** (likely) |

What the table says:

- Every rewrite rule's side condition is pinned by a proof.
- The syntactic barrier is pinned only by `#guard` regressions and one runtime test. That is
  adequate for what it does, but it is the wrong barrier (F1).
- The JS executor is pinned by the conformance test, for the clauses it compares.

The holes found by this audit (F1, F2) would survive every mutation-style check: in both, the
theorem is true and the test corpus contains no program of the shape that breaks.

## 5. Trusted base

To believe that "the shipped circuit behaves as the source program", at each level, one must
believe the following.

**At every level:**

- the Lean kernel and core (`propext`, `Classical.choice`, `Quot.sound`);
- that the IR value is the program the user meant (the surface → IR step is covered by the
  Interface theorems only for what they state);
- `Damp/Zkir/Semantics.lean` = zkir-v3 `check` (tested: 2,774 + 115 vectors);
- zkir-v3 `check` = the constraint system and prover (upstream; the Agda proof covers ZKIR 3.0 and
  is not 3.2);
- Lean core's `Json.pretty` writes text that lexes as `Text.toks` (tested, `jsontext.sh`);
- Midnight's Rust loader reads the `.zkir` as Damp's reader does (tested, `loader.sh`);
- the pinned versions: compactc 0.36.1, runtime 0.21.0, zkir 3.2.x.
- **Missing today (F2):** a theorem that the shipped ZKIR accepts no more than the source. Until
  it exists, every level depends on the passes not exploiting dead bindings, and they do.

**For the executor (any level):**

- `executor.mjs` = `Exec.run` (tested, 307 calls);
- JS ↔ field-element conversion, `ledgerView`;
- the runtime's built-ins (`createZswapOutput`, …) and `crossContractCall`;
- the user's witnesses. The Spec assumes they do not read the ledger, which is false (F1).

**`--O3` adds:**

- `Crypto.prims` = the runtime's Poseidon and SHA-256 persistent hash. This is tested on 125
  direct cases and never on a folded constant end to end (F3).

**`--ledger-opt` adds:**

- the VM model (`Vm.lean`, `Query.lean`) = the onchain runtime (tested, about 27,000 vectors);
- `σ.WF` of the starting state (holds on every recorded real state);
- `CallIsolated` (tested);
- the syntactic barrier `ctxWitness` for `createZswapOutput` and `call:` (tested by `lo_barrier`
  and `#guard`s), which is insufficient (F1);
- that the public transcript replayed on chain against a different state behaves as the executor
  run (F4, not stated anywhere);
- gas (not modelled).

**`#guard`-only checks** (no theorem):

- the barrier positions;
- `ledgerHoist` and `ledgerMerge` changing no rows (`ledger-opt.sh`);
- the `parseCli` refusal of `--no-opt --ledger-opt`;
- the depth-32 size bounds of the substituting passes.

## 6. Claims in DESIGN.md §2.6 and §4 stronger than what is proved

1. §2.6: "A circuit must not start accepting inputs it used to reject … Each rule carries that side
   condition." False for the shipped ZKIR at every level (F2).
2. §4 "Every pass … is proved sound … the pass changes neither what a run produces that anyone can
   observe". True of `Circuit.run`. "Anyone" includes the verifier, which runs the pruned ZKIR,
   where it is false (F2).
3. §4 "What the proofs do not give: the converse of `pruned_run` … constrains nothing in the
   emitted circuit". This understates it. With the optimizer, the dead binding is not only
   unconstrained; it also licenses dropping checks on live code (rows 4 and 5 of F2), and passes
   make live failing bindings dead (rows 1–3 and 6–8).
4. §2.6 `HashRanges`: "a range check on a value that a later persistent hash **certainly** reads".
   Not certainly: the hash can be in a binding the emitter prunes (F2, row 5).
5. §2.6, the witness barrier: "The model of the VM and the executor treat every witness as leaving
   the ledger state alone". True, but the issue is reading. The text names `createZswapOutput` and
   `call:` as the only gaps; every user witness is one (F1).
6. §2.6 "*Guaranteed* (`Pass.SoundLedger`) … the rewritten circuit completes exactly when the
   original does, with the same outputs, private transcript…". This holds only for witnesses
   independent of the ledger. The shipped executor's are not, and outputs differ in practice (F1).
7. §4, the table entry for `Exec.optimize_correct`, "for every oracle". This means every oracle of
   the `Oracles` type, which cannot express a ledger-reading witness. For the `Pass.Sound` passes
   this is harmless in practice: they keep the ledger statements and their order relative to
   witnesses. The definition does not require that order, though.
8. §4 "`--O3` … that they compute what Midnight's runtime and proof system compute is tested".
   It is tested on the crypto corpus, but no test exercises a folded constant through the runtime
   (F3).

## 7. Not examined

- Whether the actual constraint system or prover (`zkir-v3 prove`, not `check`) agrees with
  `preprocess` on the edge vectors.
- Gas limits per request (relevant to `ledgerMerge`'s cap).
- Re-entrancy beyond what `calls-isolation.sh` covers.
- The surface-language elaborator (`if` rewriting) beyond what the Interface theorems state.
- `Export` ↔ `executor.mjs`'s reading of `contract.json` field by field (covered only through
  `executor.sh`).
- The `nm`/`lo` gas claims in DESIGN.md.
- Running the full `test/full.sh` under each mutation; only targeted scripts were run (see §4).

## 8. Files

- `test/audit/run.sh`: runs everything below; one line per test.
- `test/audit/Prune.lean`: F2, 8 circuits. **Fails (gap).**
- `test/audit/HashRange.lean` + `executor/test/audit-o3-range.mjs`: F2 end to end at `--O3`, real
  checker. **Fails (gap).**
- `test/audit/LedgerWitness.lean` + `executor/test/audit-ledger-witness.mjs`: F1 through the real
  runtime. **Fails (gap).**
- `executor/test/audit-zkir-edges.mjs`: 115 operator edge vectors for `damp-semantics-test`.
  Passes.
- `test/audit/WfStates.lean`: `σ.WF` on `test/vm.sh`'s real states. Passes.

Run on 2026-11-23, on a scratch worktree of `ccd590e`, with `test/vm.sh`'s vectors from
`build/vm-ledger`, in 7 s once built:

```
FAIL  prune-widening             gap F2: 8 of 8 circuits widened (see build/audit/prune.log)
FAIL  o3-range-forgery           gap F2: FAIL o3: honest w=200 accept; forged w=1000 (not a Uint<0..256>) accept
FAIL  ledger-opt-witness         gap F1: audit-ledger-witness: 3 of 4 checks FAILED (expected: finding F1)
PASS  zkir-edge-vectors          vectors: 115 ok, 0 FAIL
PASS  wf-real-states             WF: starting effects 27350 of 27350 well formed; effects after a successful query 6865 of 6865
```

---

## Status after fixes

Added after the audit (the findings above are unchanged, as found at `ccd590e`). Each fixed finding
is guarded by a theorem where one exists and by tests that failed at `ccd590e` and must now pass;
`test/full.sh` runs them all, `test/audit/run.sh` included.

| finding | status | fix | guarded by |
|---|---|---|---|
| **F2** (pruning widens the shipped ZKIR) | **fixed** | The emitter drops an unused binding only when its expression cannot fail where it stands (`Emit.pruneDeadBinds`: `Bounds.totalB` with the facts the statements before establish, and with the variables later kept statements need to be 0 or 1 taken as such); a binding that might fail is kept and emitted, as compactc keeps a dead checked cast. The missing direction is now a theorem: `Emit.pruned_run_eq` (the pruned circuit runs exactly as the circuit), `Emit.circuit_exact` (the ZKIR means exactly the circuit it is emitted from, unused bindings included), `Pass.SoundRun.pruned`, `shipped_sameFor`, `shipped_preprocessFor` and `shipped_optimize_preprocess` / `shipped_optimizeFull_preprocess` / `shipped_optimizeMax_preprocess` (`Damp/Proofs/Shipped.lean`): at every level the shipped ZKIR accepts a preimage under Midnight's `preprocess` exactly when the `--no-opt` ZKIR does, with the same outputs and active public inputs (at `--O3` for `Crypto.prims`). `build_correct` carries it: `ShippedBase.exactSource`, `ShippedOK.complete` (now an equation), `ShippedOK.sameAsNoOpt` | `test/audit/run.sh` rows `prune-widening` (the 8 circuits of `test/audit/Prune.lean`, with guards that `--no-opt` still refuses each input) and `o3-range-forgery` (Midnight's checker); `test/prune-sound.sh` (`Examples/PruneSound.lean`, every level, the checker, the JS executor); `test/executor.sh` cases `dead_fail`, `dead_mul0`, `dead_eqself`, run as written and as the default level, `--O2` and `--O3` ship them, through `executor.mjs`, `Exec.run` and the ZKIR of each level |
| **F1** (`--ledger-opt` moves writes across a witness that reads the ledger) | **fixed** | The executor's definition gives every witness the ledger state and takes it back (`Exec.WitnessOracle ω σ`, `Damp/Executor/Spec.lean`). `Pass.SoundLedger` quantifies over every witness oracle meeting `Ledger.WitnessesOK` (`Damp/Executor/Witnesses.lean`: a user's witness reads and keeps the ledger, `createZswapOutput` writes call-context slot 1 only, `ownPublicKey` / `createZswapInput` / calls are isolated). The passes' barriers are now hypotheses their proofs use (`stateWitness` in `ledgerDeadStore`, `isolatedWitness` in `ledgerMerge`, `ctxWitness` in `ledgerReuse` / `ledgerHoist`); `Examples/WitnessBarrier.lean` shows for each that the pass without it changes what a circuit does under an oracle meeting `WitnessesOK` | `test/audit/run.sh` row `ledger-opt-witness` (the real runtime); `lo_witness` and `lo_barrier` in `test/ledger-opt.sh`; `test/witness-effects.sh` (the footprints, on the runtime); `Examples/WitnessBarrier.lean`. Mutation J6 (a JS witness sees a stale ledger) is now caught by `test/executor.sh` (case `peek`, a witness reading the ledger between two writes) |
| **F3** (`--O3` folded constants never run end to end) | **fixed (test)** | `test/o3-fold.sh`: a contract whose `check` requires hashes of literals, constants at `--O3` (its ZKIR has no hash instruction left), to equal hashes the runtime computed in an earlier call; both calls succeed through the executor and the runtime at `--O2` and `--O3`, the result equals the runtime's own `persistentHash` / `transientHash`, Midnight's checker accepts the proof data and refuses it with a ledger read changed | `test/o3-fold.sh`. Still a test, not a theorem: `Crypto.prims` = the runtime's hash functions is trusted |
| **F4** (on-chain replay from a different state; gas) | open | nothing stated; gas is measured (`test/ledger-opt.sh`), not modelled | — |
| **F5** (noninterference of what ships) | **fixed without `--ledger-opt`**, open with it | `shipped_noninterference` (`Damp/Proofs/Build.lean`), carried by `ShippedOK.noninterference`: two runs the shipped ZKIR accepts with the same ledger reads, whose disclosed values (as the original circuit computes them) agree, have the same active public inputs; from `groups_noninterference`, `Emit.circuit_exact` and `Pass.SoundFor.run`. With `--ledger-opt` the public inputs differ by design and nothing is transferred (`ShippedLedgerOK`'s docstring) | the theorem |
| **F6** (`st.priv` in `executor.mjs` written, never read) | open | unchanged | — |

Mutations of §4 revisited:

- **J6** (stale ledger for JS witnesses): caught by `test/executor.sh` (`synthetic … peek`: the
  definition fails at the second `assert`, the case expects success). Checked by applying the
  mutation to a scratch copy of `executor/`.
- **J7** (callee output check dropped): caught by `test/executor.sh` (call `caller.via(liar, 4)`: the
  private transcript the definition records differs from the preimage's) and by `test/all.sh`
  (`caller.via(liar, 4)` must fail in every chain whose caller is Damp's). `liar`
  (`executor/test/calls.mjs`) is the adder's module and keys returning a result one more than the
  output it records. compactc's generated caller does not make this check and accepts the call.
  Checked on a scratch copy of `executor/`.
