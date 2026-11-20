# Benchmarks: Damp against compactc on real Compact programs

`test/bench.sh` compiles 23 Compact programs with compactc 0.36.1 (`--skip-zk`), builds the same
programs written in Damp (`Bench/*.lean`) at four levels (`--no-opt`, default, `--O2`, `--O3`), and compares
the ZKIR circuits instruction by instruction and row by row. The aim is evidence for the optimizer:
where does Damp's output differ from compactc's, in which direction, and what is still left to remove.

```
test/bench.sh                      # everything below, about 20 s
BENCH_SKIP_EXEC=1 test/bench.sh    # without the executor comparison
```

| File | Role |
|---|---|
| `bench/compact/*.compact` | the Compact sources as compiled (changes from the originals are in each file's header and listed below) |
| `Bench/*.lean`, `Bench.lean`, `BenchMain.lean` | the Damp ports; `lake exe damp-bench [--no-opt \| --O2 \| --O3] DIR` builds them (`damp-bench` is not a default target) |
| `bench/report.py` | the table, totals, ranked lists; writes `build/bench/results.json` |
| `bench/headroom.py` | what a sound optimizer could still remove from a circuit (`build/bench/headroom-*.json`) |
| `bench/zdiff.py` | canonical text and diff of two ZKIR files (`--normalize`, `--multiset`, `--show`) |
| `bench/costs.py` | rows each ZKIR instruction adds; with `--attribute ROOT VARIANT`, the rows each kind of instruction accounts for in every circuit |
| `executor/test/bench.mjs` | the behavioural comparison, run by `test/bench.sh` |

Numbers below are from one run of `test/bench.sh` on the tree after commit c627efe plus the
uncommitted work of this round (the final ports of `election_core`, `zerocash_core` and `adt_merkle`,
the new `proof_data` and `zkir_generation`, and the optimizer of `Damp/Optimize/Pipeline.lean` as
described in "Optimizer levels"). Rows are the `rows` of `zkir-v3 mock-compile`. "Same" in the table:
`=` the default Damp circuit is compactc's up to variable names; `~` after `test/zkir-normalize.py`;
`c` after that and dropping compactc's `copy` instructions; `x` it differs.

## The programs

Ported faithfully: same circuits, same ledger, same logic, written the way the Damp docs write them (an
`if` statement is `if%`, a ternary is `select` or, when a branch reads the ledger or calls a witness,
an `if` expression, which evaluates only the branch taken; a `for` is a Lean `for`; a helper `circuit`
is a `def`; no hand-optimization, no mimicking of compactc's instruction order). A circuit that never
touches the ledger gets no ZKIR from compactc (or Damp) and is not in the table.

| Program | Source | What it exercises | Changes to the Compact source |
|---|---|---|---|
| `counter` | examples/counter.compact | a counter | none |
| `tiny` | examples/tiny.compact | enum state machine, `Maybe`, a witness, `persistentHash`, a constructor | none |
| `test01` | test-center/compact/test01.compact | tiny plus arithmetic: `(v + 1 - 1) * 2`, `Field as Uint<16>`, `x + 2 != 5` | `temp: Bytes<32>` became `temp: Field` and `(temp as Field) + 2 != 5` became `temp + 2 != (5 as Field)` (compactc 0.36.1 rejects the original: Field vs Uint<0..6>; Damp has no `Bytes as Field`) |
| `threading` | test-center/compact/threading.compact | counter compared and cast, `&&` guarding a ledger read, two witness calls | none |
| `gas_cost` | test-center/compact/gas-cost.compact | `Set.insert`/`remove` | none |
| `block_time` | test-center/compact/block-time.compact | the four block-time comparisons | none |
| `unshielded_tokens` | test-center/compact/unshielded-tokens.compact | 20 token circuits: mint/send/receive unshielded and shielded coins, to self, a contract and a user | none |
| `coracle` | examples/camelCase/new/coracle.compact | a two-player game with a pot of shielded coins: hashes and commitments, enums, structs, `Maybe`, six ledger fields, `sendShielded`, `mergeCoinImmediate`, `writeCoin` | `disclose` added to the `wager`/`deposit` parameters of `start`, to the results of `is_red`/`is_blue` and to the guess stored in `last_guess` (compactc 0.36.1's disclosure analysis rejects the 0.33 text); `Committable<A>`/`Commitment<A>` are written for `A = Board` in Lean |
| `election_core` | examples/election.compact | the election state machine: `MerkleTree`, `MerkleTreePath` witnesses and `merkleTreePathRoot`, `Set`, `Counter`, nullifiers by `persistentHash`, 7 witnesses | `Opaque<"string">` topic became `Field`; `$` in names became `_` |
| `zerocash_core` | examples/zerocash.compact | commitments, nullifiers, `HistoricMerkleTree<32>` with a `MerkleTreePath<32>` witness and `merkleTreePathRoot`, nested single-field structs | the `Opaque<"Uint8Array">` encryption field, ciphertext ledger field and `context$encrypt` witness removed, with the two statements of `spend` that use them; `$` in names became `_`; `commitments` exported so the behavioural test can read its root |
| `pm_19287` | examples/bugs/pm-19287.compact | loops over vectors and matrices returned by helper circuits, accumulating into 11 ledger fields; `Field as Uint<64>` comparisons; a 10-circuit driver | none |
| `pm_20028` | examples/bugs/pm-20028/examples.compact | `Uint<248>`/`Uint<247>`/`Uint<64>` casts down and up, comparison across widths, subtraction | `module N<#n>` with its prefixed import and `test3` removed; `test10` (`Uint<0>`, no ledger) not ported |
| `types` | examples/types/examples.compact | maps keyed and valued by aliases, map of maps, loop inserting into a map | only the ledger-touching circuits (test10, test10a, test16); the rest never touches the ledger |
| `assert_misc` | examples/assert/example_one.compact | structs in maps, `Field as Uint<16>` then `Counter.increment`, a map of counters | only `ellen`, `myswitch`, `abel` and their ledger fields |
| `adt_counter` | examples/adt/tests/counter.compact | `Counter` read/increment/decrement/reset and assertions | none |
| `adt_list_struct` | examples/adt/tests/list_struct.compact | a ledger list of a struct holding coins | none |
| `adt_map_list` | examples/adt/tests/map_field_list_field.compact | a map whose values are ledger lists | none |
| `adt_merkle` | examples/adt/tests/{merkletree,historicmerkletree}_field.compact | `MerkleTree` and `HistoricMerkleTree` insert variants, `MerkleTreePath` ledger fields, `merkleTreePathRoot`, `isFull`, reset | the two files joined: ledger fields declared together, the historic file's `partialTree` renamed `historicPartialTree`, one shared `path` |
| `composable_inner`, `composable_outer` | test-center/composable/Basic/{Inner,Outer}.compact | storing and calling another contract | none |
| `vectors` | examples/vectors/spread_part_one.compact | spreads into ledger vectors, a `Map` of vectors, a 100-iteration loop, `slice` | only test1b, test2, test4, with dead statements removed; `slice_to_ledger` added (modelled on slice_part_one.compact) |
| `proof_data` | examples/casts/proof_data.compact | casts between `Bytes<5>` and `Vector<5, Uint<8>>` of ledger fields | none |
| `zkir_generation` | examples/casts/zkir_generation.compact | `Vector<n, Uint<8>>` to `Bytes<n>` and back, a `Counter` | none |

90 circuits in all. Where a port first used a different idiom than Compact's text (for example `require
(← c.isEmpty)` for `assert(c.isEmpty() == true, ..)`) the numbers changed, so the ports now follow the
text: `== true` stays `==. .true`.

## Results

```
circuit                                                             instructions                                    rows  same
                                               compactc  no-opt default      O2    compactc   no-opt  default       O2
adt_counter.test_all                                 42      42      42      41         125      125      125      123  =
adt_counter.test_big_increment                       18      18      18      18          64       64       64       64  =
adt_list_struct.test                                424     427     424     418        1329     1332     1329     1317  =
adt_map_list.test                                    92      92      92      87         250      250      250      240  =
adt_merkle.test                                     220     217     217     215       18797    16776    16776    16772  c
adt_merkle.test_historic                            345     341     341     339       23176    21155    21155    21151  c
assert_misc.abel                                     18      18      18      18          77       77       77       77  =
assert_misc.ellen                                    31      31      31      31         139      139      139      139  x
assert_misc.myswitch                                 36      32      30      30         414      131      128      128  x
block_time.testBlockTimeGt                            8       8       8       8          78       78       78       78  =
block_time.testBlockTimeGte                           9       9       9       9          80       80       80       80  =
block_time.testBlockTimeLt                            8       8       8       8          78       78       78       78  =
block_time.testBlockTimeLte                           9       9       9       9          80       80       80       80  =
composable_inner.add                                 13      13      13      13          78       78       78       78  =
composable_outer.add                                 18      18      18      18         125      125      125      125  =
composable_outer.addViaConst                         18      18      18      18         125      125      125      125  =
composable_outer.echoStored                           6       6       6       6          57       57       57       57  =
composable_outer.setInner                            11      11      11      11         157      157      157      157  =
coracle.concede                                     311     343     298     298       50473    50542    50468    50468  x
coracle.guess                                       184     182     182     182       15592    15590    15590    15590  x
coracle.start                                       267     267     253     253       59578    59580    59565    59565  x
coracle.withdraw                                    384     444     362     362       85226    85355    85219    85219  x
counter.increment                                     3       3       3       3          31       31       31       31  =
election_core.add_voter                              73      73      73      73        5972     5972     5972     5972  =
election_core.advance                                32      32      32      32        3898     3898     3898     3898  =
election_core.set_topic                              24      24      24      24        3884     3884     3884     3884  =
election_core.vote_commit                           132     132     131     131       15552    15553    15552    15552  c
election_core.vote_reveal                           126     127     125     125        9904     9907     9904     9904  x
gas_cost.testGasCost                                  9       9       9       9          48       48       48       48  =
pm_19287.test                                       880    1109     874     874        2585     3496     2581     2581  x
pm_19287.test_circuit_calls_in_loop                  80      93      80      80         243      254      243      243  =
pm_19287.test_circuit_returned_tuple                 28      55      26      26          97      222       97       97  c
pm_19287.test_circuit_returned_vector                48      54      48      48         155      162      155      155  =
pm_19287.test_complex_nested_patterns                56     213      56      56         177      914      177      177  =
pm_19287.test_concatenated_circuit_results           88     100      88      88         265      279      265      265  =
pm_19287.test_conditional_circuit_calls             104     118     104     104         309      326      309      309  =
pm_19287.test_dynamic_vector_processing             266     296     266     266         773      808      773      773  =
pm_19287.test_nested_circuit_matrix                  56      56      56      56         177      177      177      177  =
pm_19287.test_recursive_style_processing            122     120     119     119         363      361      360      360  x
pm_19287.test_vector_slicing_with_circuits           41      45      40      40         134      139      133      133  x
pm_20028.test1                                        4       4       4       4          35       35       35       35  =
pm_20028.test2                                        4       4       4       4          35       35       35       35  =
pm_20028.test4                                       10      10      10      10         195      195      195      195  =
pm_20028.test5                                        8      11       8       8          45      101       45       45  =
pm_20028.test6                                        8       8       8       8          45       45       45       45  =
pm_20028.test8                                       16      16      16      16          67       67       67       67  =
pm_20028.test9                                       20      20      20      20          99       99       99       99  =
pm_20028.test_cast_comparison                        26      26      26      26          91       91       91       91  =
proof_data.test1                                     10       9       9       9         662      662      662      662  c
proof_data.test2                                     13      17      17      17         634       54       54       54  x
test01.clear                                         30      30      30      29        3904     3904     3904     3902  =
test01.get                                           11      12      11      11          68       69       68       68  =
test01.set                                           34      33      29      29        3933     3933     3929     3929  x
threading.fib                                        36      34      34      34         120      118      118      118  x
threading.fib2                                       14      14      14      14          78       78       78       78  =
tiny.clear                                           30      30      30      29        3904     3904     3904     3902  =
tiny.get                                             11      12      11      11          68       69       68       68  =
tiny.set                                             21      21      21      21        3887     3887     3887     3887  =
types.test10                                         12      12      12      12         216      216      216      216  =
types.test10a                                        12      12      12      12          75       75       75       75  =
types.test16                                         76      76      76      76         338      338      338      338  =
unshielded_tokens.getUnshieldedBalanceGtTest         18      18      18      18         215      215      215      215  =
unshielded_tokens.getUnshieldedBalanceLtTest         18      18      18      18         215      215      215      215  =
unshielded_tokens.getUnshieldedBalanceTest           15      15      15      15         155      155      155      155  =
unshielded_tokens.mintShieldedToContractTest         53      57      53      53        9865     9871     9865     9865  =
unshielded_tokens.mintShieldedToSelfTest             56      60      56      56        9789     9795     9789     9789  =
unshielded_tokens.mintShieldedToUserTest             39      57      39      39        9832     9870     9832     9832  =
unshielded_tokens.mintUnshieldedToContractTest       69      70      69      69        4144     4145     4144     4144  =
unshielded_tokens.mintUnshieldedToSelfTest           72      73      72      72        4068     4069     4068     4068  =
unshielded_tokens.mintUnshieldedToUserTest           45      70      45      45        4091     4146     4091     4091  =
unshielded_tokens.receiveShieldedTest                18      20      18      18        5898     5901     5898     5898  =
unshielded_tokens.receiveUnshieldedTest              19      19      19      19         180      180      180      180  =
unshielded_tokens.sendImmediateShieldedToContractTest       75      79      68      68       23483    17857    17843    17843  c
unshielded_tokens.sendImmediateShieldedToSelfTest       78      82      71      71       23407    17781    17767    17767  c
unshielded_tokens.sendImmediateShieldedToUserTest       64      79      59      59       17824    17857    17822    17822  c
unshielded_tokens.sendShieldedToContractTest         76      80      69      69       23521    17895    17881    17881  c
unshielded_tokens.sendShieldedToSelfTest             79      83      72      72       23445    17819    17805    17805  c
unshielded_tokens.sendShieldedToUserTest             65      80      60      60       17862    17895    17860    17860  c
unshielded_tokens.sendUnshieldedToContractTest       61      62      61      61         364      365      364      364  =
unshielded_tokens.sendUnshieldedToSelfTest           64      65      64      64         288      289      288      288  =
unshielded_tokens.sendUnshieldedToUserTest           37      62      37      37         311      366      311      311  =
vectors.slice_to_ledger                               3       3       3       3         132      132      132      132  =
vectors.test1b                                        6       6       6       6          75       75       75       75  =
vectors.test2                                        23      23      23      23         158      158      158      158  =
vectors.test4                                       500     500     500     500        1624     1624     1624     1624  =
zerocash_core.spend                                 269     268     268     268       24011    24011    24011    24011  c
zerocash_core.zerocash_mint                          33      33      33      33        7784     7784     7784     7784  =
zkir_generation.increment                             3       3       3       3          31       31       31       31  =
zkir_generation.test1                                27      36      36      36        1499      203      203      203  x
zkir_generation.test2                                 9       7       7       7          41       41       41       41  c
TOTAL                                              6940    7652    6826    6808      533476   507125   504667   504631
```

The `--O3` column is printed separately by `test/bench.sh` (only where it differs from `--O2`):

```
--O3 where it differs from --O2                           instructions              rows
adt_merkle.test                                            215 -> 201      16772 -> 2626    
adt_merkle.test_historic                                   339 -> 323      21151 -> 4985    
coracle.concede                                            298 -> 288      50468 -> 50148   
coracle.guess                                              182 -> 176      15590 -> 15398   
coracle.start                                              253 -> 240      59565 -> 59149   
coracle.withdraw                                           362 -> 348      85219 -> 84771   
election_core.add_voter                                     73 -> 69        5972 -> 5844    
election_core.advance                                       32 -> 30        3898 -> 3834    
election_core.set_topic                                     24 -> 22        3884 -> 3820    
election_core.vote_commit                                  131 -> 127      15552 -> 15424   
election_core.vote_reveal                                  125 -> 121       9904 -> 9776    
test01.clear                                                29 -> 27        3902 -> 3838    
test01.set                                                  29 -> 27        3929 -> 3865    
tiny.clear                                                  29 -> 27        3902 -> 3838    
tiny.set                                                    21 -> 19        3887 -> 3823    
unshielded_tokens.mintShieldedToContractTest                53 -> 47        9865 -> 9673    
unshielded_tokens.mintShieldedToSelfTest                    56 -> 52        9789 -> 9661    
unshielded_tokens.mintShieldedToUserTest                    39 -> 33        9832 -> 9640    
unshielded_tokens.mintUnshieldedToContractTest              69 -> 67        4144 -> 4080    
unshielded_tokens.mintUnshieldedToSelfTest                  72 -> 70        4068 -> 4004    
unshielded_tokens.mintUnshieldedToUserTest                  45 -> 43        4091 -> 4027    
unshielded_tokens.receiveShieldedTest                       18 -> 13        5898 -> 5738    
unshielded_tokens.sendImmediateShieldedToContractTest       68 -> 60       17843 -> 17587   
unshielded_tokens.sendImmediateShieldedToSelfTest           71 -> 65       17767 -> 17575   
unshielded_tokens.sendImmediateShieldedToUserTest           59 -> 51       17822 -> 17566   
unshielded_tokens.sendShieldedToContractTest                69 -> 61       17881 -> 17625   
unshielded_tokens.sendShieldedToSelfTest                    72 -> 66       17805 -> 17613   
unshielded_tokens.sendShieldedToUserTest                    60 -> 52       17860 -> 17604   
zerocash_core.spend                                        268 -> 254      24011 -> 23563   
zerocash_core.zerocash_mint                                 33 -> 27        7784 -> 7592    
TOTAL --O3                                                        6620            469263
```

### Totals

| | compactc | Damp `--no-opt` | Damp default | Damp `--O2` | Damp `--O3` |
|---|---|---|---|---|---|
| instructions | 6940 | 7652 | 6826 | 6808 | 6620 |
| rows | 533 476 | 507 125 | 504 667 | 504 631 | 469 263 |

* The default Damp circuit is compactc's up to variable names in 63 of 90, and once compactc's `copy`
  instructions are dropped in 13 more: 76 of 90 (`test/golden.sh` and `test/all.sh` check the
  verifier keys of the examples that mirror Compact programs). It is larger than compactc's by
  instructions only in `zkir_generation.test1` (+9) and `proof_data.test2` (+4), the byte-vector
  casts, and smaller by rows in both (Damp 203 and 54 rows against compactc's 1499 and 634). Everywhere else it is equal or smaller: 127 instructions fewer in 24
  circuits, mostly hashes compactc recomputes and its `copy`s.
* `--O2` differs from the default in 7 circuits (18 instructions, 36 rows): the `assert (e == 1)`
  rewrite (`assertEq`). With the restored `MerkleTreePath` checks the commitments and public keys
  that `forwardAllOpt` used to remove from `zerocash_core.spend` and the election votes are compared
  with the path's leaf, so they are no longer dead.
* `--O3` takes 35 368 rows (7.0 %) off `--O2`: 30 312 by computing hashes of constants
  (`foldHashes`, the two `adt_merkle` circuits) and 5 056 by dropping range checks that a later
  persistent hash implies (`hashRanges`, 28 circuits; see "Optimizer levels").
* `--no-opt` is larger than compactc by 712 instructions; the default pipeline takes 826 instructions
  and 2458 rows off it.

### Behavioural check

`executor/test/bench.mjs`: 119 calls on 22 programs (every file but `composable_outer`) go
through compactc's generated module and Damp's default, `--O2` and `--O3` executors; **1401 checks, all
pass**: all three succeed or all fail, results equal, proof data equal, ledger state after the call equal,
Zswap local state equal, initial states equal, and Midnight's ZKIR checker accepts each Damp proof data
against the circuit Damp emitted at each level. Where Damp's circuit is not compactc's (the
circuits the run lists at the end, see "Differences that are not size") the proof data is required to be
accepted by the checker but not to equal compactc's.

Not exercised: `composable_outer` (it calls another contract; the simulated chain of `test/world.mjs`
covers that for the existing `caller` programs); `election_core` (no constructor sets `authority`, so
every call is refused: only that all three refuse is compared; its two vote circuits therefore get no
successful run); `adt_merkle` (its circuits assert a root and then its opposite, so they always fail).
Circuits that never touch the ledger are compared as pure functions (`tiny.public_key`,
`coracle.is_red`, `coracle.is_player_alive`).

## Optimizer levels: what each adds, measured

`Damp/Optimize/Pipeline.lean` (DESIGN.md §2.6). Every level but `--O3` is proved sound for every
circuit and every choice of hash functions; `--O3` is proved sound for runs with
`Damp.Crypto.prims`, Damp's Lean implementations of Poseidon and the SHA-256 persistent hash, which
`test/semantics.sh` checks against Midnight's runtime and `zkir-v3` but which are not proved equal to
them: at `--O3` the guarantee is relative to those implementations.

| Level | Pipeline | Totals (instructions / rows) |
|---|---|---|
| default | `simplify, foldDivmod, bounds2, simplify, algebra, commuteOpt` | 6826 / 504 667 |
| `--O2` | `simplify, foldDivmod, assertEq, asserts, simplify, bounds2, simplify, algebra, forwardOpt, forwardAllOpt, commuteOpt` | 6808 / 504 631 |
| `--O3` | `simplify, foldHashes Crypto.prims`, then `--O2`, then `hashRanges` | 6620 / 469 263 |

### Where the rows are

Rows, not instructions, are what proving costs. `python3 -I bench/costs.py --attribute ROOT VARIANT`
replaces every instruction of one kind by `private_input`s for its outputs (a `persistent_hash`
together with its `bytes_into_natives`; a range check or assertion is dropped), measures the circuit
again, and sums over the suite. On the `--O3` circuits:

| kind | count | rows | share |
|---|---|---|---|
| `persistent_hash` | 96 | 439 745 | 93.7 % |
| `div_mod_power_of_two` 248 | 25 | 3 525 | 0.8 % |
| `transient_hash` | 96 | 1 866 | 0.4 % |
| `constrain_bits` 248 | 15 | 930 | 0.2 % |
| `div_mod_power_of_two` 8 | 4 | 576 | 0.1 % |
| everything else (`constrain_bits` 8..128, `less_than`, `test_eq`, `cond_select`, `assert`, ...) | | < 1 100 together | < 0.25 % |

The rest of the 469 263 rows (about 22 000) is the base cost of inputs, `impact`s and arithmetic.
Before `hashRanges` (`--O2`), `constrain_bits` 248 was 82 instructions and 5 084 rows (1.1 %),
`constrain_bits` 8 and 128 another 868. The largest circuits are all hashes:
`coracle.withdraw` 84 771 rows (16 `persistent_hash`: 82 600), `coracle.start` 59 149 (11: 58 215),
`coracle.concede` 50 148 (10: 48 790), `zerocash_core.spend` 23 563 (6: 22 544), the
`unshielded_tokens` shielded sends about 17 600 each (3: 16 899).

### What each addition saved in this suite

* **Range checks a persistent hash implies** (`hashRanges`, `--O3` only; `Damp/Optimize/HashRanges.lean`).
  A persistent hash reads a `Bytes<n>` input as one element of `8·(n mod 31)` bits and `n / 31`
  elements of 248 bits, and fails on an element that does not fit (Midnight's
  `Alignment::parse_field_repr` out of the circuit; in the circuit, `persistent_hash` decomposes each
  such element into exactly that many bytes, which constrains it the same way). Compact range checks
  a `Bytes<32>` witness result, argument or coin field when it enters the circuit and then usually
  hashes it, so the check is paid twice. The pass drops a `constrain e (bits n)` and the `bits n`
  range of a witness result when a later statement certainly evaluates a persistent hash reading the
  same expression as at most `n` bits, with no variable of it rebound in between; a value the check
  would have refused then fails the run at the hash. Measured against `--O3` without it (same tree):
  **6 778 -> 6 620 instructions, 474 319 -> 469 263 rows (-5 056, -1.07 %)**, in 28 circuits (every
  `coracle`, `unshielded_tokens` shielded and mint circuit, the `election_core` and `zerocash_core`
  key and coin checks, `tiny`/`test01` `set`/`clear`; 62 rows per 248-bit check, 2 per 8-bit, 32 per
  128-bit). In the examples: `vault.spend` 2036 -> 1972 rows, `tokens.*` 32 to 192 rows each
  (`test/opt.sh`). Proved `Pass.SoundFor Crypto.prims` (`Circuit.hashRanges_soundFor`): sound for
  any hash functions that refuse inputs not fitting their alignment (`AlignChecked p`), which
  `Crypto.prims` is proved to do; not `Pass.Sound`, since with hash functions that accept any input
  the rewritten circuit accepts more (`Examples/OptHashRanges.lean` shows it).
* **Hashes of constants** (`foldHashes`, `--O3` only): `adt_merkle.test` 215 -> 201 instructions,
  16 772 -> 2 626 rows; `test_historic` 339 -> 323, 21 151 -> 4 985. 30 instructions and **30 312
  rows**, 6.0 % of the suite's `--O2` rows. The folded constants were checked independently (Python's
  `hashlib` on `"mdn:lh"` and the 32-byte field encoding gives the same limbs as the constants in the
  `--O3` ZKIR). `Examples/OptFoldHashes.lean` checks the folding against `Circuit.run` with
  `Crypto.prims`.
* **`divmod` of constants** (`foldDivmod`, every level): nothing in this suite or in the examples.
* **Dead code** (`forwardAllOpt`, `--O2`): nothing in this suite now. With the earlier ports, which
  replaced the `MerkleTreePath` witnesses by witnesses returning a root, the commitment and public-key
  hashes of `zerocash_core.spend` and the election votes fed only a witness argument and were removed
  (15 015 rows); the restored ports compare them with the path's leaf, so they are needed. The pass
  substitutes a binding only when the substituted expression costs at most 64 instructions
  (`Circuit.forwardAll`): without a bound, a Merkle path root of depth 32 (the digest of each level
  selected on twice by the next) grew to an exponentially large expression and `damp-bench --O2` ran
  out of memory on `zerocash_core`; `Examples/OptForwardBound.lean` checks a depth-32 chain.
* **`assert (e == 1)` as `assert e`** (`assertEq`, `--O2`): `adt_list_struct` 424 -> 418 instructions
  (1329 -> 1317 rows), `adt_map_list` 92 -> 87 (250 -> 240), `adt_counter.test_all` 42 -> 41,
  `adt_merkle` -2 each, `tiny.clear` and `test01.clear` 30 -> 29: 18 instructions, 36 rows. compactc
  keeps the comparisons, so the default level does too.
* **Commutative duplicates** (`commuteOpt`, default and `--O2`): `assert_misc.myswitch` 32 -> 30
  instructions, 131 -> 128 rows. Kept only when the circuit gets smaller.

Circuits that changed, by level: default: `assert_misc.myswitch`. `--O2` (besides that): the seven
`assertEq` circuits above. `--O3` (besides `--O2`'s): the 30 listed under the results table. The
behavioural check runs every call at all three Damp levels (1401 checks pass); where a level's circuit
is no longer compactc's, its proof data is required to be accepted by Midnight's ZKIR checker rather
than to equal compactc's.

What `bench/headroom.py` still finds (instructions / rows) on Damp's default circuits: 0 dead, 0 cse,
0 fold, 0 bits, 20 / 51 repeated ledger reads (not merged: a ledger read is part of the public
transcript), 30 / 30 312 constant hashes (folded at `--O3`), 3351 / 0 adjacent impacts.

### Ideas measured and not pursued

* **Range checks implied by something other than a hash.** After `hashRanges`, 15 `constrain_bits 248`
  remain (930 rows, 0.2 %): every one is of a value that only goes to the ledger (`impact` operands:
  token colors, addresses, a stored contract address) or into arithmetic. Nothing in the circuit
  bounds those values, so the checks are needed. `less_than` and `constrain_bits` 8..128 together
  are under 0.1 %: not pursued.
* **Sharing hashes across the two arms of a conditional.** `coracle` computes the same shapes of
  hash in its red and blue branches (`withdraw`: 7 pairs, about 33 000 rows). One hash of the
  selected inputs would do, but the inputs of the second arm (a fresh `local_secret_key()` witness,
  ledger reads of the second player's coins) are produced inside that arm, after the first arm's
  ledger statements have used its hashes; witness and ledger order is observable, so the merged hash
  cannot be placed. Only `coracle.start`'s `red_pk(sk)`/`blue_pk(sk)` (one hash of a key witnessed
  before the branch, 3 741 rows, 0.8 %) has its inputs ready; merging it needs a new analysis (the
  hash's value is used only under its arm's guard) and is sound only relative to `Crypto.prims`
  (with arbitrary hash functions the dropped hash could have failed). Left for later.
* **Duplicate hashes modulo equalities.** `headroom.py cse` finds none; the remaining same-shape
  hashes in a circuit hash different witness results (a witness asked twice, as `coracle`'s
  `is_red(sk)` and the branch's own `local_secret_key()`), which the circuit cannot assume equal.
* **`div_mod_power_of_two` 248** (0.8 %): the low 31 bytes of a transient hash, which the persistent
  hash then reads; it is the value, not a check, and stays.
* **Byte/field round trips**: none found in this suite beyond the casts of `proof_data` and
  `zkir_generation`, whose four circuits total under 1 000 rows (0.2 %).

## Where Damp's default is larger than compactc's

In instructions, two circuits, both new in this round and both casts between `Vector<n, Uint<8>>`
and `Bytes<n>`: `zkir_generation.test1` 27 -> 36 and `proof_data.test2` 13 -> 17. Both are much
smaller in rows (1499 -> 203 and 634 -> 54): compactc packs the bytes with `reconstitute_field`
(about 140 rows each), Damp with one `mul` and one `add` per byte. In rows Damp's default is nowhere larger.
For the rest the evidence is the other direction, and the `--no-opt` level
shows what the default passes have to recover. The 36 circuits where `--no-opt` is larger than the
default are larger by (instructions, summed over the suite, `--no-opt` minus compactc): `cond_select`
+249, `impact` +254, `add` +75, `constrain_bits` +52, `less_than` +43, `test_eq` +38, `public_input`
+28, `mul` +27, and compactc has 58 `copy`s that Damp never emits. In circuits with constant
conditions (`for` over constant vectors, helper circuits called with literals, `Uint<64>` comparisons
of literals) Damp builds both arms of every `if%` with its guard machinery and a `constrain_bits 64`
and `less_than` on constants, where compactc's frontend has already decided the condition; example,
`pm_19287.test_complex_nested_patterns` before the default pipeline:

```
less_than  a="0x0a" b="%t" bits=64        (x18: 10 < a constant that was computed by arithmetic on literals)
constrain_bits val="%t" bits=64           (x18)
impact ... guard="%c"                     (6 instructions x18: the guarded `complex_sum` update)
```

compactc emits only the six `complex_sum` updates that the constant conditions leave.

## Where compactc's output is larger than Damp's default

24 circuits, 127 instructions and 26 933 rows in all (the table and the examples below are from
the earlier 85-circuit run; the totals per kind of difference are printed by `test/bench.sh`). By kind of difference (instructions; the
column split is `bench/report.py`'s):

| Cause | Instructions | Rows | Where |
|---|---|---|---|
| A. compactc recomputes a hash (14 instructions) and writes a constant through `copy`/`cond_select` (40) | 54 | 32 225 | sendShielded/sendImmediateShielded x6, coracle.*, adt_merkle.* |
| B. `copy` of a variable | 33 | about 60 | everywhere compactc casts or passes a value on |
| C. constants not folded: `neg c` then `add x`, `(x + a) + b`, `v + 1 - 1`, `x + 2 != 5` | 14 | about 12 | pm_19287 x3, test01.set, threading.fib |
| D. `Field as Uint<n>` lowered with `div_mod_power_of_two` | 2 | 283 | assert_misc.myswitch |
| E. repeated ledger reads | 15 | 20 | coracle.start |
| F. boolean connectives and guarded assertions | 17 | about 5 | coracle.* |

The first three columns of `bench/report.py`'s last table split the 135 as 54 (A), 33 (B) and 48 (C-F);
C-F are read off `bench/zdiff.py --multiset` per circuit. The rows of B, C, E and F are what is left of
the 32 601 after A and D (about 90 in all, each instruction costing 0 to 2 rows). I traced C, D and E to
the Compact expression that causes them; F I did not (see below).

**A. Recomputation.** compactc computes a persistent hash again each time the source asks for it
(docs/tokens.md, "Differences"); Damp shares one. In `sendShieldedToSelfTest` compactc has four
`persistent_hash` where Damp has three: the coin commitment of the output coin is hashed once for
`claimZswapCoinSpend` and again for `claimZswapCoinReceive`:

```
persistent_hash alignment=[bytes21,bytes32,bytes32,bytes16,bytes1,bytes32]
                inputs=["0x6d69646e696768743a7a737761702d63635b76315d","0x00",%n,%a,%b,%v,"0x00",%r1,%r2]   (twice)
bytes_into_natives ...                                                                                  (twice)
```

That is 5640 rows in each of the four `...ToSelf`/`...ToContract` circuits and in `coracle.start` (5691).
The same appears in `adt_merkle.test` and `test_historic`, where compactc hashes the leaf of `Field 0`
twice (`insertIndexDefault(3)` and `insert(0)` in the loop; the two `persistent_hash` instructions have
identical inputs `["0x6d646e3a6c68","0x00"]`): 2014 and 2021 rows. Total for A:
14 persistent hash/`bytes_into_natives` instructions, 32 225 rows: 98.9 % of all the rows by which
compactc is larger. Damp's `Damp/Lang/Tokens.lean` and the algebra/CSE passes already share these;
`test/oracle/known-differences` records the token ones.

**B. `copy`.** compactc writes `copy %x` before using a function argument or cast result
(`copy output="%18" val="%1"` before `transient_hash [.., %18]` in the nonce-evolution of
`sendShielded`; before `constrain_bits 16` in `test01.set`). 58 in the suite, 25 of them copies of
constants (removed by `test/zkir-normalize.py`); a `copy` costs 0 rows alone (`bench/costs.py`) and
about one where its result is used (`sendShieldedToUserTest`: two copies, two rows). Damp never emits them.

**C. Constants.** compactc emits `x - 5` as `neg 0x05` then `add x %neg` (`pm_19287.test_recursive_style_processing`,
`transform_vector`: 3 `neg` and 3 `add` against Damp's 3 `add x 0xfcff...`), `(x + 42) + 256` as two
adds, and `(v + 1 - 1) * 2` as `add 1; neg 1; add; mul 2` (`test01.set`: Damp emits `mul 2 v`), and
`temp + 2 != 5` as `add; test_eq` (Damp: `test_eq temp 3`). Saves 1 to 3 instructions per occurrence,
1 row each.

**D. Field to Uint cast.** `disclose(x) as Uint<16>` costs compactc a `div_mod_power_of_two bits=16`
(144 rows), `test_eq hi 0`, a guarded `assert` and a `copy`; Damp checks the same fact with one
`constrain_bits 16` on `cond_select(guard, x, 0)` (2 rows). `myswitch` has two such casts: 414 rows
against 131. (Unlike A-C this is a different lowering, not a missed simplification; Damp's is
sound for the same reason: `x < 2^16` is exactly what the quotient being 0 says.)

**E. Repeated ledger reads.** `coracle.start` reads `state` three times and `pot` twice (Compact
reads the field at each mention), each read a `public_input` and a few `impact`s guarded by the
branch; Damp's default reuses an earlier read when no write intervenes: 30 `public_input`s against
compactc's 36.

**F. Boolean connectives.** compactc has 2 more `cond_select`s than Damp in `coracle.guess`, 4 in
`concede`, 4 in `withdraw` and about 7 in `start`, in the bodies guarded by `player_is_red`
(`cond_select a=% b=0x00 bit=%` and `a=0x00 b=% bit=%`: an `&&` of two booleans, one of them a
guard, that Damp has simplified), and writes guarded assertions as `cond_select a=1 b=c bit=g` where
Damp writes `a=c b=1` (same count, different circuit). I did not trace each extra select to its
source expression.

### Differences that are not size

Before short-circuit evaluation was added to the language, fifteen circuits were not compactc's
circuit even up to normalization and dropping `copy`s, and in several of them the reason was
**guards**: compactc executes `a && b`, `a || b` and `c ? x : y` lazily, so the ledger read or witness
call in `b`/`x` is guarded by `a`/`c`, while Damp's `&&.` and `select` took already-evaluated
operands, so a `(← w)` or `(← cell.read)` inside them was performed unconditionally:

```
tiny.get      compactc: public_input output=%2 guard=%1      Damp: public_input output=%2 guard=None
                        impact ... guard=%1 (x3)                    impact ... (x3, unguarded)
election_core.vote_commit
              compactc: private_input output=%3 guard=%2     Damp: private_input output=%2 guard=None
```

This was a behavioural difference, not only a ZKIR one: in `election_core.vote_commit` with the state
not `commit`, compactc's module never calls the witness `private_state`, Damp's executor called it
once (measured: 0 and 1 calls). Damp now evaluates the second operand of `&&.`/`||.`, the branches of
`select`/`if` expressions and the non-`do` branches of `if%` under their guard when they contain a
`(← …)` (docs/language.md, "Short-circuit evaluation"), and the ports were brought back to the
Compact text where they had hoisted the read out of the operand (`tiny.get`, `test01.get`:
`value` inside the conditional; `threading.fib`: `counter` inside the `&&`; `coracle.start`:
`kernel.self()` inside each branch, as Compact writes it, which costs Damp one coin-commitment hash
that sharing `self` had saved: 236 -> 253 instructions, 53 891 -> 59 565 rows, still below compactc's
267 / 59 578). Effect on the table: `tiny.get`, `test01.get` and `election_core.vote_commit` went from
`x` to `=`; `tiny.get` and `test01.get` left the list of circuits whose public transcript the
behavioural check allows to differ (`election_core` is not exercised: every call is refused).

Twelve circuits are still `x`. In every one of them the witness calls and ledger operations
(`private_input`, `public_input`, `impact`) are compactc's, in the same order and guarded or
unguarded alike (checked instruction by instruction at the default level; `assert_misc.myswitch`
also at `--no-opt`, where its extra asserts are D); they differ by C-F and by order:
`election_core.vote_reveal` computes the negated guard of its last `if%` where it is first used,
compactc right after the comparison; `assert_misc.ellen` reads both ledger values and then
compares, compactc interleaves; `threading.fib` and `test01.set` have C and write the guarded
`assert` of an `else` branch as `cond_select a=c b=1 bit=!g` where compactc writes `a=1 b=c bit=g`
(F); `coracle.*`, `pm_19287.*` and `myswitch` differ as described under A-F. These are the circuits
the behavioural check does not require to have compactc's proof data.

## What is left to remove

`bench/headroom.py` applies, to a circuit and one at a time, rewrites that a sound optimizer could make,
and measures the result with `mock-compile`. On compactc's circuits and on Damp's default ones:

| Rewrite | compactc: instr / rows | Damp default: instr / rows |
|---|---|---|
| `dead`: pure instructions nothing uses | 6 / 6 | 0 / 0 |
| `cse`: a pure instruction repeating an earlier one | 46 / 26 619 | 0 / 0 |
| `fold`: constant arithmetic, `x+0`, `x*1`, constant `cond_select`, `copy` | 92 / 33 | 0 / 0 |
| `bits`: a range check of a value already known to fit | 0 / 0 | 0 / 0 |
| `reads`: a ledger read repeating an earlier one, no write between | 20 / 51 | 20 / 51 |
| `hashes`: `persistent_hash`/`transient_hash`/`div_mod` of constants only | 34 / 34 354 | 30 / 30 312 |
| `merge`: adjacent `impact`s with one guard joined | 3347 / 0 | 3351 / 0 |
| all together | 3510 / 57 017 | 3400 / 30 365 |

(`bits` does not see a range check implied by a later hash; that is `hashRanges`, 5 056 rows at
`--O3`, see "Optimizer levels".)

What the rows are made of (`bench/costs.py`, 20 copies of an instruction in a small circuit):
`persistent_hash` of two `Bytes<32>` 3741, `div_mod_power_of_two` 144, `constrain_bits` 8 bits 2,
64 bits 16, 248 bits 62, `less_than` 64/128 bits 7/9, `transient_hash` 20, `test_eq` 2,
`add`/`mul`/`neg`/`cond_select`/`assert`/`public_input`/`private_input` 1, `copy` 0. Attributed in
the circuits themselves (`bench/costs.py --attribute`, "Where the rows are" above), the persistent
hashes are 93 % of the suite's rows at every level. So the rewrites that matter for proving cost are
those that remove a hash, or the checks around one; everything else is a few rows.

**Hashes of constants.** `adt_merkle.test` inserts the literals 7, 0, 1, 2, 3, 42 and 100 into a
`MerkleTree` (`insertIndex(7 as Field, 1)`, the unrolled `for (const i of 0..4) merkleTreeSmall.insert(i)`,
`insertIndexDefault`); the leaf of each is `persistent_hash` of constants, and compactc (and Damp)
emit it in the circuit:

```
persistent_hash inputs=["0x6d646e3a6c68","0x07"] alignment=[bytes6, field]    -> 2014 rows
bytes_into_natives ...
```

Seven of them in `test`, eight in `test_historic`. The values are known when the circuit is built;
folding them removes 30 instructions and 30 312 rows (6.0 % of the suite) from two circuits. **Done at `--O3`** (see "Optimizer levels"): the constant is computed with
`Damp/Crypto/Sha256.lean`, which `test/semantics.sh` checks against the real evaluator; the proof is
relative to that implementation. (Only literals trigger this: it is rare outside
tests, `insertIndexDefault` and constant `persistentHash` domain-separator-only inputs.)

**Dead hashes.** With the earlier ports of `election_core` and `zerocash_core` (a witness returning
the Merkle root instead of a `MerkleTreePath`), the commitment of `spend` and the public keys of the
two votes were computed only for a witness-call argument, which the circuit does not evaluate: 15 015
rows, removed at `--O2` by `forwardOpt`/`forwardAllOpt`. The restored ports compare them with
`path.leaf`, as the Compact originals do, so they are live and nothing dead is left.

## Prioritized optimizations

The order is by rows. What is left after these is the hashes the programs need (93 % of the rows),
`div_mod` of transient hashes (0.8 %) and range checks of values that go only to the ledger (0.2 %).

0. **Done (`--O3`, `hashRanges`): drop range checks a later persistent hash implies.** 158
   instructions, **5 056 rows** (1.07 %) in 28 circuits. Sound relative to `Crypto.prims` only (the
   hash must refuse inputs that do not fit). Next by size: share a hash between the arms of a
   conditional when both arms' inputs are ready before either is used (`coracle.start`, one hash,
   3 741 rows, 0.8 %; see "Ideas measured and not pursued").
1. **Done (`--O3`, `foldHashes`; `divmod` at every level, `foldDivmod`).** **Fold `persistent_hash`, `transient_hash` and `div_mod_power_of_two` whose inputs are all constants**
   (a `simplify` rule using the `Prims` of `Damp/Crypto`). 30 instructions and **30 312 rows** (6.0 % of
   the suite) in `adt_merkle.test` and `test_historic`; 2014 rows per constant leaf. Needs the hash
   function at compile time; the semantics already has it. The evidence is two test programs: the gain
   is large where a literal reaches a hash and nil elsewhere.
2. **Done at `--O2` (`forwardOpt`, `forwardAllOpt`).** **Drop circuit computations whose only consumers
   are witness-call arguments.** It removed 15 015 rows from the earlier, adapted ports of
   `election_core` and `zerocash_core`; the restored ports use those hashes (compared with the Merkle
   path's leaf), so it removes nothing in this suite now. Not at the default level, where it would
   change a circuit that is compactc's.
3. **Short-circuit lowering for `&&.`, `||.` and `?:`-style `select`**: done (a Lang change, not an
   optimization; see "Differences that are not size"). As expected it saved nothing in rows or
   instructions (`tiny.get`, `vote_commit` have equal counts either way); it removed the behavioural
   difference and made `tiny.get`, `test01.get` and `vote_commit` compactc's circuit.
4. **Done for `assert` (`--O2`, `assertEq`: 18 instructions, 36 rows).** **Fold `b == true` to `b` on `Boolean`** (O2). Measured by writing the same ports once without the
   `==. .true` (`require (← c.isEmpty)` for `assert(c.isEmpty() == true, ..)`): `adt_list_struct`
   424 -> 420 instructions (1329 -> 1321 rows), `adt_map_list` 92 -> 89 (250 -> 244), `adt_merkle`
   -2 instructions each. 1 instruction and 2 rows per occurrence. (`b == false` as `!b` is one
   instruction either way: nothing to gain.) compactc keeps them, so Damp's default and O2 currently
   match compactc here.
5. **Repeated ledger reads** (`headroom reads`): 24 instructions, 61 rows left in Damp's default
   circuits (`coracle.start` 8 / 20, `pm_20028.test_cast_comparison` 8 / 20, `adt_merkle.test` 8 / 21):
   `Cell.read` of the same cell twice with no write between. Cheap, small; `Damp/Optimize/Forward.lean`
   (in progress) is this.
6. **Done (`commuteOpt`, default and `--O2`: myswitch -2 instructions, -3 rows).** **Commutative duplicates** (`headroom cse` on the default output): `x != y` and `y != x` in the two arms of
   `myswitch` are two `test_eq`s: 2 instructions, 3 rows. Negligible.
7. **Merge adjacent `impact` instructions with one guard**: 3325 instructions (53 % of the suite's
   instructions) and **0 rows**. Only worth doing if ZKIR size matters; it does not move the proof.
8. Nothing for `bits` (0 redundant range checks in either compiler's output) and nothing from the
   `asserts` pass, which has no effect on these 90 circuits. A corpus with `assert(x < n)` followed by
   use of `x` as a narrower `Uint` would be needed to evaluate it.

Not worth chasing: `copy` (0 rows), C and A (Damp already does them). Where Damp is already ahead of
compactc: A (up to 5.6k rows per circuit), C, D (283 rows per two casts), E.

## Rejected programs

Programs from Compact's tree that I did not port, and the first thing Damp lacks.

| Program | Missing in Damp | Compact |
|---|---|---|
| examples/election.compact (ported as `election_core`) | `Opaque` types; `MerkleTreePath` and `merkleTreePathRoot` | `ledger topic: Maybe<Opaque<"string">>;` `witness context$eligible_voters$path_of(pk: Bytes<32>): Maybe<MerkleTreePath<10, Bytes<32>>>;` `eligible_voters.checkRoot(disclose(merkleTreePathRoot<10, Bytes<32>>(path.value)))` `pk == path.value.leaf` |
| examples/zerocash.compact (ported as `zerocash_core`) | `Opaque<"Uint8Array">`; `MerkleTreePath` | `struct public_key { zk: zk_public_key; encryption: Opaque<"Uint8Array">; }` `ledger ciphertexts: Opaque<"Uint8Array">;` `witness context$encrypt(pk: Opaque<"Uint8Array">, coin: coin_info): Opaque<"Uint8Array">;` |
| examples/proposal.compact | not Compact 0.36.1 syntax (compactc: `parse error: found "{" looking for a type` at `type Ledger = {`); old `ledger.field.write`, `check_root`, `merkle_path_root`, `find_element` | `type Ledger = { field1: Map<Field, Foo>; ... };` `ledger.field2.check_root(merkle_path_root(ledger.field2.find_element(...)))` |
| examples/std_lib/mint.compact | pre-0.10 syntax; compactc: `found "Integer" looking for ","` | `amount: Unsigned Integer[64]` `receive(coin)` `own_public_key()` |
| test-center/compact/test01.compact | `Bytes<n> as Field` (ported with `temp: Field`) | `if ((temp as Field) + 2 != 5) assert(false, 'oops 1');` |
| test-center/compact/schnorr.compact, ecdsa.compact; examples/ecdsa, examples/jubjubpoint, examples/external/examples.compact | the embedded curve: `JubjubPoint`, `JubjubScalar`, `JubjubSchnorrSignature`, `Secp256k1Point`, `Secp256k1EcdsaSignature`, `ecAdd`, `ecNeg`, `ecMul`, `ecMulGenerator`, `hashToCurve`, `jubjubSchnorrVerify`, `secp256k1EcdsaVerify`, `keccak256` | `result = disclose(jubjubSchnorrVerify<3>(msg, sig, pk));` `secp256k1EcdsaVerify(keccak256<Bytes<32>>(msg), sig, pk)` `const g: JubjubPoint = ecAdd(default<JubjubPoint>, default<JubjubPoint>);` |
| test-center/compact/test.compact | modules with generic parameters and prefixed imports; `contract C {}`/`contract implements`; `ledger kernel2: Kernel`; `sealed ledger`; `emit` (events); `include` | `module M<#a, b> { export struct pair { x: Field; y: Vector<a, b>; } }` `import M<5, Opaque<"sisters">> prefix M$;` `emit ( ShieldedSpend {authority} );` `contract implements CX;` |
| test-center/composable/Events/{Inner,Outer}.compact | events | `emit(ShieldedSpend { nullifier: disclose(n) });` |
| test-center/composable/Storage/Outer.compact | `MerkleTree<2, Inner>` of a contract type (`tree.insert(disclose(i))`); not tried: the rest of that file ports | `ledger tree: MerkleTree<2, Inner>;` |
| examples/casts/advanced_casts.compact, vector_to_bytes.compact, zkir_generation.compact, proof_data.compact | casts between `Bytes<n>`, `Vector<n, Uint<8>>`, `Uint<k>`, `Field`, and enums | `val1 = disclose(param1) as Bytes<10>;` (param1: `Vector<10, Uint<8>>`) `const bytes_from_uint8 = uint8_val as Bytes<4>;` `const uint_from_bytes0 = test_bytes0 as Uint<127>;` `const uint_a = Test4Enum.A as Uint<8>;` `const cast_0 = enum_0 as Test4Enum;` `test_bytes as Vector<4, Field>` |
| examples/bytes/test_basic_bytes.compact, test-contracts/primitives/bytes/* | `Bytes[..]` literals, spread and indexing of `Bytes`, `map`/`fold`/`slice` over `Bytes<n>` (as `Vector<n, Uint<8>>`) | `Bytes[0x00, 0xFF, 0b11111111, 0o377, 128]` `Bytes[...a, ...b]` `assert(test1_var[5] == 0 as Uint<8>, ..)` `map((x: Field) => Bytes[x as Uint<8>], fields)` `slice<1>(b, 4)` |
| examples/types/examples.compact (the circuits not ported) | `Bytes` casts, `slice`/spread of `Bytes`, `default<..>` of vectors of structs | `const a = slice<1>(default<t1_Bytes2>, 0);` `1 as t7_f as t7_u64 as t7_u4 as t7_u2 as t7_b2048` |
| examples/vectors/slice_part_one.compact | `Boolean as Uint<8>`, `Bytes as Vector`; `Vector<0xffff, Field>` | `const b = slice<2>(vector, a)` with `const a = true as Uint<8>;` `slice<1>(d as Vector<5, Uint<8>>, 1)` |
| examples/bugs/pm-20028 `test3`; examples/modules/*, wpp/* | modules containing ledger fields, with generic parameters and prefix imports | `module N<#n> { export ledger field: Field; export circuit test3a(): Uint<n> { .. } }` `import N<248> prefix m$;` |
| examples/adt/tests/list_opaque.compact; merkletree/historicmerkletree `path` | `Opaque<"string">` in a `List`; `MerkleTreePath` as a ledger field | `ledger c: List<Opaque<"string">>;` `ledger path: MerkleTreePath<4, Field>;` |
| examples/assert/example_one.compact (the rest) | `[]`-typed values used as values, immediately invoked lambdas, `Map<[], []>` | `assert(assert(true != false, "bob 3") != [], "bob 4");` `(() => assert( 1 > 2, ""))();` `export ledger maps2: Map<[], []>;` |
| examples/bugs/pm-15405.compact | does not compile with compactc 0.36.1 (`Map<Uint<8>>` with one parameter: mismatch between actual number 1 and declared number 2 of ADT parameters) | `map_uint_8 = default<Map<Uint<8>>>;` |

Programs that compile but have no circuit that touches the ledger (so no ZKIR to compare):
examples/camelCase/new/{standard,ledger}.compact, most of examples/types, test-center/composable/Witness.

## What went wrong in Damp while porting

Nothing failed to compile that looked like a miscompilation. These cost time or differ from Compact:

1. **`&&.`, `||.`, `select` and `if`-as-expression evaluated both sides** (fixed since): a witness
   call or ledger read inside the second operand ran even when the first decided the result (the
   measured difference above). Minimal reproduction:
   ```
   -- Compact: private_state() is called only if state == commit
   assert(state.read() == PublicState.commit && private$state() == PrivateState.initial, "x");
   -- Damp: (← private_state) was lifted out and ran first; it now runs under `state == commit`
   require ((← state.read) ==. PublicState.commit &&. (← private_state) ==. PrivateState.initial) "x"
   ```
   Each `do` statement is now rewritten before Lean lifts its `(← …)`s: a `(← …)` in the second
   operand of `&&.`/`||.`, in a branch of `select` or of an `if` expression, or in a non-`do` branch
   of `if%`, runs under the guard (docs/language.md, "Short-circuit evaluation"). The ports follow
   the Compact text again where they had hoisted the read: `tiny.get` and `test01.get` read `value`
   inside the conditional, `threading.fib` reads `counter` inside the `&&`.
2. `const (a, b, c, d) := e` was a parse error ("unexpected token '('; expected identifier"); `const`
   now takes tuples and `⟨…⟩` of names.
3. `if c then x else y` in a plain `def` returning a circuit value failed ("The argument `Bytes.pad 32 "yes"` has
   type `Bytes 32` but is expected to have type `CircuitM ?m`"); with `open Damp` it is now
   `select c x y` wherever its type is a value rather than `CircuitM _`.
4. `damp-bench` (like `damp-examples`) stops at the first contract whose build fails, so a failing
   port hides the rest; `lake build Bench` checks each port separately.

Compact source files from 0.33 needed these changes for 0.36.1 and are listed per program above:
the `disclose` requirements (coracle), `Field` vs `Uint` equality (test01), 0.10-era syntax (proposal,
mint).
