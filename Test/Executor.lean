/-
Conformance of the JavaScript executor (`executor/src/executor.mjs`) to its
definition, `Damp.Exec.run` (Damp/Executor.lean). See docs/executor.md and
test/executor.sh, which runs the three steps:

  lake exe damp-executor-test export <dir>
      writes <dir>/contracts/<name>/contract.json for every example contract
      (optimized, exactly as `Contract.build` writes it) and for the
      synthetic contract below (as written), and <dir>/synthetic.json, the
      synthetic calls with their arguments and witness answers.
  node executor/test/conformance.mjs <dir>
      runs every call through the JS executor with its trace hook on and
      writes <dir>/traces.json: per call, the trace and, for a call that
      completed, the field elements of its proof preimage as the runtime
      serializes it.
  lake exe damp-executor-test check <dir>
      replays every call through `Damp.Exec` with the real hashes and with
      scripted oracles that give back, in order, the witness and ledger
      answers the JS run recorded, and compares.

For each call: the same success or failure, at the same place (statement
index, inputs or outputs); at every statement, the definition asks an oracle
exactly when the JS did, with the same witness name and arguments or the same
ledger instructions; on success, the same outputs (as JS computed them and as
the runtime encodes the result), the private transcript and ledger reads equal
to the preimage's, the active public inputs equal to the preimage's public
transcript inputs, the same groups as JS computed, and every scripted answer
used. `Exec.run` itself is also run on the same scripts and must agree with the
statement-by-statement replay. For the synthetic calls, the definition's
outcome must also be the one the case was written to exercise.
-/
import Damp.Executor
import Damp.Build
import Damp.Crypto.Prims
import Examples.Step
import Examples.Counter
import Examples.Shapes
import Examples.Loops
import Examples.Bytes
import Examples.Extras
import Examples.Vault
import Examples.Notes
import Examples.Structures
import Examples.StructuresNested
import Examples.Tokens
import Examples.Tuned
import Examples.Calls

open Lean (Json)
open Damp Damp.IR
open Damp.Zkir (Group)

namespace Damp.ExecutorTest

/-! ## The contracts -/

def examples : List Contract :=
  [Examples.Step.contract, Examples.Counter.contract, Examples.Shapes.contract,
   Examples.Loops.contract, Examples.Bytes.contract, Examples.Extras.contract, Examples.Vault.contract, Examples.Notes.contract,
   Examples.Structures.contract, Examples.StructuresNested.contract, Examples.Tuned.contract,
   Examples.Tokens.contract,
   -- cross-contract calls (docs/calls.md); a callee's runs are traced and replayed as its own calls
   Examples.Adder.contract, Examples.Rich.contract, Examples.Caller.contract, Examples.Relay.contract,
   Examples.Top.contract, Examples.Picker.contract]

/-! ## Synthetic circuits

Raw IR, written to exercise every clause of `Exec.step` and `Expr.eval` in its
succeeding and failing form, the boundary values of every `Range`, and each
place where the JS executor used to depart from the definition. Inputs are
Field arguments bound to variables `0, 1, ...`; locals start at 10. -/

def fld : Shape := .prim .field
def V (n : Nat) : Expr := .var n
def K (i : Int) : Expr := .const i
def bad : Expr := .invalid "synthetic"
def P : Nat := Fr.modulus

def circ (name : String) (n : Nat) (body : List Stmt) (outputs : List Expr)
    (inputs : List Nat := List.range n) : Circuit :=
  { name, args := (List.range n).map fun i => (s!"a{i}", fld),
    inputs := inputs.map fun i => { name := s!"a{i}", var := i, range := none },
    body := body.toArray, result := .vector outputs.length fld, outputs }

/-- `bind 10 e`, returning variable 10. -/
def ex (name : String) (n : Nat) (e : Expr) : Circuit := circ name n [.bind 10 "x" e] [V 10]

/-- What the definition is expected to do with a synthetic call. -/
inductive Expect where
  | ok
  | failAt (i : Nat)
  | failInputs
  | failOutputs
  deriving BEq, Repr

structure Case where
  what : String
  fn : Circuit
  args : List Nat := []
  /-- What the JS witness answers, call by call: field elements of a vector of
      Fields, or `none` to throw. -/
  answers : List (Option (List Nat)) := []
  expect : Expect

/-- A witness statement whose shape is a vector of `k` Fields. -/
def wit (guard : Expr) (outs : List (Var × Option Range)) (k : Nat) (args : List Expr := []) : Stmt :=
  .witness guard "w" args outs (.vector k fld)

def readOps (field : Nat) (r : Expr) : List (Impact.Op Expr) :=
  [.dup 0, .idx false false [fieldKey field], .popeq false [.field] [r]]
def writeOps (field : Nat) (e : Expr) : List (Impact.Op Expr) :=
  [.push false (fieldKey field), .push true { align := [.field], vals := [e] }, .ins false 1]
def incrOps (field : Nat) (e : Expr) : List (Impact.Op Expr) :=
  [.idx false true [fieldKey field], .addi e, .ins true 1]
def readCounterOps (field : Nat) (r : Expr) : List (Impact.Op Expr) :=
  [.dup 0, .idx false false [fieldKey field], .popeq true [.bytes 8] [r]]

def constrainCirc (name : String) (r : Range) : Circuit := circ name 1 [.constrain (V 0) r] []

def phashCirc (name : String) (n : Nat) (high : Bool) (align : List Zkir.AlignAtom) (xs : List Expr) : Circuit :=
  ex name n (.phash high align xs)

def cases : List Case :=
  let lt8 := ex "lt8" 2 (.lt 8 (V 0) (V 1))
  let sel := ex "select" 3 (.select (V 0) (V 1) (V 2))
  let assertC := circ "assert" 1 [.assert (V 0) "synthetic"] []
  let ledgerC := circ "ledger_guarded" 2
    [.ledger (V 0) [10] (readOps 0 (V 10)), .ledger (V 0) [] (writeOps 1 (V 1))] [V 10]
  [ -- Expr.eval
    { what := "var bound", fn := ex "var" 1 (V 0), args := [7], expect := .ok },
    { what := "var never bound reads 0", fn := ex "var_unbound" 0 (V 99), expect := .ok },
    { what := "const, negative", fn := ex "const_neg" 0 (K (-5)), expect := .ok },
    { what := "const above the modulus", fn := ex "const_big" 0 (K (P + 3)), expect := .ok },
    { what := "invalid", fn := ex "invalid" 0 bad, expect := .failAt 0 },
    { what := "disclose", fn := ex "disclose" 1 (.disclose (V 0)), args := [8], expect := .ok },
    { what := "add wraps", fn := ex "add" 2 (.add (V 0) (V 1)), args := [P - 1, 2], expect := .ok },
    { what := "add, right operand fails", fn := ex "add_fail" 1 (.add (V 0) bad), args := [1], expect := .failAt 0 },
    { what := "mul", fn := ex "mul" 2 (.mul (V 0) (V 1)), args := [P - 1, P - 1], expect := .ok },
    { what := "mul, left operand fails", fn := ex "mul_fail" 1 (.mul bad (V 0)), args := [1], expect := .failAt 0 },
    { what := "neg", fn := ex "neg" 1 (.neg (V 0)), args := [5], expect := .ok },
    { what := "neg 0", fn := ex "neg" 1 (.neg (V 0)), args := [0], expect := .ok },
    { what := "neg, operand fails", fn := ex "neg_fail" 0 (.neg bad), expect := .failAt 0 },
    { what := "lt 8: 3 < 5", fn := lt8, args := [3, 5], expect := .ok },
    { what := "lt 8: 255 < 255", fn := lt8, args := [255, 255], expect := .ok },
    { what := "lt 8: left 256 does not fit", fn := lt8, args := [256, 0], expect := .failAt 0 },
    { what := "lt 8: right 256 does not fit", fn := lt8, args := [0, 256], expect := .failAt 0 },
    { what := "lt 8: p-1 does not fit", fn := lt8, args := [P - 1, 3], expect := .failAt 0 },
    { what := "lt 0: 0 < 0", fn := ex "lt0" 2 (.lt 0 (V 0) (V 1)), args := [0, 0], expect := .ok },
    { what := "lt 254 at its largest value", fn := ex "lt254" 2 (.lt 254 (V 0) (V 1)), args := [2 ^ 254 - 1, 0], expect := .ok },
    { what := "lt 254: 2^254 does not fit", fn := ex "lt254" 2 (.lt 254 (V 0) (V 1)), args := [2 ^ 254, 0], expect := .failAt 0 },
    { what := "lt 255: width not below 255", fn := ex "lt255" 2 (.lt 255 (V 0) (V 1)), args := [0, 1], expect := .failAt 0 },
    { what := "lt, operand fails", fn := ex "lt_fail" 1 (.lt 8 bad (V 0)), args := [1], expect := .failAt 0 },
    { what := "eq, equal", fn := ex "eq" 2 (.eq (V 0) (V 1)), args := [5, 5], expect := .ok },
    { what := "eq, different", fn := ex "eq" 2 (.eq (V 0) (V 1)), args := [5, 6], expect := .ok },
    { what := "eq, operand fails", fn := ex "eq_fail" 1 (.eq (V 0) bad), args := [1], expect := .failAt 0 },
    { what := "select on 1", fn := sel, args := [1, 10, 20], expect := .ok },
    { what := "select on 0", fn := sel, args := [0, 10, 20], expect := .ok },
    { what := "select on 2", fn := sel, args := [2, 10, 20], expect := .failAt 0 },
    { what := "select on p-1", fn := sel, args := [P - 1, 10, 20], expect := .failAt 0 },
    { what := "select on 1, unchosen branch invalid",
      fn := ex "select_bad_else" 2 (.select (V 0) (V 1) bad), args := [1, 10], expect := .failAt 0 },
    { what := "select on 0, unchosen branch an out-of-width lt",
      fn := ex "select_bad_then" 2 (.select (V 0) (.lt 8 (V 1) (K 0)) (V 1)), args := [0, 300], expect := .failAt 0 },
    { what := "select, condition fails", fn := ex "select_bad_cond" 1 (.select bad (V 0) (V 0)), args := [1], expect := .failAt 0 },
    { what := "hash of two", fn := ex "hash" 2 (.hash [V 0, V 1]), args := [1, 2], expect := .ok },
    { what := "hash of none", fn := ex "hash0" 0 (.hash []), expect := .ok },
    { what := "hash, element fails", fn := ex "hash_fail" 1 (.hash [V 0, bad]), args := [1], expect := .failAt 0 },
    { what := "phash field, low", fn := phashCirc "phash_f_lo" 1 false [.field] [V 0], args := [12345], expect := .ok },
    { what := "phash field, high", fn := phashCirc "phash_f_hi" 1 true [.field] [V 0], args := [P - 1], expect := .ok },
    { what := "phash bytes 32", fn := phashCirc "phash_b32" 2 false [.bytes 32] [V 0, V 1],
      args := [255, 2 ^ 248 - 1], expect := .ok },
    { what := "phash bytes 32, high limb 256 does not fit", fn := phashCirc "phash_b32" 2 false [.bytes 32] [V 0, V 1],
      args := [256, 0], expect := .failAt 0 },
    { what := "phash bytes 32, low limb 2^248 does not fit", fn := phashCirc "phash_b32" 2 false [.bytes 32] [V 0, V 1],
      args := [0, 2 ^ 248], expect := .failAt 0 },
    { what := "phash bytes 1: 255", fn := phashCirc "phash_b1" 1 true [.bytes 1] [V 0], args := [255], expect := .ok },
    { what := "phash bytes 1: 256 does not fit", fn := phashCirc "phash_b1" 1 true [.bytes 1] [V 0], args := [256], expect := .failAt 0 },
    { what := "phash bytes 33: stray limb 2^16 does not fit", fn := phashCirc "phash_b33" 2 false [.bytes 33] [V 0, V 1],
      args := [2 ^ 16, 1], expect := .failAt 0 },
    { what := "phash bytes 33", fn := phashCirc "phash_b33" 2 false [.bytes 33] [V 0, V 1],
      args := [2 ^ 16 - 1, 1], expect := .ok },
    { what := "phash compress", fn := phashCirc "phash_c" 1 false [.compress] [V 0], args := [1], expect := .failAt 0 },
    { what := "phash, too few elements", fn := phashCirc "phash_short" 1 false [.bytes 32] [V 0], args := [1], expect := .failAt 0 },
    { what := "phash, surplus element ignored", fn := phashCirc "phash_surplus" 2 false [.field] [V 0, V 1],
      args := [12345, 99], expect := .ok },
    { what := "phash bytes 0 then field", fn := phashCirc "phash_b0" 1 false [.bytes 0, .field] [V 0],
      args := [12345], expect := .ok },
    { what := "phash, element fails", fn := phashCirc "phash_fail" 1 false [.field] [bad], args := [1], expect := .failAt 0 },
    -- assert
    { what := "assert 1", fn := assertC, args := [1], expect := .ok },
    { what := "assert 0", fn := assertC, args := [0], expect := .failAt 0 },
    { what := "assert 2", fn := assertC, args := [2], expect := .failAt 0 },
    { what := "assert, condition fails", fn := circ "assert_fail" 0 [.assert bad "synthetic"] [], expect := .failAt 0 },
    -- constrain, every Range form on its boundary values
    { what := "zero: 0", fn := constrainCirc "r_zero" .zero, args := [0], expect := .ok },
    { what := "zero: 1", fn := constrainCirc "r_zero" .zero, args := [1], expect := .failAt 0 },
    { what := "bool: 0", fn := constrainCirc "r_bool" .bool, args := [0], expect := .ok },
    { what := "bool: 1", fn := constrainCirc "r_bool" .bool, args := [1], expect := .ok },
    { what := "bool: 2", fn := constrainCirc "r_bool" .bool, args := [2], expect := .failAt 0 },
    { what := "bits 0: 0", fn := constrainCirc "r_bits0" (.bits 0), args := [0], expect := .ok },
    { what := "bits 0: 1", fn := constrainCirc "r_bits0" (.bits 0), args := [1], expect := .failAt 0 },
    { what := "bits 8: 255", fn := constrainCirc "r_bits8" (.bits 8), args := [255], expect := .ok },
    { what := "bits 8: 256", fn := constrainCirc "r_bits8" (.bits 8), args := [256], expect := .failAt 0 },
    { what := "bits 254: 2^254-1", fn := constrainCirc "r_bits254" (.bits 254), args := [2 ^ 254 - 1], expect := .ok },
    { what := "bits 254: 2^254", fn := constrainCirc "r_bits254" (.bits 254), args := [2 ^ 254], expect := .failAt 0 },
    { what := "bits 255: 0 (width not below 255)", fn := constrainCirc "r_bits255" (.bits 255), args := [0], expect := .failAt 0 },
    { what := "below 10 at 4 bits: 9", fn := constrainCirc "r_below10_4" (.below 10 4), args := [9], expect := .ok },
    { what := "below 10 at 4 bits: 0", fn := constrainCirc "r_below10_4" (.below 10 4), args := [0], expect := .ok },
    { what := "below 10 at 4 bits: 10", fn := constrainCirc "r_below10_4" (.below 10 4), args := [10], expect := .failAt 0 },
    { what := "below 10 at 4 bits: p-1", fn := constrainCirc "r_below10_4" (.below 10 4), args := [P - 1], expect := .failAt 0 },
    { what := "below 16 at 4 bits: 15 (bound does not fit the width)", fn := constrainCirc "r_below16_4" (.below 16 4),
      args := [15], expect := .failAt 0 },
    { what := "below 10 at 3 bits: 5 (bound does not fit the width)", fn := constrainCirc "r_below10_3" (.below 10 3),
      args := [5], expect := .failAt 0 },
    { what := "below 10 at 255 bits: 5 (width not below 255)", fn := constrainCirc "r_below10_255" (.below 10 255),
      args := [5], expect := .failAt 0 },
    { what := "below 2^254-1 at 254 bits: 2^254-2", fn := constrainCirc "r_below_big" (.below (2 ^ 254 - 1) 254),
      args := [2 ^ 254 - 2], expect := .ok },
    { what := "below 0 at 8 bits: 0", fn := constrainCirc "r_below0" (.below 0 8), args := [0], expect := .failAt 0 },
    { what := "constrain, value fails", fn := circ "r_fail" 0 [.constrain bad .bool] [], expect := .failAt 0 },
    -- witness
    { what := "witness asked, answer in range",
      fn := circ "w_ok" 1 [wit (V 0) [(10, some (.bits 8))] 1] [V 10], args := [1], answers := [some [200]], expect := .ok },
    { what := "witness asked, answer out of range",
      fn := circ "w_ok" 1 [wit (V 0) [(10, some (.bits 8))] 1] [V 10], args := [1], answers := [some [256]], expect := .failAt 0 },
    { what := "witness asked, no range, answer p-1",
      fn := circ "w_norange" 0 [wit (K 1) [(10, none)] 1] [V 10], answers := [some [P - 1]], expect := .ok },
    { what := "witness: 2 results for 3 variables",
      fn := circ "w_short" 0 [wit (K 1) [(10, none), (11, none), (12, none)] 2] [V 10], answers := [some [1, 2]],
      expect := .failAt 0 },
    { what := "witness: 3 results for 2 variables",
      fn := circ "w_long" 0 [wit (K 1) [(10, none), (11, none)] 3] [V 10], answers := [some [1, 2, 3]],
      expect := .failAt 0 },
    { what := "witness not asked (guard 0): zeros",
      fn := circ "w_ok" 1 [wit (V 0) [(10, some (.bits 8))] 1] [V 10], args := [0], expect := .ok },
    { what := "witness not asked (guard 0), zero fails its range",
      fn := circ "w_skip_range" 1 [wit (V 0) [(10, some (.below 0 8))] 1] [V 10], args := [0], expect := .failAt 0 },
    { what := "witness, guard 2", fn := circ "w_ok" 1 [wit (V 0) [(10, some (.bits 8))] 1] [V 10], args := [2],
      expect := .failAt 0 },
    { what := "witness with nothing to read, guard 2",
      fn := circ "w_none" 1 [wit (V 0) [] 0] [], args := [2], expect := .ok },
    { what := "witness with nothing to read, guard 1: asked, for its effect on the private state",
      fn := circ "w_none" 1 [wit (V 0) [] 0] [], args := [1], answers := [some []], expect := .ok },
    { what := "witness with nothing to read, guard fails",
      fn := circ "w_none_bad" 0 [wit bad [] 0] [], expect := .failAt 0 },
    { what := "witness, guard fails", fn := circ "w_bad_guard" 0 [wit bad [(10, none)] 1] [V 10], expect := .failAt 0 },
    { what := "witness not asked, its argument fails",
      fn := circ "w_bad_arg" 1 [wit (V 0) [(10, none)] 1 [bad]] [V 10], args := [0], expect := .ok },
    { what := "witness asked, its argument fails",
      fn := circ "w_bad_arg" 1 [wit (V 0) [(10, none)] 1 [bad]] [V 10], args := [1], answers := [some [5]], expect := .failAt 0 },
    { what := "witness refuses (throws)",
      fn := circ "w_norange" 0 [wit (K 1) [(10, none)] 1] [V 10], answers := [none], expect := .failAt 0 },
    { what := "witness answers a value not of its shape",
      fn := circ "w_short" 0 [wit (K 1) [(10, none), (11, none), (12, none)] 2] [V 10], answers := [some [1]],
      expect := .failAt 0 },
    { what := "witness arguments, then a second witness under a computed guard",
      fn := circ "w_two" 2
        [wit (K 1) [(10, some (.bits 16)), (11, none)] 2 [.add (V 0) (K 1), V 1],
         .bind 12 "g" (.eq (V 10) (V 0)),
         wit (V 12) [(13, some .bool)] 1 [V 11]] [V 10, V 11, V 13],
      args := [41, 7], answers := [some [42, 9], some [1]], expect := .ok },
    { what := "second witness skipped by a computed guard",
      fn := circ "w_two" 2
        [wit (K 1) [(10, some (.bits 16)), (11, none)] 2 [.add (V 0) (K 1), V 1],
         .bind 12 "g" (.eq (V 10) (V 0)),
         wit (V 12) [(13, some .bool)] 1 [V 11]] [V 10, V 11, V 13],
      args := [40, 7], answers := [some [42, 9]], expect := .ok },
    -- ledger (field 0: a Field cell, field 1: a Field cell, field 2: a counter)
    { what := "ledger write", fn := circ "l_write" 1 [.ledger (K 1) [] (writeOps 0 (V 0))] [], args := [42], expect := .ok },
    { what := "ledger read", fn := circ "l_read" 0 [.ledger (K 1) [10] (readOps 0 (V 10))] [V 10], expect := .ok },
    { what := "ledger read and write, guard 1", fn := ledgerC, args := [1, 5], expect := .ok },
    { what := "ledger read and write, guard 0: zeros, inactive groups", fn := ledgerC, args := [0, 6], expect := .ok },
    { what := "ledger, guard 2", fn := ledgerC, args := [2, 6], expect := .failAt 0 },
    { what := "ledger with nothing to run, guard 2", fn := circ "l_empty" 1 [.ledger (V 0) [] []] [], args := [2], expect := .ok },
    { what := "ledger with nothing to run, guard fails", fn := circ "l_empty_bad" 0 [.ledger bad [] []] [], expect := .failAt 0 },
    { what := "ledger, guard fails", fn := circ "l_bad_guard" 0 [.ledger bad [] (writeOps 0 (K 1))] [], expect := .failAt 0 },
    { what := "ledger skipped (guard 0), an operand is invalid",
      fn := circ "l_skip_bad" 1 [.ledger (V 0) [] (writeOps 0 bad)] [], args := [0], expect := .failAt 0 },
    { what := "ledger skipped (guard 0), an operand is an out-of-width lt",
      fn := circ "l_skip_lt" 2 [.ledger (V 0) [] (writeOps 0 (.lt 8 (V 1) (K 0)))] [], args := [0, 300], expect := .failAt 0 },
    { what := "ledger run (guard 1), an operand of the last instruction fails: nothing runs",
      fn := circ "l_run_bad" 0 [.ledger (K 1) [] (writeOps 1 (K 3) ++ [.addi bad])] [], expect := .failAt 0 },
    { what := "ledger run, a popeq result fails as the request is formed",
      fn := circ "l_popeq_bad" 0 [.ledger (K 1) [10] [.dup 0, .idx false false [fieldKey 0], .popeq false [.field] [bad]]] [],
      expect := .failAt 0 },
    { what := "ledger write 300", fn := circ "l_write" 1 [.ledger (K 1) [] (writeOps 0 (V 0))] [], args := [300], expect := .ok },
    { what := "ledger run, a popeq result fails only once the read is bound (in its public inputs)",
      fn := circ "l_popeq_late" 0 [.ledger (K 1) [10] [.dup 0, .idx false false [fieldKey 0], .popeq false [.field] [.lt 8 (V 10) (K 0)]]] [],
      expect := .failAt 0 },
    { what := "ledger: two reads for one value read",
      fn := circ "l_count" 0 [.ledger (K 1) [10, 11] (readOps 0 (V 10))] [V 10], expect := .failAt 0 },
    { what := "ledger refuses (no field 9)",
      fn := circ "l_refuse" 0 [.ledger (K 1) [10] (readOps 9 (V 10))] [V 10], expect := .failAt 0 },
    { what := "counter increment by an input, then read, guard from a read",
      fn := circ "l_counter" 1
        [.ledger (K 1) [] (incrOps 2 (V 0)),
         .ledger (K 1) [10] (readCounterOps 2 (V 10)),
         .bind 11 "g" (.eq (V 10) (V 0)),
         .ledger (V 11) [12] (readOps 0 (V 12))] [V 10, V 12],
      args := [3], expect := .ok },
    { what := "counter increment, read, guard from a read is 0",
      fn := circ "l_counter" 1
        [.ledger (K 1) [] (incrOps 2 (V 0)),
         .ledger (K 1) [10] (readCounterOps 2 (V 10)),
         .bind 11 "g" (.eq (V 10) (V 0)),
         .ledger (V 11) [12] (readOps 0 (V 12))] [V 10, V 12],
      args := [3], expect := .ok },
    -- inputs and outputs
    { what := "one argument for two input variables",
      fn := circ "inputs_mismatch" 1 [] [] (inputs := [0, 1]), args := [1], expect := .failInputs },
    { what := "an output fails", fn := circ "outputs_fail" 1 [] [bad], args := [1], expect := .failOutputs },
    { what := "an output reads an unbound variable", fn := circ "outputs_unbound" 0 [] [V 50], expect := .ok } ]

/-- Circuits of `cases`, each name once. -/
def synCircuits : List Circuit :=
  cases.foldl (fun acc c => if acc.any (·.name == c.fn.name) then acc else acc ++ [c.fn]) []

def synthetic : Contract :=
  { name := "synthetic",
    «ledger» := [{ name := "c0", index := 0, kind := .cell fld }, { name := "c1", index := 1, kind := .cell fld },
               { name := "n", index := 2, kind := .counter }],
    circuits := synCircuits }

/-- What the JS executor is given: the optimized examples, and the synthetic contract as written. -/
def contracts : List Contract := examples.map Contract.optimize ++ [synthetic]

def caseLabel (i : Nat) (c : Case) : String := s!"synthetic {i}: {c.fn.name}: {c.what}"

/-! ## Export -/

def exportAll (dir : System.FilePath) : IO Unit := do
  -- Two synthetic circuits of one name must be the same circuit.
  for c in cases do
    let some d := synCircuits.find? (·.name == c.fn.name) | pure ()
    unless (Export.circuit d).compress == (Export.circuit c.fn).compress do
      throw (IO.userError s!"two different synthetic circuits named {c.fn.name}")
  for c in contracts do
    IO.ofExcept c.check
    IO.FS.createDirAll (dir / "contracts" / c.name)
    IO.FS.writeFile (dir / "contracts" / c.name / "contract.json") ((Export.contract c).pretty ++ "\n")
  let calls := cases.zipIdx.map fun (c, i) =>
    Json.mkObj [("label", caseLabel i c), ("contract", "synthetic"), ("circuit", c.fn.name),
      ("args", .arr (c.args.map fun a => Json.str (toString a)).toArray),
      ("witness", .arr (c.answers.map fun
        | some xs => .arr (xs.map fun a => Json.str (toString a)).toArray
        | none => .null).toArray)]
  IO.FS.writeFile (dir / "synthetic.json") ((Json.arr calls.toArray).pretty ++ "\n")
  IO.println s!"wrote {contracts.length} contracts and {cases.length} synthetic calls to {dir}"

/-! ## The scripted oracles -/

/-- One question put to an oracle: a witness (name, arguments) or the ledger
    (the request's public-input encoding). -/
structure Ask where
  isWitness : Bool
  name : String
  args : List Fr
  deriving BEq

def Ask.show (a : Ask) : String :=
  if a.isWitness then s!"witness {a.name}({a.args})" else s!"ledger {a.args}"

/-- Each run logs the questions its oracles were asked, so that a question asked
    by a step that then fails is seen too (the step's result is only `none`). -/
@[noinline] unsafe def logAskImpl (ref : IO.Ref (Array Ask)) (a : Ask) : Bool :=
  unsafeBaseIO do
    ref.modify (·.push a)
    return true

@[implemented_by logAskImpl] opaque logAsk (ref : IO.Ref (Array Ask)) (a : Ask) : Bool

/-- The answers recorded from the JS run, in order: `none` where its oracle refused. -/
abbrev Script := List (Option (List Fr))

def scripted (ref : IO.Ref (Array Ask)) : Exec.Oracles Script Script where
  «witness» name args ω :=
    if logAsk ref { isWitness := true, name, args } then
      match ω with
      | some vals :: rest => some (vals, rest)
      | _ => none
    else none
  «ledger» req σ :=
    if logAsk ref { isWitness := false, name := "", args := req.flatMap (Impact.Op.encode Fr.ofInt) } then
      match σ with
      | some vals :: rest => some (vals, rest)
      | _ => none
    else none

/-! ## Running the definition -/

inductive Loc where
  | inputs
  | stmt (i : Nat)
  | outputs
  | other (s : String)
  deriving BEq, Inhabited

def Loc.show : Loc → String
  | .inputs => "inputs"
  | .stmt i => s!"statement {i}"
  | .outputs => "outputs"
  | .other s => s

abbrev Result := Exec.Result Script Script

structure Run where
  failure : Option Loc := none
  result : Option Result := none
  /-- The questions asked by each statement that ran. -/
  asks : Array (List Ask) := #[]
  /-- A coverage tag per statement that ran. -/
  tags : Array String := #[]

def guardTag (env : Env) (g : Expr) : String :=
  match g.eval Crypto.prims env with
  | none => "guard fails"
  | some x => if x = 0 then "guard 0" else if x = 1 then "guard 1" else "guard not 0/1"

def exprTag : Expr → String
  | .var _ => "var" | .const _ => "const" | .invalid _ => "invalid" | .disclose _ => "disclose"
  | .add .. => "add" | .mul .. => "mul" | .neg _ => "neg" | .lt .. => "lt" | .eq .. => "eq"
  | .select .. => "select" | .hash _ => "hash" | .phash .. => "phash" | .divmod .. => "divmod"

/-- Coverage only: which clause a statement exercises. -/
def stmtTag (env : Env) : Stmt → String
  | .bind _ _ e => s!"bind ({exprTag e})"
  | .assert .. => "assert"
  | .constrain _ r => s!"constrain ({match r with | .zero => "zero" | .bool => "bool" | .bits _ => "bits" | .below .. => "below"})"
  | .witness g _ _ outs _ => s!"witness, {guardTag env g}{if outs.isEmpty then ", nothing to read" else ""}"
  | .ledger g reads ops => s!"ledger, {guardTag env g}{if reads.isEmpty && ops.isEmpty then ", nothing to run" else ""}"

/-- `Exec.run`, one `Exec.step` at a time, logging each statement's questions. -/
def stepwise (c : Circuit) (inputs : List Fr) (wit led : Script) : IO Run := do
  let ref ← IO.mkRef (#[] : Array Ask)
  let O := scripted ref
  let some env := bindInputs (fun _ => 0) c.inputs inputs | return { failure := some .inputs }
  let mut s : Exec.State Script Script := { env, private_ := wit, «ledger» := led }
  let mut asks : Array (List Ask) := #[]
  let mut tags : Array String := #[]
  let mut i := 0
  for stmt in c.body.toList do
    let n0 := (← ref.get).size
    let r ← IO.lazyPure fun _ => Exec.step Crypto.prims O s stmt
    let log ← ref.get
    asks := asks.push (log.toList.drop n0)
    match r with
    | none =>
        tags := tags.push (stmtTag s.env stmt ++ ": fails")
        return { failure := some (.stmt i), asks, tags }
    | some s' =>
        tags := tags.push (stmtTag s.env stmt ++ ": ok")
        s := s'
    i := i + 1
  match Expr.evalList Crypto.prims s.env c.outputs with
  | none => return { failure := some .outputs, asks, tags }
  | some outputs =>
      return { result := some { outputs, priv := s.priv, pub := s.pub, groups := s.groups,
                                private_ := s.private_, «ledger» := s.«ledger» }, asks, tags }

/-! ## Reading traces -/

def frOf (s : String) : Except String Fr :=
  match s.toNat? with
  | some n => if n < Fr.modulus then pure (Fr.ofNat n) else throw s!"{s} is not below the modulus"
  | none => throw s!"not a number: {s}"

def frsOf (j : Json) : Except String (List Fr) := do
  let xs ← j.getArr?
  xs.toList.mapM fun x => do frOf (← x.getStr?)

/-- The value at `k`, absent or null as `none`. -/
def opt (j : Json) (k : String) : Option Json :=
  match j.getObjVal? k with
  | .ok .null => none
  | .ok v => some v
  | .error _ => none

structure JsAsk where
  ask : Ask
  answer : Option (List Fr)

structure JsStep where
  index : Nat
  ask : Option JsAsk

structure JsRecord where
  /-- `none` if the arguments did not convert to field elements. -/
  inputs : Option (List Fr)
  steps : List JsStep
  groups : List Group
  outputs : Option (List Fr)
  failure : Option (Loc × String)

def parseAsk (isW : Bool) (j : Json) : Except String JsAsk := do
  let name := if isW then (j.getObjValAs? String "name").toOption.getD "" else ""
  let args ← frsOf (← j.getObjVal? (if isW then "args" else "request"))
  let answer ← match opt j "answer" with
    | some a => some <$> frsOf a
    | none => pure none
  pure { ask := { isWitness := isW, name, args }, answer }

def parseRecord (j : Json) : Except String JsRecord := do
  let inputs : Option (List Fr) ← match opt j "inputs" with
    | none => pure none
    | some xs => do
        let xs ← xs.getArr?
        if xs.any (· == .null) then pure none else some <$> frsOf (.arr xs)
  let steps ← (← j.getObjValAs? (Array Json) "steps").toList.mapM fun s => do
    let index ← s.getObjValAs? Nat "index"
    let ask ← match opt s "witness", opt s "ledger" with
      | some w, _ => some <$> parseAsk true w
      | none, some l => some <$> parseAsk false l
      | none, none => pure none
    pure { index, ask : JsStep }
  let groups ← (← j.getObjValAs? (Array Json) "groups").toList.mapM fun g => do
    pure { active := ← g.getObjValAs? Bool "active", vals := ← frsOf (← g.getObjVal? "vals") : Group }
  let outputs ← match opt j "outputs" with
    | some o => some <$> frsOf o
    | none => pure none
  let failure ← match opt j "failure" with
    | none => pure none
    | some f => do
        let reason := (f.getObjValAs? String "reason").toOption.getD ""
        let at_ ← f.getObjVal? "at"
        let loc : Loc := match at_.getNat?, at_.getStr? with
          | .ok n, _ => .stmt n
          | _, .ok "inputs" => .inputs
          | _, .ok "outputs" => .outputs
          | _, .ok s => .other s
          | _, _ => .other "?"
        pure (some (loc, reason))
  pure { inputs, steps, groups, outputs, failure }

/-- The field elements of the runtime's serialized preimage. -/
structure Preimage where
  inputs : List Fr
  priv : List Fr
  ptIn : List Fr
  ptOut : List Fr

def parsePreimage (j : Json) : Except String Preimage := do
  pure { inputs := ← frsOf (← j.getObjVal? "inputs"), priv := ← frsOf (← j.getObjVal? "privateTranscript"),
         ptIn := ← frsOf (← j.getObjVal? "publicTranscriptInputs"),
         ptOut := ← frsOf (← j.getObjVal? "publicTranscriptOutputs") }

/-! ## Comparing -/

def showFrs (xs : List Fr) : String := s!"[{", ".intercalate (xs.map toString)}]"

def activeInputs (gs : List Group) : List Fr := (gs.filter (·.active)).flatMap (·.vals)

def sameResult (a b : Option Result) : Bool :=
  match a, b with
  | none, none => true
  | some a, some b =>
      a.outputs == b.outputs && a.priv == b.priv && a.pub == b.pub && a.groups == b.groups &&
      a.private_ == b.private_ && a.«ledger» == b.«ledger»
  | _, _ => false

/-- Compare one call. `.ok note` or `.error why`. -/
def compare (c : Circuit) (rec : JsRecord) (pre : Option Preimage) (outFields : Option (List Fr))
    (expect : Option Expect) : IO (Except String String × Array String) := do
  -- Arguments the boundary rejected: the definition never sees them. Where they
  -- have a field form, the circuit must reject it too, before asking anything.
  if let some (.other "arguments", reason) := rec.failure then
    match rec.inputs with
    | none => return (.ok s!"arguments not representable as field elements; outside the definition ({reason})", #[])
    | some inputs =>
        let run ← stepwise c inputs [] []
        if run.failure.isNone then
          return (.error s!"JS rejected the arguments ({reason}) but the definition accepts them", run.tags)
        if run.asks.any (!·.isEmpty) then
          return (.error s!"JS rejected the arguments ({reason}); the definition gets as far as asking an oracle", run.tags)
        return (.ok s!"arguments rejected at the boundary; the definition fails too, at {run.failure.get!.show}", run.tags)
  let some inputs := rec.inputs | return (.error "no inputs recorded", #[])
  let asksOf (w : Bool) : Script := rec.steps.filterMap fun s => s.ask.bind fun a =>
    if a.ask.isWitness == w then some a.answer else none
  let wit := asksOf true
  let led := asksOf false
  let run ← stepwise c inputs wit led
  let r := run.tags
  -- The definition in one piece must agree with the step-by-step replay.
  let whole := Exec.run Crypto.prims (scripted (← IO.mkRef #[])) c inputs wit led
  unless sameResult whole run.result do
    return (.error "Exec.run and the step-by-step replay disagree", r)
  -- Statement by statement: the same statements started, the same questions.
  if run.asks.size != rec.steps.length then
    return (.error s!"the definition ran {run.asks.size} statement(s), JS {rec.steps.length}", r)
  for (s, i) in rec.steps.zipIdx do
    if s.index != i then return (.error s!"JS statement record {i} has index {s.index}", r)
    let lean := run.asks[i]!
    let js := s.ask.toList.map (·.ask)
    unless lean == js do
      return (.error s!"statement {i}: the definition asks {lean.map Ask.show}, JS asked {js.map Ask.show}", r)
  -- The outcome.
  let verdict : Except String String ← match run.failure, run.result, rec.failure with
    | some l, _, some (l', reason) =>
        pure <| if l == l' then .ok s!"both fail at {l.show}: {reason}"
          else .error s!"the definition fails at {l.show}, JS at {l'.show} ({reason})"
    | some l, _, none => pure (.error s!"the definition fails at {l.show}; JS completes")
    | none, _, some (l', reason) => pure (.error s!"the definition completes; JS fails at {l'.show} ({reason})")
    | none, none, none => pure (.error "no result")
    | none, some res, none => do
        let some pre := pre | return (.error "JS completed but recorded no preimage", r)
        let check (ok : Bool) (what : String) : Except String Unit := if ok then pure () else throw what
        pure <| (do
          check (rec.outputs == some res.outputs) s!"outputs {showFrs res.outputs}, JS {rec.outputs.map showFrs}"
          check (outFields == some res.outputs) s!"outputs {showFrs res.outputs}, runtime's encoding of JS's result {outFields.map showFrs}"
          check (pre.inputs == inputs) s!"preimage inputs {showFrs pre.inputs}, JS inputs {showFrs inputs}"
          check (pre.priv == res.priv) s!"private transcript {showFrs res.priv}, preimage {showFrs pre.priv}"
          check (pre.ptOut == res.pub) s!"ledger reads {showFrs res.pub}, preimage {showFrs pre.ptOut}"
          check (pre.ptIn == activeInputs res.groups)
            s!"active public inputs {showFrs (activeInputs res.groups)}, preimage {showFrs pre.ptIn}"
          check (rec.groups == res.groups) "the groups JS computed differ"
          check (res.private_.isEmpty && res.«ledger».isEmpty)
            s!"unused scripted answers: {res.private_.length} witness, {res.«ledger».length} ledger"
          pure s!"both complete; {res.outputs.length} output(s), {res.priv.length} private, {res.pub.length} read, {res.groups.length} group(s)" : Except String String)
  -- A synthetic call must also do what it was written to exercise.
  let got : Expect := match run.failure with
    | none => .ok
    | some (.stmt i) => .failAt i
    | some .inputs => .failInputs
    | some .outputs => .failOutputs
    | some (.other _) => .ok
  if let some e := expect then
    unless e == got do
      return (.error s!"the definition does {repr got}, the case expects {repr e}", r)
  return (verdict, r)

/-! ## Main -/

def checkAll (dir : System.FilePath) : IO UInt32 := do
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile (dir / "traces.json")))
  let calls ← IO.ofExcept (j.getObjValAs? (Array Json) "calls")
  let expects : List (String × Expect) := cases.zipIdx.map fun (c, i) => (caseLabel i c, c.expect)
  let mut ok := 0
  let mut bad := 0
  let mut nSyn := 0
  let mut cov : Std.HashMap String Nat := {}
  for call in calls do
    let label := (call.getObjValAs? String "label").toOption.getD "?"
    let res ← (do
      if let .ok e := call.getObjValAs? String "driverError" then throw (IO.userError e)
      let cname ← IO.ofExcept (call.getObjValAs? String "contract")
      let cn ← IO.ofExcept (call.getObjValAs? String "circuit")
      let some con := contracts.find? (·.name == cname) | throw (IO.userError s!"no contract {cname}")
      let circ? := if cn == "constructor" then con.constructor else con.circuits.find? (·.name == cn)
      let some circ := circ? | throw (IO.userError s!"no circuit {cname}.{cn}")
      let rec_ ← IO.ofExcept (parseRecord (← IO.ofExcept (call.getObjVal? "record")))
      let pre ← match opt call "preimage" with
        | some p => some <$> IO.ofExcept (parsePreimage p)
        | none => pure none
      let outFields ← match opt call "outputFields" with
        | some o => some <$> IO.ofExcept (frsOf o)
        | none => pure none
      let expect := expects.lookup label
      if cname == "synthetic" && expect.isNone then throw (IO.userError "no such synthetic case")
      compare circ rec_ pre outFields expect : IO _).toBaseIO
    match res with
    | .ok (.ok note, tags) =>
        ok := ok + 1
        IO.println s!"ok    {label}  [{note}]"
        if label.startsWith "synthetic" then
          nSyn := nSyn + 1
          for t in tags do cov := cov.insert t (cov.getD t 0 + 1)
    | .ok (.error why, _) =>
        bad := bad + 1
        IO.println s!"FAIL  {label}  {why}"
    | .error e =>
        bad := bad + 1
        IO.println s!"FAIL  {label}  {e}"
  -- Every synthetic case must have been run.
  let labels := calls.toList.filterMap fun c => (c.getObjValAs? String "label").toOption
  for (l, _) in expects do
    unless labels.contains l do
      bad := bad + 1
      IO.println s!"FAIL  {l}  not run by the JS executor"
  IO.println "\nstatements the synthetic calls ran, by clause and outcome:"
  for (t, n) in cov.toList.toArray.qsort (fun a b => a.1 < b.1) do
    IO.println s!"  {t}: {n}"
  let nEx := labels.filter (!·.startsWith "synthetic") |>.length
  IO.println s!"\n{calls.size} calls ({nEx} on the example contracts, {calls.size - nEx} synthetic): {ok} agree, {bad} disagree"
  return if bad == 0 then 0 else 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["export", dir] => exportAll dir; return 0
  | ["check", dir] => checkAll dir
  | _ =>
      IO.eprintln "usage: damp-executor-test export <dir> | check <dir>"
      return 2

end Damp.ExecutorTest

def main (args : List String) : IO UInt32 := Damp.ExecutorTest.main args
