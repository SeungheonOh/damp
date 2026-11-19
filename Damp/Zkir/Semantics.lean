/-
What a ZKIR circuit means: Midnight's reference evaluator, in Lean.

This follows `IrSource::preprocess` in midnight-zkir 3.2.1 (`zkir/src/ir_vm.rs`)
and §6 of the ZKIR v3 specification, for the instructions Damp emits. It is the
function the proof server runs to decide whether a call satisfies a circuit and
to compute the public inputs; upstream proves it agrees with the constraint
system. Everything Damp claims about circuits is stated against this file.

It is partial exactly where the Rust is: an instruction whose premise fails
yields `none`, meaning "this preimage does not satisfy this circuit".

Not modelled: instructions Damp does not emit (they yield `none`), types other
than native field elements and byte strings, and the hashes themselves, which
are parameters.
-/
import Damp.Zkir.Basic

namespace Damp.Zkir

/-- Number of bits in a field element (`FR_BITS`). -/
def frBits : Nat := 255

/-- Runtime values (`IrValue`), restricted to the two kinds Damp's circuits use. -/
inductive Value where
  | native (x : Fr)
  /-- A byte string, first byte first. Only the persistent hash produces one. -/
  | bytes (bs : List Nat)
  deriving DecidableEq, Inhabited

/-- The cryptographic functions, taken as given. -/
structure Prims where
  /-- Poseidon over native field elements. -/
  transientHash : List Fr → Fr
  /-- SHA-256 of the binary form of field elements read under an alignment;
      `none` when the elements do not fit that alignment. 32 bytes. -/
  persistentHash : Alignment → List Fr → Option (List Nat)
  /-- `transient_commit(values, opening)`. -/
  transientCommit : List Fr → Fr → Fr

/-- One `impact` instruction's contribution to the public-input vector. -/
structure Group where
  /-- False when the guard did not hold; the values are then all zero. -/
  active : Bool
  vals : List Fr
  deriving DecidableEq, Inhabited

abbrev Memory := Ident → Option Value

def Memory.set (m : Memory) (id : Ident) (v : Value) : Memory :=
  fun j => if j = id then some v else m j

structure State where
  mem : Memory
  /-- Unread part of the private transcript. -/
  priv : List Fr
  /-- Unread part of the public transcript's outputs (values read from the ledger). -/
  pub : List Fr
  /-- Public inputs declared so far, oldest first. -/
  groups : List Group := []
  outputs : List Fr := []

/-! ## Reading operands -/

/-- `resolve`: a register's value, or an immediate as a native element. -/
def resolve (m : Memory) : Operand → Option Value
  | .var id => m id
  | .imm v => some (.native (Fr.ofInt v))

/-- An operand that must be a native field element. -/
def native (m : Memory) (o : Operand) : Option Fr :=
  match resolve m o with
  | some (.native x) => some x
  | _ => none

def natives (m : Memory) : List Operand → Option (List Fr)
  | [] => some []
  | o :: os => do
      let x ← native m o
      let xs ← natives m os
      pure (x :: xs)

/-- `bool`: 0 is false, 1 is true, anything else is a failure. -/
def bool (m : Memory) (o : Operand) : Option Bool :=
  match native m o with
  | some x => if x = 0 then some false else if x = 1 then some true else none
  | none => none

/-- A native value that fits in `n` bits, where `n` is a legal bound. -/
def fitsBits (x : Fr) (n : Nat) : Bool := n < frBits && x.val < 2 ^ n

/-- `eval-guard`: an absent guard holds. -/
def evalGuard (m : Memory) : Option Operand → Option Bool
  | none => some true
  | some g => bool m g

/-- Bytes packed into native elements, 31 bytes each, least significant first. -/
def bytesToNatives (bs : List Nat) : List Fr :=
  if h : bs.length ≤ 31 then
    [Fr.ofNat (bs.foldr (fun b acc => acc * 256 + b) 0)]
  else
    Fr.ofNat ((bs.take 31).foldr (fun b acc => acc * 256 + b) 0) :: bytesToNatives (bs.drop 31)
termination_by bs.length
decreasing_by simp only [List.length_drop]; omega

/-- Take `n` values from a transcript when the guard holds, or the default without reading. -/
def readOne (active : Bool) (stream : List Fr) : Option (Fr × List Fr) :=
  if active then
    match stream with
    | x :: rest => some (x, rest)
    | [] => none
  else some (0, stream)

/-! ## Instructions -/

/-- Run one instruction. `none` is failure. -/
def Instr.step (p : Prims) (s : State) : Instr → Option State
  | .assert cond => do
      let b ← bool s.mem cond
      if b then pure s else none
  | .condSelect out bit a b => do
      let c ← bool s.mem bit
      let x ← resolve s.mem a
      let y ← resolve s.mem b
      -- checked against the real evaluator: `select_offcircuit` takes any two values of one type, byte strings of one length included (was: native only).
      match x, y with
      | .native u, .native v => pure { s with mem := s.mem.set out (.native (if c then u else v)) }
      | .bytes us, .bytes vs =>
          if us.length = vs.length then pure { s with mem := s.mem.set out (.bytes (if c then us else vs)) } else none
      | _, _ => none
  | .constrainBits v n => do
      let x ← native s.mem v
      if fitsBits x n then pure s else none
  | .constrainEq a b => do
      let x ← resolve s.mem a
      let y ← resolve s.mem b
      if x = y then pure s else none
  | .constrainToBoolean v => do
      let _ ← bool s.mem v
      pure s
  | .copy out v => do
      let x ← resolve s.mem v
      pure { s with mem := s.mem.set out x }
  | .testEq out a b => do
      let x ← resolve s.mem a
      let y ← resolve s.mem b
      -- checked against the real evaluator: `test_eq_offcircuit` also compares two byte strings (was: native only).
      match x, y with
      | .native u, .native v => pure { s with mem := s.mem.set out (.native (Fr.ofBool (u = v))) }
      | .bytes us, .bytes vs => pure { s with mem := s.mem.set out (.native (Fr.ofBool (us = vs))) }
      | _, _ => none
  | .add out a b => do
      let x ← native s.mem a
      let y ← native s.mem b
      pure { s with mem := s.mem.set out (.native (x + y)) }
  | .mul out a b => do
      let x ← native s.mem a
      let y ← native s.mem b
      pure { s with mem := s.mem.set out (.native (x * y)) }
  | .neg out a => do
      let x ← native s.mem a
      pure { s with mem := s.mem.set out (.native (-x)) }
  | .not out a => do
      let b ← bool s.mem a
      pure { s with mem := s.mem.set out (.native (Fr.ofBool (!b))) }
  | .lessThan out a b bits => do
      let x ← native s.mem a
      let y ← native s.mem b
      if fitsBits x bits && fitsBits y bits then
        pure { s with mem := s.mem.set out (.native (Fr.ofBool (x.val < y.val))) }
      else none
  | .divModPowerOfTwo outs v bits => do
      -- `DivModPowerOfTwo` in ir_vm.rs: exactly two outputs, quotient then
      -- remainder; the width may not exceed 248 (`FR_BYTES_STORED * 8`).
      match outs with
      | [q, r] =>
          let x ← native s.mem v
          if bits ≤ 248 then
            pure { s with mem := (s.mem.set q (.native (Fr.ofNat (x.val / 2 ^ bits)))).set r
                                    (.native (Fr.ofNat (x.val % 2 ^ bits))) }
          else none
      | _ => none
  | .transientHash out inputs => do
      let xs ← natives s.mem inputs
      pure { s with mem := s.mem.set out (.native (p.transientHash xs)) }
  | .persistentHash out alignment inputs => do
      let xs ← natives s.mem inputs
      let digest ← p.persistentHash alignment xs
      pure { s with mem := s.mem.set out (.bytes digest) }
  | .bytesIntoNatives outs bytes => do
      match resolve s.mem bytes, outs with
      | some (.bytes bs), [lo, hi] =>
          match bytesToNatives bs with
          | [x, y] => pure { s with mem := (s.mem.set lo (.native x)).set hi (.native y) }
          | _ => none
      | _, _ => none
  | .privateInput ty out guard => do
      if ty != .native then none
      let active ← evalGuard s.mem guard
      let (x, rest) ← readOne active s.priv
      pure { s with mem := s.mem.set out (.native x), priv := rest }
  | .publicInput ty out guard => do
      if ty != .native then none
      let active ← evalGuard s.mem guard
      let (x, rest) ← readOne active s.pub
      pure { s with mem := s.mem.set out (.native x), pub := rest }
  | .impact guard inputs => do
      let active ← bool s.mem guard
      if active then
        let xs ← natives s.mem inputs
        pure { s with groups := s.groups ++ [{ active := true, vals := xs }] }
      else
        -- Skipped: zeros, however many inputs there are. The inputs are not read.
        pure { s with groups := s.groups ++ [{ active := false, vals := inputs.map fun _ => 0 }] }
  | .output vals => do
      let xs ← natives s.mem vals
      pure { s with outputs := s.outputs ++ xs }
  | _ => none

/-- Run instructions in order. -/
def exec (p : Prims) : List Instr → State → Option State
  | [], s => some s
  | i :: is, s => do
      let s' ← i.step p s
      exec p is s'

/-! ## Whole circuits -/

/-- What the prover supplies (`ProofPreimage`), minus the binding input, which
    the circuit never looks at. -/
structure Preimage where
  inputs : List Fr
  privateTranscript : List Fr
  /-- Values read from the ledger. -/
  publicTranscriptOutputs : List Fr
  /-- Field encoding of the on-chain instructions that ran. -/
  publicTranscriptInputs : List Fr
  /-- `(commitment, opening)`, when the circuit binds its inputs and outputs. -/
  commitment : Option (Fr × Fr) := none

structure Outcome where
  outputs : List Fr
  groups : List Group
  deriving DecidableEq

def bindInputs (m : Memory) : List (Ident × IrType) → List Fr → Option Memory
  | [], [] => some m
  | (id, .native) :: ins, x :: xs => bindInputs (m.set id (.native x)) ins xs
  | _, _ => none

/-- Every `output` lists exactly the declared outputs, which (as `output` only
    takes native values here) must all be native. The Rust checks this when it
    runs each `output`; as every instruction runs unless an earlier one fails,
    checking it up front accepts and rejects the same preimages. -/
def IrSource.outputsDeclared (src : IrSource) : Bool :=
  src.instructions.all fun
    | .output vals => vals.length == src.outputs.length && src.outputs.all (· == .native)
    | _ => true

/-- Run a circuit on inputs and the two transcripts it reads. Both must be
    consumed exactly (TC1, for the two transcripts read here). -/
def IrSource.run (p : Prims) (src : IrSource) (inputs priv pub : List Fr) : Option Outcome := do
  -- checked against the real evaluator: an `output` whose arity or types differ from the declared outputs is rejected (was: accepted).
  if !src.outputsDeclared then none
  let mem ← bindInputs (fun _ => none) src.inputs inputs
  let s ← exec p src.instructions.toList { mem, priv, pub }
  if s.priv.isEmpty && s.pub.isEmpty then pure { outputs := s.outputs, groups := s.groups }
  else none

/-- The public inputs of the instructions that ran, in order. -/
def Outcome.activeInputs (o : Outcome) : List Fr :=
  (o.groups.filter (·.active)).flatMap (·.vals)

/-- `preprocess`: the run must also reproduce the public transcript it claims
    (the active-`impact` check and the rest of TC1) and, when the circuit asks
    for it, open the communications commitment (TC2). -/
def IrSource.preprocess (p : Prims) (src : IrSource) (pre : Preimage) : Option Outcome := do
  let o ← src.run p pre.inputs pre.privateTranscript pre.publicTranscriptOutputs
  if o.activeInputs ≠ pre.publicTranscriptInputs then none
  if src.commCommitment then
    match pre.commitment with
    | some (c, r) => if c = p.transientCommit (pre.inputs ++ o.outputs) r then pure o else none
    | none => none
  else pure o

end Damp.Zkir
