/-
What the circuit IR means.

A run takes the circuit inputs and the two oracle streams of the Kachina model:
the private transcript (witness results) and the values read from the public
state. It yields the outputs and one group of public inputs per on-chain
instruction, or `none` when the inputs and transcripts do not satisfy the
circuit.

This is deliberately the same shape, the same result type and the same notion
of failure as the ZKIR evaluator in `Damp/Zkir/Semantics.lean`, which is a port
of Midnight's reference implementation. The definition here is the statement
of what the emitter must achieve: `Damp/Proofs/Emit.lean` proves that the
ZKIR emitted for a circuit evaluates to exactly what this file says.

Partiality follows ZKIR:

* a conditional on a value that is neither 0 nor 1 fails;
* a comparison fails unless both sides fit the stated width;
* `invalid` has no value;
* both branches of a conditional are evaluated, so a failure in either fails.
-/
import Damp.IR.Basic
import Damp.Zkir.Semantics

namespace Damp.IR
open Damp.Zkir (Prims Group Outcome fitsBits bytesToNatives)

abbrev Env := Var → Fr

def Env.set (env : Env) (v : Var) (x : Fr) : Env := fun w => if w = v then x else env w

/-- A field element as a condition: 0 is false, 1 is true, anything else fails. -/
def asBool (x : Fr) : Option Bool :=
  if x = 0 then some false else if x = 1 then some true else none

mutual
def Expr.eval (p : Prims) (env : Env) : Expr → Option Fr
  | .var v => some (env v)
  | .const c => some (Fr.ofInt c)
  | .invalid _ => none
  | .disclose e => e.eval p env
  | .add a b => do
      let x ← a.eval p env
      let y ← b.eval p env
      pure (x + y)
  | .mul a b => do
      let x ← a.eval p env
      let y ← b.eval p env
      pure (x * y)
  | .neg a => do
      let x ← a.eval p env
      pure (-x)
  | .lt bits a b => do
      let x ← a.eval p env
      let y ← b.eval p env
      if fitsBits x bits && fitsBits y bits then pure (Fr.ofBool (x.val < y.val)) else none
  | .eq a b => do
      let x ← a.eval p env
      let y ← b.eval p env
      pure (Fr.ofBool (x = y))
  | .select c a b => do
      let c ← c.eval p env
      let x ← a.eval p env
      let y ← b.eval p env
      let c ← asBool c
      pure (if c then x else y)
  | .divmod quot bits a => do
      let x ← a.eval p env
      if bits ≤ 248 then
        pure (Fr.ofNat (if quot then x.val / 2 ^ bits else x.val % 2 ^ bits))
      else none
  | .hash xs => do
      let xs ← Expr.evalList p env xs
      pure (p.transientHash xs)
  | .phash high align xs => do
      let xs ← Expr.evalList p env xs
      let digest ← p.persistentHash align xs
      match bytesToNatives digest with
      | [lo, hi] => pure (if high then hi else lo)
      | _ => none
def Expr.evalList (p : Prims) (env : Env) : List Expr → Option (List Fr)
  | [] => some []
  | x :: xs => do
      let y ← x.eval p env
      let ys ← Expr.evalList p env xs
      pure (y :: ys)
end

/-- Whether a value passes a range check, as the instructions emitted for the
    check decide it. -/
def Range.holds (x : Fr) : Range → Bool
  | .zero => x = 0
  | .bool => x = 0 || x = 1
  | .bits n => fitsBits x n
  | .below bound width =>
      fitsBits x width && fitsBits (Fr.ofInt bound) width && x.val < (Fr.ofInt (bound : Int)).val

structure RunState where
  env : Env
  priv : List Fr
  pub : List Fr
  groups : List Group := []

/-- Read one value per variable from a stream when active, zeros otherwise,
    checking each against its range as it arrives. -/
def readAll (active : Bool) (env : Env) :
    List (Var × Option Range) → List Fr → Option (Env × List Fr)
  | [], stream => some (env, stream)
  | (v, range) :: rest, stream => do
      let (x, stream) ← Zkir.readOne active stream
      match range with
      | some r => if r.holds x then pure () else none
      | none => pure ()
      readAll active (env.set v x) rest stream

/-- The public inputs one ledger statement declares: every operand is
    evaluated whether or not the guard holds; the values are zeroed if not. -/
def ledgerGroups (p : Prims) (env : Env) (active : Bool) :
    List (Impact.Op Expr) → Option (List Group)
  | [] => some []
  | op :: ops => do
      let vals ← Expr.evalList p env (op.encode Expr.const)
      let rest ← ledgerGroups p env active ops
      pure ({ active, vals := if active then vals else vals.map fun _ => 0 } :: rest)

def Stmt.exec (p : Prims) (s : RunState) : Stmt → Option RunState
  | .bind v _ e => do
      let x ← e.eval p s.env
      pure { s with env := s.env.set v x }
  | .assert cond _ => do
      let c ← cond.eval p s.env
      let c ← asBool c
      if c then pure s else none
  | .constrain e r => do
      let x ← e.eval p s.env
      if r.holds x then pure s else none
  | .witness guard _ _ outs _ => do
      let g ← guard.eval p s.env
      -- With nothing to read, no instruction looks at the guard.
      if outs.isEmpty then pure s
      else
        let active ← asBool g
        let (env, priv) ← readAll active s.env outs s.priv
        pure { s with env, priv }
  | .ledger guard reads ops => do
      let g ← guard.eval p s.env
      if reads.isEmpty && ops.isEmpty then pure s
      else
        let active ← asBool g
        let (env, pub) ← readAll active s.env (reads.map fun v => (v, none)) s.pub
        let groups ← ledgerGroups p env active ops
        pure { s with env, pub, groups := s.groups ++ groups }

def execAll (p : Prims) : List Stmt → RunState → Option RunState
  | [], s => some s
  | stmt :: rest, s => do
      let s' ← stmt.exec p s
      execAll p rest s'

def bindInputs (env : Env) : List Input → List Fr → Option Env
  | [], [] => some env
  | i :: ins, x :: xs => bindInputs (env.set i.var x) ins xs
  | _, _ => none

/-- Run a circuit. Both transcripts must be consumed exactly. -/
def Circuit.run (p : Prims) (c : Circuit) (inputs priv pub : List Fr) : Option Outcome := do
  let env ← bindInputs (fun _ => 0) c.inputs inputs
  let s ← execAll p c.body.toList { env, priv, pub }
  let outputs ← Expr.evalList p s.env c.outputs
  if s.priv.isEmpty && s.pub.isEmpty then pure { outputs, groups := s.groups } else none

end Damp.IR
