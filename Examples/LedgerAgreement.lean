import Damp
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
import Examples.Tuned

/-! `Circuit.checkLedger` (`Damp/LedgerAgreement.lean`) on every example
contract, and on statements made by hand to fail it. -/
namespace Examples.LedgerAgreement
open Damp IR Impact

/-- Every example contract, as `Main.lean` lists them. -/
def contracts : List Contract :=
  [Examples.Step.contract, Examples.Counter.contract, Examples.Shapes.contract,
   Examples.Loops.contract, Examples.Bytes.contract, Examples.Extras.contract,
   Examples.Vault.contract, Examples.Notes.contract, Examples.Structures.contract,
   Examples.StructuresNested.contract, Examples.Tuned.contract]

/-- A contract's circuits and its constructor. -/
def circuitsOf (k : Contract) : List Circuit := k.circuits ++ k.constructor.toList

/-- Whether a circuit passes `checkLedger`. -/
def passes (c : Circuit) : Bool :=
  match c.checkLedger with
  | .ok () => true
  | .error _ => false

/-- The ledger statements of a circuit that read something. -/
def readingStmts (c : Circuit) : Nat :=
  c.body.toList.countP fun | .ledger _ reads _ => !reads.isEmpty | _ => false

/-- The failures, if any, as messages. -/
def failures : List String :=
  contracts.flatMap fun k => (circuitsOf k).flatMap fun c =>
    [c, c.optimize].filterMap fun c =>
      match c.checkLedger with
      | .ok () => none
      | .error e => some s!"{k.name}: {e}"

-- Every circuit and constructor of every example passes, as written and optimized.
#guard contracts.all fun k => (circuitsOf k).all passes
#guard contracts.all fun k => (circuitsOf k).all fun c => passes c.optimize
#guard failures == []

-- Not vacuous: the examples read from the ledger, many times, before and after
-- optimization.
#guard (contracts.flatMap circuitsOf).foldl (· + readingStmts ·) 0 ≥ 10
#guard (contracts.flatMap circuitsOf).foldl (fun n c => n + readingStmts c.optimize) 0 ≥ 10

/-! ## Statements made by hand -/

private def mkCircuit (body : List Stmt) : Circuit :=
  { name := "bad", args := [], inputs := [], body := body.toArray, result := .tuple [],
    outputs := [] }

/-- `Cell.read` of the field at `key` into `r`. -/
private def cellRead (key : Expr) (r : Var) : List (Op Expr) :=
  [.dup 0, .idx false false [{ align := [.bytes 1], vals := [key] }], .popeq false [.field] [.var r]]

private def errorOf (c : Circuit) : String :=
  match c.checkLedger with
  | .ok () => ""
  | .error e => e

-- A good read passes.
#guard passes (mkCircuit [.ledger (.const 1) [5] (cellRead (.const 0) 5)])

-- An operand mentions the statement's own read variable.
#guard !passes (mkCircuit [.ledger (.const 1) [5] (cellRead (.var 5) 5)])
#guard errorOf (mkCircuit [.bind 0 "x" (.const 3), .ledger (.const 1) [5] (cellRead (.var 5) 5)]) ==
  "circuit bad: ledger statement 1: an operand other than a popeq result mentions variable 5, \
   which the statement reads"

-- A later instruction of the same statement mentions a read variable.
#guard !passes (mkCircuit [.ledger (.const 1) [5] (cellRead (.const 0) 5 ++ [.addi (.var 5)])])

-- The results out of order, in one `popeq`.
#guard !passes (mkCircuit [.ledger (.const 1) [5, 6]
  [.dup 0, .popeq false [.field, .field] [.var 6, .var 5]]])

-- Results split over two `popeq`s pass in order and fail out of order.
#guard passes (mkCircuit [.ledger (.const 1) [5, 6]
  [.dup 0, .popeq false [.field] [.var 5], .dup 0, .popeq false [.field] [.var 6]]])
#guard !passes (mkCircuit [.ledger (.const 1) [5, 6]
  [.dup 0, .popeq false [.field] [.var 6], .dup 0, .popeq false [.field] [.var 5]]])

-- The same variable read twice.
#guard !passes (mkCircuit [.ledger (.const 1) [5, 5]
  [.dup 0, .popeq false [.field, .field] [.var 5, .var 5]]])

-- A `popeq` result that is not a plain variable.
#guard !passes (mkCircuit [.ledger (.const 1) [] [.dup 0, .popeq false [.field] [.const 0]]])

-- A read variable with no `popeq` to bind it.
#guard !passes (mkCircuit [.ledger (.const 1) [5] [.dup 0]])

end Examples.LedgerAgreement
