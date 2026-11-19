/-
When a ledger statement's instructions, as the executor sends them, are what
the circuit declares: the `popeq` results, read left to right, are exactly the
statement's read variables (each a plain variable), these are distinct, and no
other operand mentions one of them. `IR.Circuit.checkLedger` checks this on a
circuit, and the build refuses a circuit that fails it.
`Damp/Proofs/LedgerAgreement.lean` proves what the condition buys.
-/
import Damp.IR.Basic

namespace Damp.Impact

variable {α β : Type}

/-! ## Instructions: what a `popeq` reads, and the rest -/

/-- The values a `popeq` reads; nothing for any other instruction. -/
def Op.results : Op α → List α
  | .popeq _ _ r => r
  | _ => []

/-- How many values a `popeq` reads; `none` for any other instruction. -/
def Op.width? : Op α → Option Nat
  | .popeq _ _ r => some r.length
  | _ => none

/-- The instruction with what a `popeq` reads left empty. -/
def Op.blank : Op α → Op α
  | .popeq cached align _ => .popeq cached align []
  | op => op

/-- Every value read by the `popeq`s of a list of instructions, in order. -/
def allResults (ops : List (Op α)) : List α := ops.flatMap Op.results

/-- How many values each `popeq` of a list of instructions reads, in order. -/
def popeqWidths (ops : List (Op α)) : List Nat := ops.filterMap Op.width?

end Damp.Impact

namespace Damp.IR
open Impact

/-- What could make a ledger statement's instructions disagree with what it
    declares, if anything: its `popeq` results must be exactly its read
    variables, in order, each a plain variable; these must be distinct; and no
    other operand of any instruction may mention one of them. -/
def ledgerProblem (reads : List Var) (ops : List (Op Expr)) : Option String :=
  if !(allResults ops == reads.map Expr.var) then
    some s!"its popeq results are not exactly its read variables {reads}, in order"
  else if !decide reads.Nodup then
    some s!"it reads into the same variable twice: {reads}"
  else
    match (ops.flatMap fun op => Expr.varsList (op.blank.encode Expr.const)).find? reads.contains with
    | some v => some s!"an operand other than a popeq result mentions variable {v}, which the statement reads"
    | none => none

/-- What could make a statement's ledger instructions disagree with what it declares. -/
def Stmt.ledgerProblem : Stmt → Option String
  | .ledger _ reads ops => IR.ledgerProblem reads ops
  | _ => none

/-- A ledger statement whose instructions, as sent, are what it declares (see
    `ledgerProblem`); every other statement. -/
def Stmt.ledgerWellFormed (s : Stmt) : Bool := s.ledgerProblem.isNone

/-- Check every statement from index `i` on. -/
def checkLedgerFrom (name : String) : Nat → List Stmt → Except String Unit
  | _, [] => .ok ()
  | i, s :: ss =>
      match s.ledgerProblem with
      | some why => .error s!"circuit {name}: ledger statement {i}: {why}"
      | none => checkLedgerFrom name (i + 1) ss

/-- Check that every ledger statement of a circuit is well formed
    (`Stmt.ledgerWellFormed`), naming the first one that is not. -/
def Circuit.checkLedger (c : Circuit) : Except String Unit :=
  checkLedgerFrom c.name 0 c.body.toList

end Damp.IR
