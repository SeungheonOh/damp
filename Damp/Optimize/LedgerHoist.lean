/-
Ledger-level reordering: move a read of the call context up to an earlier
ledger statement it can be merged with.

`Circuit.ledgerMerge` merges a ledger statement into the previous one only
across statements that are not ledger statements. A read of the call context
(`dup 2; idx _ false path; popeq`, `Kernel.self` and the other context reads
of `Damp/Lang/Ledger.lean`) changes nothing in the ledger, and no ledger
statement changes the call context, so it gives the same answer anywhere: it
may move above other ledger statements too. `Circuit.ledgerHoist` moves such
a read up to right after the nearest earlier ledger statement `L` with the same
guard, when

* every statement between (at most `hoistWindow`) commutes with it
  (`lcommutes true`: neither reads nor binds what the other binds; no witness
  that writes the call context, `ctxWitness`: `createZswapOutput`);
* the two statements pass `mergeInto` (so that `Circuit.ledgerMerge`, which
  runs next, makes them one request; the move by itself changes nothing but
  the order of the public transcript).

Two statements that both write the ledger are never reordered: only reads of
the context move. The order of the effects' entries (which depend on the
order of their writes in the model) is therefore never changed.

Not a `Pass.Sound` pass (the public transcript is reordered). It is
`Pass.SoundLedger` (`Damp/Proofs/Optimize/LedgerHoist.lean`).
-/
import Damp.Optimize.LedgerMerge

namespace Damp.IR
open Damp.Impact

/-- A read of the call context: `dup 2; idx _ false path; popeq _ a _`. -/
def Stmt.ctxRead : Stmt → Bool
  | .ledger _ _ [.dup 2, .idx _ false _, .popeq _ _ _] => true
  | _ => false

/-- A ledger statement without instructions (never moved above). -/
def Stmt.emptyLedger : Stmt → Bool
  | .ledger _ _ [] => true
  | _ => false

/-- A ledger statement with guard `g`. -/
def Stmt.guardIs (g : Expr) : Stmt → Bool
  | .ledger g' .. => g' == g
  | _ => false

/-- How many statements a context read may move above. -/
def hoistWindow : Nat := 64

/-- The first context read with guard `g` in `l`, within `n` statements, that
    moves above every statement before it and merges into `.ledger g rs ops`:
    the statements before it, the read, and the rest. -/
def findCtxRead (g : Expr) (rs : List Var) (ops : List (Op Expr)) : Nat → List Stmt → Option (List Stmt × Stmt × List Stmt)
  | 0, _ => none
  | _, [] => none
  | n + 1, x :: l =>
      if x.ctxRead && x.guardIs g && (mergeInto g rs ops x).isSome then
        some ([], x, l)
      else
        (findCtxRead g rs ops n l).bind fun (mid, r, rest) =>
          if lcommutes true r x && !x.emptyLedger then some (x :: mid, r, rest) else none

/-- The scan: after each ledger statement, pull up a later context read it can merge with. -/
def hoistGo : Nat → List Stmt → List Stmt
  | 0, l => l
  | _ + 1, [] => []
  | fuel + 1, s :: rest =>
      match s with
      | .ledger g rs ops =>
          match findCtxRead g rs ops hoistWindow rest with
          | some (mid, r, rest') => s :: r :: hoistGo fuel (mid ++ rest')
          | none => s :: hoistGo fuel rest
      | _ => s :: hoistGo fuel rest

/-- Move reads of the call context up to an earlier ledger statement they merge with (see the file header). -/
def Circuit.ledgerHoist (c : Circuit) : Circuit :=
  { c with body := (hoistGo (c.body.size + 1) c.body.toList).toArray }

end Damp.IR
