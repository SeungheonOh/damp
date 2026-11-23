/-
Ledger-level dead stores: drop a cell write that a later cell write of the same
key overwrites, with nothing between that touches the ledger.

A write `push false k; push true v; ins false 1` under the constant guard 1,
with a constant key `k` and a value of one field element whose expression
cannot fail (`Expr.total []` of `Simplify`), or of constants that fit their
alignment as one atom (`droppableValue`), is dropped when the next ledger statement, after
any number of bindings, assertions, range checks and witness calls other than
a user's witness (`stateWitness`, which may read the contract state, so would
see the dropped write) (at most
`deadStoreWindow` statements), is a cell write of the same key, also under the
constant guard 1. Only what the dropped write would have left can differ, and
the second write replaces it; a failure of the first write (the key does not
fit the state, the state has no such slot) is a failure of the second on the
same state.

After `Circuit.ledgerReuse` has forwarded the reads between such writes, this
is the remaining pattern of `pm_19287` (a cell written, read back, written).

Not a `Pass.Sound` pass: it sends fewer ledger statements. It is
`Pass.SoundLedger` (`Damp/Proofs/Optimize/LedgerDeadStore.lean`).
-/
import Damp.Optimize.LedgerReuse
import Damp.Optimize.Simplify

namespace Damp.IR
open Damp.Impact

def Expr.isConst : Expr → Bool
  | .const _ => true
  | _ => false

/-- How far ahead the pass looks for the overwriting write. -/
def deadStoreWindow : Nat := 64

/-- A written value whose write the pass may drop: one field element whose
    expression cannot fail (`Expr.total []`), or constants that fit their
    alignment as one atom of at most 32 bytes (`constAV`, computed here: the
    VM stores exactly that value, and a Merkle-tree slot would accept it). -/
def droppableValue (v : Aligned Expr) : Bool :=
  (match v with
   | ⟨[.field], [e]⟩ => e.total []
   | _ => false) ||
  (match constAV v with
   | some vv => vv.toHash.isSome
   | none => false)

/-- The key of a write the pass may drop. -/
def droppableWrite? : Stmt → Option (Aligned Expr)
  | .ledger (.const 1) [] [.push false k, .push true v, .ins false 1] =>
      if k.vals.all Expr.isConst && droppableValue v then some k else none
  | _ => none

/-- The next ledger statement, within `fuel` statements, is a cell write of `k`
    under the constant guard 1. -/
def overwrites (k : Aligned Expr) : Nat → List Stmt → Bool
  | 0, _ => false
  | _, [] => false
  | n + 1, s :: rest =>
      match s with
      | .ledger (.const 1) [] [.push false k', .push true _, .ins false 1] => alignedSame k' k
      | .ledger .. => false
      | .witness _ name _ _ _ => !stateWitness name && overwrites k n rest
      | _ => overwrites k n rest

def deadStoreGo : List Stmt → List Stmt
  | [] => []
  | s :: rest =>
      match droppableWrite? s with
      | some k => if overwrites k deadStoreWindow rest then deadStoreGo rest else s :: deadStoreGo rest
      | none => s :: deadStoreGo rest

/-- Drop cell writes that the next ledger statement overwrites (see the file header). -/
def Circuit.ledgerDeadStore (c : Circuit) : Circuit :=
  { c with body := (deadStoreGo c.body.toList).toArray }

end Damp.IR
