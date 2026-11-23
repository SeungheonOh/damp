import Damp
import Damp.Optimize.LedgerDeadStore
import Damp.Optimize.LedgerReuse
import Damp.Ledger.Merkle

/-! Checks on the opt-in ledger pass `Circuit.ledgerDeadStore`, run by the build.

Proved sound against the modelled ledger in
`Damp/Proofs/Optimize/LedgerDeadStore.lean` (`Circuit.ledgerDeadStore_soundLedger`).
These checks show the rewrite firing, each side condition stopping it, and runs
through the executor against the VM model leaving the same outputs and ledger
state. -/
namespace Examples.OptLedgerDeadStore
open Damp Damp.IR Damp.Impact Damp.Ledger

private def one : Expr := .const 1
private def wrA (g : Expr) (k : Aligned Expr) (a : List Zkir.AlignAtom) (vs : List Expr) : Stmt :=
  .ledger g [] [.push false k, .push true ⟨a, vs⟩, .ins false 1]
private def wr (i : Nat) (e : Expr) : Stmt := wrA one (fieldKey i) [.field] [e]
private def rd (i v : Nat) : Stmt :=
  .ledger one [v] [.dup 0, .idx false false [fieldKey i], .popeq false [.field] [.var v]]

private def mk (n : Nat) (body : List Stmt) (outputs : List Expr) : Circuit where
  name := "t"
  args := []
  inputs := (List.range n).map fun v => { name := s!"x{v}", var := v, range := none }
  body := body.toArray
  result := .tuple []
  outputs := outputs

private def shape (c : Circuit) : String :=
  String.ofList (c.body.toList.map fun | .ledger .. => 'L' | .bind .. => 'B' | .witness .. => 'W' | _ => 'A')
private def after (c : Circuit) : String := shape c.ledgerDeadStore

/-! ### The rewrite fires -/

#guard after (mk 1 [wr 1 (.var 0), wr 1 (.add (.var 0) (.var 0))] []) == "L"
-- bindings, assertions and witness calls between
#guard after (mk 1 [wr 1 (.var 0), .bind 5 "t" (.lt 8 (.var 0) (.const 3)), .assert (.var 5) "a",
    .witness one "w" [] [] (.tuple []), wr 1 (.var 0)] []) == "BAWL"
-- the second write may hold any value of any alignment
#guard after (mk 1 [wr 1 (.var 0), wrA one (fieldKey 1) [.bytes 40] [.var 0, .var 0]] []) == "L"
-- a run of writes keeps the last
#guard after (mk 1 [wr 1 (.var 0), wr 1 (.var 0), wr 1 (.var 0)] []) == "L"
-- not across `createZswapOutput` or a contract call (`ctxWitness`)
#guard after (mk 1 [wr 1 (.var 0), .witness one "createZswapOutput" [] [] (.tuple []), wr 1 (.var 0)] []) == "LWL"
#guard after (mk 1 [wr 1 (.var 0), .witness one "call:I.c" [] [] (.tuple []), wr 1 (.var 0)] []) == "LWL"

/-! ### The side conditions stop it -/

-- a read of the field between
#guard after (mk 1 [wr 1 (.var 0), rd 1 5, wr 1 (.var 5)] [.var 5]) == "LLL"
-- any other ledger statement between, even of another field
#guard after (mk 1 [wr 1 (.var 0), wr 2 (.var 0), wr 1 (.var 0)] []) == "LLL"
-- a different key
#guard after (mk 1 [wr 1 (.var 0), wr 2 (.var 0)] []) == "LL"
-- a guard that is not the constant 1, on either write
#guard after (mk 1 [wrA (.var 0) (fieldKey 1) [.field] [.var 0], wr 1 (.var 0)] []) == "LL"
#guard after (mk 1 [wr 1 (.var 0), wrA (.var 0) (fieldKey 1) [.field] [.var 0]] []) == "LL"
-- a value that can fail (a comparison): dropping it would drop the failure
#guard after (mk 1 [wr 1 (.lt 8 (.var 0) (.const 3)), wr 1 (.var 0)] []) == "LL"
-- a value of an alignment other than one field element (it might not fit)
#guard after (mk 1 [wrA one (fieldKey 1) [.bytes 2] [.var 0], wr 1 (.var 0)] []) == "LL"
-- ... unless it is a constant that fits, as one atom
#guard after (mk 1 [wrA one (fieldKey 1) [.bytes 2] [.const 5], wr 1 (.var 0)] []) == "L"
#guard after (mk 1 [wrA one (fieldKey 1) [.bytes 1] [.const 300], wr 1 (.var 0)] []) == "LL"
#guard after (mk 1 [wrA one (fieldKey 1) [.bytes 1, .bytes 1] [.const 1, .const 2], wr 1 (.var 0)] []) == "LL"
-- a key that is not constant
#guard after (mk 1 [wrA one ⟨[.field], [.var 0]⟩ [.field] [.var 0], wrA one ⟨[.field], [.var 0]⟩ [.field] [.var 0]] [])
  == "LL"
-- an overwriting write further than the window
#guard after (mk 1 (wr 1 (.var 0) :: (List.range 70).map (fun i => .bind (10 + i) "t" (.var 0)) ++ [wr 1 (.var 0)]) [])
  == String.ofList ('L' :: List.replicate 70 'B' ++ ['L'])

/-! ### Runs through the executor against the VM model -/

private def σ₀ : LedgerState where
  context := .array [.cell ⟨[.bytes 32], [12345]⟩, .null, .cell (AV.ofU64 7)]
  effects := .array (List.replicate 9 (.map []))
  state := .array [.null, .cell ⟨[.field], [3]⟩, .cell ⟨[.field], [4]⟩, .map []]

private def noWitness : String → List Fr → Unit → Option (List Fr × Unit) := fun _ _ _ => none

private def run (c : Circuit) (inputs : List Nat) : String :=
  match Exec.run Crypto.prims (oracles merkleHooks noWitness) c (inputs.map Fr.ofNat) () σ₀ with
  | none => "fails"
  | some r => reprStr (r.outputs.map (·.val), r.priv.map (·.val), r.ledger.state, r.ledger.context, r.ledger.effects)

private def same (c : Circuit) (inputs : List Nat) : Bool := run c inputs == run c.ledgerDeadStore inputs

-- written, read back, written: after `ledgerReuse` forwards the read, the first write is dead
private def c1 := mk 1 [wr 1 (.var 0), rd 1 5, wr 1 (.add (.var 5) (.var 0)), rd 1 6] [.var 6]
#guard shape c1.ledgerReuse == "LBLB"
#guard after c1.ledgerReuse == "BLB"
#guard same c1.ledgerReuse [9]
#guard run c1 [9] == run c1.ledgerReuse.ledgerDeadStore [9]
-- a write into a map field, then over it
private def c2 := mk 1 [wrA one (fieldKey 3) [.field] [.var 0], wrA one (fieldKey 3) [.field] [.const 8]] []
#guard after c2 == "L"
#guard same c2 [1]
-- a field that does not exist: both fail
private def c3 := mk 1 [wr 9 (.var 0), wr 9 (.var 0)] []
#guard run c3 [1] == "fails"
#guard same c3 [1]

end Examples.OptLedgerDeadStore
