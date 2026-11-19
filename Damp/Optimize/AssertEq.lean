/-
`assert (e == 1)` is `assert e`.

An `assert` passes exactly when its condition evaluates to 1: a value of 0
fails it, and so does any other value (it is not a boolean). `e == 1` is 1
exactly when `e` is 1. So `assert (e == 1)` and `assert e` pass and fail on
exactly the same runs, whatever `e` is: no knowledge that `e` is a boolean is
needed. The rewrite drops one `test_eq` (2 rows) per occurrence.

The common source is Compact's `assert(x == true, ..)` on a `Boolean` read
from the ledger (`Set.member`, `List.isEmpty`, `MerkleTree.isFull`): a ledger
read is not range checked in the circuit, so the value is not known to be 0
or 1 and the expression-level rule of `algebra` (`e == 1` is `e` when `e` is
syntactically boolean) does not apply.

`Circuit.assertEq` rewrites the conditions of `assert` statements (also
`1 == e`, and any constant whose field value is 1), and nothing else; the
statement keeps its place. compactc keeps the comparison, so this runs at
`--O2` and `--O3` only (`Circuit.assertEq_sound` in
`Damp/Proofs/Optimize/AssertEq.lean`).
-/
import Damp.IR.Semantics

namespace Damp.IR

/-- The condition of an `assert`, without a comparison with 1. -/
def assertCond : Expr → Expr
  | .eq e (.const k) => if Fr.ofInt k = 1 then e else .eq e (.const k)
  | .eq (.const k) e => if Fr.ofInt k = 1 then e else .eq (.const k) e
  | c => c

/-- Rewrite the condition of an `assert`. -/
def Stmt.assertEq : Stmt → Stmt
  | .assert c msg => .assert (assertCond c) msg
  | s => s

/-- Rewrite the condition of every `assert`. -/
def Circuit.assertEq (c : Circuit) : Circuit := { c with body := c.body.map Stmt.assertEq }

end Damp.IR
