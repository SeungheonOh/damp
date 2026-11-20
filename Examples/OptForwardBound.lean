import Damp

/-! Regression check: `forwardAll` (inside `forwardAllOpt`, `--O2`) must not
build exponentially large expressions. A Merkle path root of depth 32 selects
on the previous level's digest twice per level; substituting every binding
into the next doubled the expression at each level (2^32 nodes), and
`damp-bench --O2` ran out of memory on `zerocash_core`. `forwardAll` now
substitutes only bindings whose substituted expression costs at most 64
instructions (`Damp/Optimize/Forward.lean`). -/
namespace Examples.OptForwardBound
open Damp Damp.IR

/-- Inputs: a direction bit `0` and a leaf `1`; level `k` binds variable `k + 2`
    to the hash of the previous digest and itself, in an order the bit picks. -/
def chain (depth : Nat) : Circuit where
  name := "chain"
  args := []
  inputs := [{ name := "dir", var := 0, range := some .bool }, { name := "leaf", var := 1, range := none }]
  body := ((List.range depth).map fun k =>
    let prev : Expr := .var (k + 1)
    Stmt.bind (k + 2) "d" (.hash [.select (.var 0) prev (.const 7), .select (.var 0) (.const 7) prev])).toArray
  result := .prim .field
  outputs := [.var (depth + 1)]

/-- The largest cost of a bound expression. -/
def maxCost (c : Circuit) : Nat :=
  c.body.toList.foldl (fun m s => match s with | .bind _ _ e => max m (Algebra.cost e) | _ => m) 0

-- Every substituted expression stays small ...
#guard maxCost (Circuit.forwardAll (chain 32)) ≤ 64 * 4
-- ... and the pass leaves the depth-32 chain as small as it was.
#guard Circuit.emittedSize (Circuit.forwardAllOpt (chain 32)) == Circuit.emittedSize (chain 32)
#guard ((Circuit.optimizeFull (chain 32)).emittedSize.getD 0) ≤ ((chain 32).emittedSize.getD 0)
#guard (chain 32).emittedSize.isSome

end Examples.OptForwardBound
