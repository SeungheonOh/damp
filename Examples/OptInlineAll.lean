import Damp
import Damp.Optimize.InlineAll

/-! Checks on dead code: the emitter's pruning of unused bindings, and
`Circuit.forwardAllOpt` (`--O2`), which removes computations whose only
consumers are witness-call arguments. Proved sound in
`Damp/Proofs/Optimize/InlineAll.lean` (`Circuit.forwardAllOpt_sound`). -/
namespace Examples.OptInlineAll
open Damp Damp.IR

/-- A circuit with inputs `0..n-1`, a body and outputs. -/
private def mk (n : Nat) (body : List Stmt) (outputs : List Expr) : Circuit where
  name := "t"
  args := []
  inputs := (List.range n).map fun v => { name := s!"x{v}", var := v, range := none }
  body := body.toArray
  result := .tuple []
  outputs := outputs

/-! ### Pruning is already a fixpoint

`Emit.pruneDeadBinds` walks the statements backwards and adds a binding's uses
to the live set only when it keeps the binding: a chain of bindings that only
feed each other and nothing else goes in one pass. -/

private def chain := mk 1
  [.bind 1 "a" (.add (.var 0) (.const 1)),
   .bind 2 "b" (.mul (.var 1) (.var 1)),
   .bind 3 "c" (.hash [.var 2]),
   .ledger (.const 1) [] [.addi (.var 0)]]
  []

#guard (Emit.pruned chain).body.size == 1

/-! ### What pruning keeps: values read only by witness arguments

`v1 := hash x; v2 := hash [v1, v1]; w(v2)`: the emitter compiles the witness
to its `private_input` only, yet counts `v2`, and through it `v1`, as used. -/

private def viaWitness := mk 1
  [.bind 1 "pk" (.hash [.var 0]),
   .bind 2 "cm" (.hash [.var 1, .var 1]),
   .witness (.const 1) "root" [.var 2] [(3, none)] (.prim .field),
   .ledger (.const 1) [] [.addi (.var 3)]]
  []

/-- Number of ZKIR instructions of the emitted circuit (0 if it cannot be emitted). -/
def size (c : Circuit) : Nat :=
  match Emit.circuit c with
  | .ok src => src.instructions.size
  | .error _ => 0

-- Both hashes are emitted. `forwardOpt` inlines only `cm` (used once), which
-- removes its hash; `pk` (used twice) stays, now read by the witness argument.
#guard (Emit.pruned viaWitness).body.size == 4
#guard size (Circuit.forwardOpt viaWitness) + 1 == size viaWitness
-- `forwardAllOpt` inlines both into the witness argument: no hash is left in
-- the circuit, and the witness is still asked the same question.
#guard size (Circuit.forwardAllOpt viaWitness) + 2 == size viaWitness
#guard (Circuit.forwardAllOpt viaWitness).body.toList.filterMap
    (fun | .witness _ _ args _ _ => some args | _ => none) ==
  [[.hash [.hash [.var 0], .hash [.var 0]]]]

end Examples.OptInlineAll
