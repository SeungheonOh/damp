import Examples.Counter
import Examples.Step
import Examples.Shapes
import Examples.Bytes
import Examples.Extras
import Examples.Vault
import Examples.Tuned

/-! The emitter-correctness theorem, run on examples.

`Damp/EmitCorrect.lean` proves that the ZKIR emitted for a circuit evaluates,
under the ZKIR evaluator, to what the IR semantics says. These checks compute
both sides for concrete circuits and inputs, accepted and rejected alike. They
are no substitute for the proof; they are how a wrong statement would have
been noticed before trying to prove it. -/
namespace Examples.EmitAgrees
open Damp Damp.IR

def prims : Zkir.Prims where
  transientHash xs := xs.foldl (fun acc x => acc * 3 + x) 7
  persistentHash _ xs := some ((List.range 32).map fun i => (xs.foldl (fun acc x => acc + x.val) i) % 256)
  transientCommit xs r := xs.foldl (· + ·) r

/-- The emitted ZKIR and the IR give the same result on this run. -/
def agrees (c : Circuit) (inputs priv pub : List Fr) : Bool :=
  match Emit.circuitCore c with
  | .ok src => src.run prims inputs priv pub == c.run prims inputs priv pub
  | .error _ => false

/-- The same for the circuit as shipped: unused bindings dropped, optimized. -/
def agreesShipped (c : Circuit) (inputs priv pub : List Fr) : Bool :=
  agrees (Emit.pruned c.optimize) inputs priv pub

def accepted (c : Circuit) (inputs priv pub : List Fr) : Bool :=
  (c.run prims inputs priv pub).isSome

private def bump := Examples.Counter.bump.circuit
private def arith := Examples.Counter.arith.circuit
private def step := Examples.Step.step.circuit
private def pay := Examples.Shapes.pay.circuit
private def move := Examples.Shapes.move.circuit
private def claim := Examples.Bytes.claim.circuit
private def advance := Examples.Extras.advance.circuit
private def spend := Examples.Vault.spend.circuit
private def settle := Examples.Tuned.settle.circuit

-- Accepted runs.
#guard accepted bump [12, 1, 0] [] [40] && agrees bump [12, 1, 0] [] [40]
#guard accepted bump [12, 0, 1] [] [40] && agrees bump [12, 0, 1] [] [40]
#guard accepted step [5, 1, 42] [7] [] && agrees step [5, 1, 42] [7] []
#guard accepted step [5, 0, 42] [] [] && agrees step [5, 0, 42] [] []
#guard accepted arith [4, 4, 100] [3] [97] && agrees arith [4, 4, 100] [3] [97]
#guard accepted settle [10, 20, 30, 40, 1] [] [130] && agrees settle [10, 20, 30, 40, 1] [] [130]

-- Rejected runs: a failed assert, a value out of range, a non-boolean
-- condition, a missing or surplus transcript entry.
#guard !accepted bump [600, 1, 0] [] [40] && agrees bump [600, 1, 0] [] [40]
#guard !accepted bump [70000, 1, 0] [] [40] && agrees bump [70000, 1, 0] [] [40]
#guard !accepted bump [12, 2, 0] [] [40] && agrees bump [12, 2, 0] [] [40]
#guard !accepted bump [12, 1, 0] [] [] && agrees bump [12, 1, 0] [] []
#guard !accepted bump [12, 1, 0] [] [40, 41] && agrees bump [12, 1, 0] [] [40, 41]
#guard !accepted step [5, 1, 42] [] [] && agrees step [5, 1, 42] [] []
#guard !accepted step [5, 1, 42] [11] [] && agrees step [5, 1, 42] [11] []
#guard !accepted arith [3, 4, 100] [3] [97] && agrees arith [3, 4, 100] [3] [97]

-- Whatever the outcome, the two sides agree. These sweep many transcripts
-- through the larger circuits, including byte strings and both hashes.
#guard (List.range 6).all fun n => agrees pay [77, 10, 3, 2] [] ((List.range n).map fun i => Fr.ofNat (i % 2))
#guard (List.range 6).all fun n => agrees move [5, 2, 1, 2, 3, 1, 1] [1000, 9] ((List.range n).map Fr.ofNat)
#guard (List.range 6).all fun n => agrees claim [1, 2, 3, 1] [7, 250] ((List.range n).map Fr.ofNat)
#guard (List.range 8).all fun n => agrees advance [0, 1, 1, 1, 500, 42] [11, 12] ((List.range n).map fun i => Fr.ofNat (i % 2))
#guard (List.range 5).all fun n => agrees spend [30] [21, 22] ((List.range n).map Fr.ofNat)

-- And for the circuits as shipped.
#guard agreesShipped bump [12, 1, 0] [] [40] && agreesShipped bump [600, 1, 0] [] [40]
#guard agreesShipped step [5, 1, 42] [7] [] && agreesShipped arith [4, 4, 100] [3] [97]
#guard agreesShipped settle [10, 20, 30, 40, 1] [] [130]
#guard (List.range 8).all fun n => agreesShipped advance [0, 1, 1, 1, 500, 42] [11, 12] ((List.range n).map fun i => Fr.ofNat (i % 2))

end Examples.EmitAgrees
