import Examples.Counter

/-!
The reference semantics run on the example circuits, and a first theorem about
a circuit definition. The theorem is about the same value the compiler emits
ZKIR from: there is no separate model of the contract.
-/
namespace Examples.Semantics
open Damp Damp.IR

/-- A stand-in hash; the real one is a parameter of the semantics. -/
def prims : Zkir.Prims where
  transientHash xs := xs.foldl (· + ·) 0
  persistentHash _ xs := some (List.replicate 32 (xs.length % 256))
  transientCommit xs r := xs.foldl (· + ·) r

def bump : Circuit := Examples.Counter.bump.circuit

/-- Outputs of a run, or `none` if it fails. -/
def outputs (c : Circuit) (inputs priv pub : List Fr) : Option (List Nat) :=
  (c.run prims inputs priv pub).map fun o => o.outputs.map (·.val)

-- bump(x = 12, go, ¬stop): the counter read returns what the public state answers.
#guard outputs bump [12, 1, 0] [] [40] = some [40]
-- x ≥ 500 under `go` fails the assert; without `go` the assert is vacuous.
#guard outputs bump [600, 1, 0] [] [40] = none
#guard outputs bump [600, 0, 0] [] [40] = some [40]
-- A read that the public state does not answer is rejected.
#guard outputs bump [12, 1, 0] [] [] = none

/-- Under a false guard the increment's public inputs are zeroed, as ZKIR's `impact` does. -/
def groups (c : Circuit) (inputs priv pub : List Fr) : List (Bool × List Nat) :=
  match c.run prims inputs priv pub with
  | some o => o.groups.map fun g => (g.active, g.vals.map (·.val))
  | none => []

#guard (groups bump [12, 0, 0] [] [40]).take 3 = [(false, [0, 0, 0, 0]), (false, [0, 0]), (false, [0])]
#guard (groups bump [12, 1, 0] [] [40]).take 3 = [(true, [0x70, 1, 1, 0]), (true, [0x0e, 12]), (true, [0xa1])]

/-! ### A theorem about a circuit definition -/

circuit sumOfSquares (x y : Field) : Field := do
  const a := x * x
  const b := y * y
  return a + b

/-- For every input, the circuit computes `x² + y²` and touches neither oracle. -/
theorem sumOfSquares_spec (p : Zkir.Prims) (x y : Fr) :
    sumOfSquares.circuit.run p [x, y] [] []
      = some { outputs := [x * x + y * y], groups := [] } := by
  rfl

end Examples.Semantics
