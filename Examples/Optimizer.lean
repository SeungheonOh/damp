import Examples.Counter
import Examples.Tuned
import Examples.Step

/-! Checks on the optimizer, run by the build.

Both layers are proved correct in `Damp/Proofs/Optimize/Simplify.lean` (`Expr.simp_eval`,
`Circuit.optimize_correct`). These checks pin down which rewrites fire, and run
the reference semantics before and after optimization on real and hand-made
circuits, including ones the optimizer used to get wrong when evaluation was
taken to be total. -/
namespace Examples.Optimizer
open Damp Damp.IR

/-! ### Expression rewrites -/

private def x : Expr := .var 0
private def y : Expr := .var 1

#guard (Expr.add x (.const 0)).simp == x
#guard (Expr.mul (.const 1) x).simp == x
#guard (Expr.mul x (.const 0)).simp == .const 0
#guard (Expr.neg (.neg x)).simp == x
#guard (Expr.add (.const 2) (.const 3)).simp == .const 5
#guard (Expr.select (.const 1) x y).simp == x
#guard (Expr.select (.const 0) x y).simp == y
#guard (Expr.eq x x).simp == .const 1
#guard (Expr.lt 8 (.const 3) (.const 9)).simp == .const 1
-- Equal branches: dropped when the condition cannot fail and is 0 or 1.
#guard (Expr.select (.eq x y) x x).simp == x
-- A negated condition swaps the branches.
#guard (Expr.select (.select y (.const 0) (.const 1)) x (.const 7)).simp == .select y (.const 7) x
-- Rewrites apply inside larger expressions.
#guard (Expr.mul (.add x (.const 0)) (.add (.const 1) (.const 1))).simp == .mul x (.const 2)

/-! Rewrites that would drop something that can fail are not made. A comparison
fails unless both sides fit its width, and a conditional fails unless its
condition is 0 or 1, so a circuit must keep them even when their value is not
needed. -/

private def bad : Expr := .lt 8 x y   -- fails unless both fit in 8 bits

#guard (Expr.mul (.const 0) bad).simp == .mul (.const 0) bad
#guard (Expr.mul bad (.const 0)).simp == .mul bad (.const 0)
#guard (Expr.select (.const 1) x bad).simp == .select (.const 1) x bad
#guard (Expr.select (.const 0) bad y).simp == .select (.const 0) bad y
#guard (Expr.eq bad bad).simp == .eq bad bad
-- A condition not known to be 0 or 1 is still checked.
#guard (Expr.select y x x).simp == .select y x x
#guard (Expr.select bad x x).simp == .select bad x x
-- A constant condition other than 0 or 1 fails, and stays.
#guard (Expr.select (.const 2) x y).simp == .select (.const 2) x y
-- Comparisons of constants are folded only when both fit the width.
#guard (Expr.lt 8 (.const 300) (.const 9)).simp == .lt 8 (.const 300) (.const 9)
#guard (Expr.lt 255 (.const 3) (.const 9)).simp == .lt 255 (.const 3) (.const 9)
#guard (Expr.lt 8 (.const 9) (.const 3)).simp == .const 0

/-! ### Range checks -/

#guard Range.implies (.bits 8) (.bits 16)
#guard !Range.implies (.bits 16) (.bits 8)
#guard Range.implies .bool (.bits 8)
#guard Range.implies (.below 10 4) (.bits 4)
#guard !Range.implies (.below 20 6) (.bits 4)
-- Widths of 255 bits or more never pass, and a `below` bound must fit its width.
#guard !Range.implies (.bits 8) (.bits 300)
#guard !Range.implies .zero (.bits 255)
#guard !Range.implies .bool (.below 1 4)
#guard !Range.implies (.bits 4) (.below 16 4)
#guard Range.implies (.bits 4) (.below 16 5)

/-! ### Whole circuits, before and after -/

def prims : Zkir.Prims where
  transientHash xs := xs.foldl (· + ·) 0
  persistentHash _ xs := some (List.replicate 32 (xs.length % 256))
  transientCommit xs r := xs.foldl (· + ·) r

/-- What a run produces that anyone can observe: outputs, and the public inputs
    of the ledger instructions that actually ran. -/
def observe (c : Circuit) (inputs priv pub : List Fr) : Option (List Nat × List (List Nat)) :=
  (c.run prims inputs priv pub).map fun o =>
    (o.outputs.map (·.val), (o.groups.filter (·.active)).map fun g => g.vals.map (·.val))

/-- The optimized circuit behaves as the original on this run. -/
def agrees (c : Circuit) (inputs priv pub : List Fr) : Bool :=
  observe c inputs priv pub == observe c.optimize inputs priv pub

private def settle := Examples.Tuned.settle.circuit
private def bump := Examples.Counter.bump.circuit
private def step := Examples.Step.step.circuit

-- The optimizer really does remove statements from `settle`.
#guard settle.optimize.body.size < settle.body.size

#guard agrees settle [10, 20, 30, 40, 1] [] [130]
#guard agrees settle [10, 20, 30, 40, 0] [] [80]
#guard agrees settle [65535, 0, 65535, 1, 1] [] [7]
-- A run that fails still fails: an out-of-range input, an unanswered read.
#guard agrees settle [70000, 0, 0, 0, 1] [] [0]
#guard agrees settle [1, 2, 3, 4, 1] [] []
#guard (observe settle [1, 2, 3, 4, 1] [] [11]).isSome

#guard agrees bump [12, 1, 0] [] [40]
#guard agrees bump [600, 1, 0] [] [40]
#guard agrees bump [12, 0, 1] [] [40]
#guard agrees step [5, 1, 42] [7] []
#guard agrees step [5, 0, 42] [] []
#guard agrees step [5, 1, 5000] [7] []

/-! ### Hand-made circuits the optimizer used to get wrong

Each would have started accepting a run the original rejects. -/

/-- A circuit with inputs `0..n-1`, a body and outputs. -/
private def mk (n : Nat) (body : List Stmt) (outputs : List Expr) : Circuit where
  name := "t"
  args := []
  inputs := (List.range n).map fun v => { name := s!"x{v}", var := v, range := none }
  body := body.toArray
  result := .tuple []
  outputs := outputs

/-- The run fails, before and after optimization. -/
def rejects (c : Circuit) (inputs priv pub : List Fr) : Bool :=
  (observe c inputs priv pub).isNone && agrees c inputs priv pub

-- The unused branch of a constant conditional fails for x0 = 300.
private def selDrop := mk 1 [.bind 1 "t" (.select (.const 1) x (.lt 8 x (.const 1)))] [.var 1]
#guard rejects selDrop [300] [] []
#guard agrees selDrop [3] [] []

-- `select c 1 0` with `c` not known to be 0 or 1.
private def selBool := mk 1 [.bind 1 "t" (.select x (.const 1) (.const 0))] [.var 1]
#guard selBool.optimize.body.size == 1
#guard rejects selBool [5] [] []
#guard agrees selBool [1] [] []
-- After a boolean check it is rewritten to `c`.
private def selBool' := mk 1 [.constrain x .bool, .bind 1 "t" (.select x (.const 1) (.const 0))] [.var 1]
#guard selBool'.optimize.body.size == 1
#guard selBool'.optimize.outputs == [x]
#guard agrees selBool' [1] [] [] && rejects selBool' [5] [] []

-- `select c a a` with `c` not known to be 0 or 1.
private def selSame := mk 2 [.bind 2 "t" (.select x y y)] [.var 2]
#guard rejects selSame [5, 7] [] []
#guard agrees selSame [1, 7] [] []

-- A witness call guarded by 2 fails; it was dropped as if the guard were 0.
private def wit2 := mk 0 [.witness (.const 2) "w" [] [(0, none)] (.prim .field)] [.var 0]
#guard wit2.optimize.body.size == 1
#guard rejects wit2 [] [] []
-- Guarded by 0 it is dropped, its result is 0 ...
private def wit0 := mk 0 [.witness (.const 0) "w" [] [(0, some (.bits 8))] (.prim .field)] [.var 0]
#guard wit0.optimize.body.size == 0
#guard agrees wit0 [] [] []
-- ... unless 0 fails its range check, which happens even when nothing is asked.
private def wit0bad := mk 0 [.witness (.const 0) "w" [] [(0, some (.bits 300))] (.prim .field)] [.var 0]
#guard wit0bad.optimize.body.size == 1
#guard rejects wit0bad [] [] []

-- A ledger statement guarded by 0 evaluates its operands anyway.
private def led0bad := mk 1 [.ledger (.const 0) [] [.addi (.lt 8 x (.const 1))]] []
#guard led0bad.optimize.body.size == 1
#guard rejects led0bad [300] [] []
#guard agrees led0bad [3] [] []
-- With operands that cannot fail it is dropped; its group was inactive anyway.
private def led0 := mk 1 [.ledger (.const 0) [] [.addi x]] []
#guard led0.optimize.body.size == 0
#guard agrees led0 [3] [] []

-- A second check that the first does not imply under the real range semantics.
private def wide := mk 1 [.constrain x (.bits 8), .constrain x (.bits 300)] []
#guard wide.optimize.body.size == 2
#guard rejects wide [3] [] []
-- A check the first does imply is still dropped.
private def narrow := mk 1 [.constrain x (.bits 8), .constrain x (.bits 16)] []
#guard narrow.optimize.body.size == 1
#guard agrees narrow [3] [] [] && rejects narrow [300] [] []

-- A variable bound twice, with a remembered copy of its first value: the pass
-- gives up rather than lose that value, and the circuit is left as it is.
private def rebind := mk 1 [.bind 1 "a" x, .bind 2 "b" (.add y (.const 1)),
  .bind 0 "c" (.add x (.const 5)), .bind 3 "d" (.add (.var 1) (.const 0))] [.var 3]
#guard rebind.optimize.body.size == rebind.body.size
#guard agrees rebind [4] [] []

/-! ### What the executor does, before and after

The executor (`Damp/Executor/Spec.lean`) sends a ledger statement's instructions to
the ledger with their operands evaluated before the reads are bound. Here the
read variable `0` was bound to 5 earlier, a binding the optimized circuit does
not emit, so the instruction `addi 0` used to be sent as `addi 0` instead of
`addi 5`: the circuit accepted the same run, but the ledger was asked
something else. The pass now gives up on such a circuit (`Facts.knows`). -/

/-- A ledger that writes down the immediates of the `addi` instructions it is
    sent, and answers every read with 7. -/
def logLedger : Exec.Oracles Unit (List Nat) :=
  ⟨fun _ _ _ _ => none,
   fun req log => some ([7], log ++ req.filterMap fun | .addi i => some i.val | _ => none)⟩

/-- What the executor leaves: outputs and the ledger's log. -/
def execObserve (c : Circuit) : Option (List Nat × List Nat) :=
  (Exec.run prims logLedger c [] () []).map fun r => (r.outputs.map (·.val), r.ledger)

private def readKnown := mk 0 [.bind 0 "r" (.const 5),
  .ledger (.const 1) [0] [.addi (.var 0), .popeq false [] [.var 0]]] [.var 0]
#guard execObserve readKnown == some ([7], [5])
#guard execObserve readKnown.optimize == some ([7], [5])
#guard readKnown.optimize.body.size == readKnown.body.size
#guard agrees readKnown [] [] [7]

end Examples.Optimizer
