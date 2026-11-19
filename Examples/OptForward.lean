import Damp
import Damp.Optimize.Forward

/-! Checks on forward substitution (`Circuit.forward`, `Circuit.forwardOpt`), run
by the build.

The pass is proved sound in `Damp/Proofs/Optimize/Forward.lean`
(`Circuit.forward_sound`, `Circuit.forwardOpt_sound`). These checks show the
substitution firing, and for each side condition a run on which substituting
anyway would change the result. -/
namespace Examples.OptForward
open Damp Damp.IR

private def x : Expr := .var 0
private def y : Expr := .var 1
/-- Fails unless both sides fit in 8 bits. -/
private def bad : Expr := .lt 8 x y

def prims : Zkir.Prims where
  transientHash xs := xs.foldl (· + ·) 0
  persistentHash _ xs := some (List.replicate 32 (xs.length % 256))
  transientCommit xs r := xs.foldl (· + ·) r

/-- A circuit with inputs `0..n-1`, a body and outputs. -/
private def mk (n : Nat) (body : List Stmt) (outputs : List Expr) : Circuit where
  name := "t"
  args := []
  inputs := (List.range n).map fun v => { name := s!"x{v}", var := v, range := none }
  body := body.toArray
  result := .tuple []
  outputs := outputs

def observe (c : Circuit) (inputs priv pub : List Fr) : Option (List Nat × List (List Nat)) :=
  (c.run prims inputs priv pub).map fun o =>
    (o.outputs.map (·.val), (o.groups.filter (·.active)).map fun g => g.vals.map (·.val))

def agrees (c : Circuit) (inputs priv pub : List Fr) : Bool :=
  observe c inputs priv pub == observe (Circuit.forward c) inputs priv pub

/-- The expressions of a circuit's statements, in order. -/
private def exprs (c : Circuit) : List (List Expr) :=
  c.body.toList.map fun
    | .bind _ _ e => [e] | .assert e _ => [e] | .constrain e _ => [e]
    | .witness g _ args _ _ => g :: args | .ledger g _ ops => g :: ops.flatMap (·.encode Expr.const)

/-! ### It fires, and `algebra` cashes it in -/

/-- `v2 := x - y; v3 := v2 + y`, written to the ledger and returned. -/
private def chain := mk 2
  [.bind 2 "d" (.add x (.neg y)),
   .bind 3 "e" (.add (.var 2) y),
   .assert (.eq (.var 3) (.const 5)) "five",
   .ledger (.const 1) [] [.addi (.var 3)]]
  [.mul (.var 3) (.const 2)]

-- `v2` is used once, `v3` twice: `v2` is inlined into `v3`'s binding; `v3` stays
-- named (its uses are rewritten only when it is used at most once).
#guard exprs (Circuit.forward chain) ==
  [[.add x (.neg y)], [.add (.add x (.neg y)) y], [.eq (.var 3) (.const 5)], [.const 1, .const 14, .var 3]]
-- `forwardAll` inlines everything it may.
#guard exprs (Circuit.forwardAll chain) ==
  [[.add x (.neg y)], [.add (.add x (.neg y)) y], [.eq (.add (.add x (.neg y)) y) (.const 5)],
   [.const 1, .const 14, .add (.add x (.neg y)) y]]
-- After `algebra`, `v3` is `x`, which `simplify` propagates as a copy (and
-- drops the copy).
#guard exprs (Circuit.forward chain).algebra.simplify ==
  [[.add x (.neg y)], [.eq x (.const 5)], [.const 1, .const 14, x]]
#guard agrees chain [5, 3] [] []
#guard agrees chain [4, 3] [] []
#guard (observe chain [5, 3] [] []).isSome

/-! ### Side conditions -/

-- A binding that mentions its own variable is not remembered: after
-- `v2 := v2 + 1`, `v2 + 1` means something else. With `v2 = 0` initially,
-- the output is 1; substituting would give 2.
private def selfRef := mk 0 [.bind 2 "s" (.add (.var 2) (.const 1))] [.var 2]
#guard (Circuit.forward selfRef).outputs == [.var 2]
#guard observe selfRef [] [] [] == some ([1], [])
#guard observe (mk 0 [.bind 2 "s" (.add (.var 2) (.const 1))] [.add (.var 2) (.const 1)]) [] [] [] ==
  some ([2], [])

-- A binding is forgotten when a variable it mentions is bound again:
-- `v2 := x + y; x := 7` leaves `v2` as it was (with `x = 1`, `y = 2`, 3),
-- while `x + y` is now 9.
private def rebound := mk 2 [.bind 2 "s" (.add x y), .bind 0 "x" (.const 7)] [.var 2]
#guard (Circuit.forward rebound).outputs == [.var 2]
#guard observe rebound [1, 2] [] [] == some ([3], [])
#guard observe (mk 2 [.bind 2 "s" (.add x y), .bind 0 "x" (.const 7)] [.add x y]) [1, 2] [] [] ==
  some ([9], [])

-- ... and when its own variable is bound again (here by a witness).
private def rebind := mk 2
  [.bind 2 "s" (.add x y), .witness (.const 1) "w" [] [(2, none)] (.prim .field)] [.var 2]
#guard (Circuit.forward rebind).outputs == [.var 2]
#guard observe rebind [1, 2] [40] [] == some ([40], [])

-- Ledger operands are not rewritten with a binding that mentions a read
-- variable: they are evaluated both before the reads (the request) and after
-- (the public inputs). Here `v2 := v5 + 1` with `v5 = 0` before the read and
-- 9 after: the operand `v2` is 1, `v5 + 1` would be 10.
private def readVar := mk 0
  [.bind 2 "s" (.add (.var 5) (.const 1)),
   .ledger (.const 1) [5] [.addi (.var 2), .popeq false [.field] [.var 5]]] []
#guard exprs (Circuit.forward readVar) ==
  [[.add (.var 5) (.const 1)], [.const 1, .const 14, .var 2, .const 12, .const 1, .const (-2), .var 5]]
#guard agrees readVar [] [] [9]
private def readVarNaive := mk 0
  [.bind 2 "s" (.add (.var 5) (.const 1)),
   .ledger (.const 1) [5] [.addi (.add (.var 5) (.const 1)), .popeq false [.field] [.var 5]]] []
#guard observe readVarNaive [] [] [9] != observe readVar [] [] [9]
-- (The naive rewrite also breaks the ledger check.)
#guard readVar.checkLedger matches .ok ()
#guard !(readVarNaive.checkLedger matches .ok ())
#guard (Circuit.forward readVar).checkLedger matches .ok ()

-- A `popeq` result stays the read variable even when that variable was bound
-- (wrongly) before; the guard of a ledger statement is rewritten.
private def popeqBound := mk 1
  [.bind 5 "s" (.add x (.const 1)), .bind 6 "g" (.eq x (.const 1)),
   .ledger (.var 6) [5] [.popeq false [.field] [.var 5]]] [.var 5]
#guard exprs (Circuit.forward popeqBound) ==
  [[.add x (.const 1)], [.eq x (.const 1)], [.eq x (.const 1), .const 12, .const 1, .const (-2), .var 5]]
#guard agrees popeqBound [1] [] [9]
#guard agrees popeqBound [0] [] []

-- A binding that fails still fails the run after its only use is inlined: the
-- `bind` stays (with `x = 300`, `bad` fails).
private def failing := mk 2 [.bind 2 "b" bad] [.add (.var 2) (.const 1)]
#guard (Circuit.forward failing).outputs == [.add bad (.const 1)]
#guard (Circuit.forward failing).body.size == 1
#guard observe failing [300, 2] [] [] == none
#guard agrees failing [300, 2] [] []
#guard agrees failing [1, 2] [] []

-- Witness arguments are rewritten (the oracle is asked the same values).
private def witArg := mk 2
  [.bind 2 "s" (.add x y), .witness (.const 1) "w" [.var 2] [(3, none)] (.prim .field)] [.var 3]
#guard exprs (Circuit.forward witArg) == [[.add x y], [.const 1, .add x y]]
#guard agrees witArg [1, 2] [7] []

/-! ### `forwardOpt` keeps the result only when it is smaller -/

-- Without a pass to cash it in, `forward` alone changes no instruction count.
-- `forwardOpt` falls back to the input when nothing is gained.
private def nothing := mk 2 [.bind 2 "s" (.add x y)] [.mul (.var 2) (.var 2)]
#guard (Circuit.forwardOpt nothing).body.toList.length == 1
#guard exprs (Circuit.forwardOpt nothing) == exprs nothing

/-! ### A contract: the emitted ZKIR shrinks -/

ledger
  total : Cell Field

circuit split (a b : Field) : Field := do
  const d := a - b
  const e := d + b
  total.write (disclose (e * 2))
  total.read

private def size (c : Circuit) : Nat :=
  match Emit.circuit c with
  | .ok src => src.instructions.size
  | .error _ => 0

/-- The default pipeline, written out. -/
private def base (c : Circuit) : Circuit :=
  runPasses [Circuit.simplify, Circuit.bounds2, Circuit.simplify, Circuit.algebra] c

#guard size (base split.circuit) = 12
#guard size (Circuit.forwardOpt (base split.circuit)) = 9
#guard agrees (base split.circuit) [3, 4] [] [7]
#guard (observe (base split.circuit) [3, 4] [] [7]).isSome
#guard observe (base split.circuit) [3, 4] [] [7] ==
  observe (Circuit.forwardOpt (base split.circuit)) [3, 4] [] [7]

end Examples.OptForward
