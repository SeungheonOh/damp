import Damp
open Damp Damp.IR Damp.Zkir

/-! Audit (docs/audit.md, finding F2): what the SHIPPED ZKIR accepts, compared with the ZKIR the
same circuit gets with no optimization (`Emit.circuit c`, which is `--no-opt`).

The pass theorems (`Pass.Sound`, `Pass.SoundFor`) compare `Circuit.run` before and after; `Circuit.run`
evaluates every binding, used or not. The emitter drops unused bindings (`Emit.pruneDeadBinds`), so
the shipped ZKIR means `Emit.pruned (pass c)` (`compile_exact`), and nothing relates that to
`Emit.pruned c`. A pass that removes the last use of a binding that can fail, or that learns
"this has a value" from a binding the emitter later drops, makes the shipped ZKIR accept inputs
the unoptimized ZKIR (and the source semantics) rejects.

Each `#guard` below states the property that must hold ("the optimized ZKIR rejects what the
unoptimized ZKIR rejects") on one input. All of them failed at `ccd590e`; F2 is fixed (the emitter
prunes only bindings that cannot fail, `Emit.pruned_run_eq`, `Emit.circuit_exact`) and they are now
regressions that must pass: `lake env lean` on this file exits non-zero if one fails. The first
block checks that each case is not vacuous (`--no-opt` still refuses the input). Run by
test/audit/run.sh. -/

def zkirAccepts (c : Circuit) (inputs priv : List Int) : Option Bool :=
  match Emit.circuit c with
  | .error _ => none
  | .ok src => some (src.run Crypto.prims (inputs.map Fr.ofInt) (priv.map Fr.ofInt) []).isSome

def mk (n : Nat) (body : List Stmt) (outputs : List Expr) : Circuit where
  name := "t"
  args := []
  inputs := (List.range n).map fun v => { name := s!"x{v}", var := v, range := none }
  body := (body ++ [Stmt.ledger (.const 1) [] []]).toArray
  result := .tuple []
  outputs := outputs

/-- `a < 2^8` fails for `a = 1000`. -/
def fails : Expr := .lt 8 (.var 0) (.const 0)

/-- What each level ships, and whether it accepts `inputs` where `--no-opt` refuses. -/
def widened (lvl : OptLevel) (c : Circuit) (inputs : List Int) (priv : List Int := []) : Bool :=
  zkirAccepts c inputs priv == some false && zkirAccepts (buildPassWith lvl false c) inputs priv == some true

/-- 1. Default level, `Circuit.simplify`: `v * 0` becomes `0` (a variable cannot fail), which
    removes the last use of `v := a <₈ 0`; the binding is then pruned. -/
def ex1 := mk 1 [.bind 1 "v" fails] [.mul (.var 1) (.const 0)]
/-- 2. Default level: `v == v` becomes 1. -/
def ex2 := mk 1 [.bind 1 "v" fails] [.eq (.var 1) (.var 1)]
/-- 3. Default level, `Algebra`: `(x - v) + v` becomes `x`. -/
def ex3 := mk 1 [.bind 1 "v" fails] [.add (.add (.var 0) (.neg (.var 1))) (.var 1)]
/-- 4. `--O2`, `Asserts`: the body of the unused binding `t` counts as evaluated, so `cmp * 0`
    elsewhere becomes 0. -/
def ex4 := mk 1 [.bind 1 "t" fails, .bind 2 "u" (.mul fails (.const 0))] [.var 2]
/-- 5. `--O3`, `hashRanges`: a range check dropped because an unused binding hashes the value. -/
def ex5 : Circuit :=
  { mk 0 [.witness (.const 1) "w" [] [(0, some (.bits 8))] (.prim (.uint 255)),
          .bind 1 "h" (.phash false [.bytes 1] [.var 0])] [.var 0] with }

/-- 6. Default level, `Bounds2`: `v := a <₈ 0` has the bound 1, so `v <₈ 5` folds to 1, removing
    the last use of `v`. -/
def ex6 := mk 1 [.bind 1 "v" fails] [.lt 8 (.var 1) (.const 5)]
/-- 7. `--O2`, `forwardAllOpt` (InlineAll): `v` is used only as a witness argument; it is
    substituted into the argument, which the emitter does not compile, and the binding pruned. -/
def ex7 := mk 1 [.bind 1 "v" fails, .witness (.const 1) "w" [.var 1] [(2, some .bool)] (.prim .bool)] [.var 2]
/-- 8. `--O2`, `mergeChecks`: `assert (select b c 1)` and `assert (select !b c 1)` become
    `assert c`, removing the last uses of `b := a <₈ 0`. -/
def c8 : Expr := .eq (.var 0) (.const 1000)
def ex8 := mk 1 [.bind 1 "b" fails, .bind 2 "n" (.select (.var 1) (.const 0) (.const 1)),
  .assert (.select (.var 1) c8 (.const 1)) "x", .assert (.select (.var 2) c8 (.const 1)) "y"] []

#eval [("ex6 default", widened .default ex6 [1000]), ("ex7 --O2", widened .full ex7 [1000] [1]),
       ("ex7 default", widened .default ex7 [1000] [1]), ("ex8 --O2", widened .full ex8 [1000]),
       ("ex8 default", widened .default ex8 [1000])]

#eval [("ex1 default", widened .default ex1 [1000]), ("ex2 default", widened .default ex2 [1000]),
       ("ex3 default", widened .default ex3 [1000]), ("ex4 --O2", widened .full ex4 [1000]),
       ("ex4 default", widened .default ex4 [1000]), ("ex5 --O3", widened .max ex5 [] [1000]),
       ("ex5 --O2", widened .full ex5 [] [1000])]

-- Not vacuous: the unoptimized ZKIR refuses each input.
#guard zkirAccepts ex1 [1000] [] == some false
#guard zkirAccepts ex2 [1000] [] == some false
#guard zkirAccepts ex3 [1000] [] == some false
#guard zkirAccepts ex4 [1000] [] == some false
#guard zkirAccepts ex5 [] [1000] == some false
#guard zkirAccepts ex6 [1000] [] == some false
#guard zkirAccepts ex7 [1000] [1] == some false
#guard zkirAccepts ex8 [1000] [] == some false
-- The property that must hold (regression for F2; failed at ccd590e).
#guard !widened .default ex1 [1000]
#guard !widened .default ex2 [1000]
#guard !widened .default ex3 [1000]
#guard !widened .full ex4 [1000]
#guard !widened .max ex5 [] [1000]
#guard !widened .default ex6 [1000]
#guard !widened .full ex7 [1000] [1]
#guard !widened .full ex8 [1000]
