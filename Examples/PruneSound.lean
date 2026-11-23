import Damp

/-! The shipped ZKIR rejects what the source rejects, at every level.

The pass theorems (`Pass.Sound`, `Pass.SoundFor`) compare `Circuit.run` before
and after a pass, and `Circuit.run` evaluates every binding, used or not. The
emitter drops unused bindings, but only those whose expression certainly has a
value (`Emit.pruneDeadBinds`), so the shipped ZKIR means exactly the circuit it
is emitted from (`Emit.pruned_run_eq`, `Emit.circuit_exact`), and a pass that
removes the last use of a binding that can fail no longer makes the shipped ZKIR
accept what the unoptimized one rejects (`shipped_preprocessFor`,
`Damp/Proofs/Shipped.lean`).

Before that change, each circuit below was accepted at some level with
`a = 1000` (the audit's finding F2, `test/audit/Prune.lean`); the checks here
are the same cases: at every level, the shipped ZKIR accepts exactly when the
`--no-opt` ZKIR does, and `--no-opt` rejects. `test/prune-sound.sh` runs the
same circuits through Midnight's own checker. -/
namespace Examples.PruneSound
open Damp Damp.IR Damp.Zkir

/-- Whether the ZKIR emitted for `c` accepts these inputs and private transcript
    (no ledger reads), with Damp's hash functions; `none` if it cannot be emitted. -/
def zkirAccepts (c : Circuit) (inputs priv : List Int) : Option Bool :=
  match Emit.circuit c with
  | .error _ => none
  | .ok src => some (src.run Crypto.prims (inputs.map Fr.ofInt) (priv.map Fr.ofInt) []).isSome

/-- A circuit with inputs `0..n-1`, a body ending in an empty ledger statement
    (so that it is proved), and outputs. -/
def mk (n : Nat) (body : List Stmt) (outputs : List Expr) : Circuit where
  name := "t"
  args := []
  inputs := (List.range n).map fun v => { name := s!"x{v}", var := v, range := none }
  body := (body ++ [Stmt.ledger (.const 1) [] []]).toArray
  result := .tuple []
  outputs := outputs

/-- `a < 2^8`, which fails for `a = 1000`. -/
def fails : Expr := .lt 8 (.var 0) (.const 0)

def levels : List OptLevel := [.none, .default, .full, .max]

/-- At every level the shipped ZKIR accepts exactly when the `--no-opt` one
    does, and `--no-opt` refuses. -/
def agrees (c : Circuit) (inputs : List Int) (priv : List Int := []) : Bool :=
  zkirAccepts c inputs priv == some false &&
    levels.all fun lvl => zkirAccepts (buildPassWith lvl false c) inputs priv == zkirAccepts c inputs priv

/-- 1. Default level, `Simplify`: `v * 0` becomes `0`. -/
def ex1 := mk 1 [.bind 1 "v" fails] [.mul (.var 1) (.const 0)]
/-- 2. Default level, `Simplify`: `v == v` becomes 1. -/
def ex2 := mk 1 [.bind 1 "v" fails] [.eq (.var 1) (.var 1)]
/-- 3. Default level, `Algebra`: `(x - v) + v` becomes `x`. -/
def ex3 := mk 1 [.bind 1 "v" fails] [.add (.add (.var 0) (.neg (.var 1))) (.var 1)]
/-- 4. `--O2`, `Asserts`: the body of the unused binding `t` counts as evaluated. -/
def ex4 := mk 1 [.bind 1 "t" fails, .bind 2 "u" (.mul fails (.const 0))] [.var 2]
/-- 5. `--O3`, `hashRanges`: a range check dropped because an unused binding hashes the value. -/
def ex5 : Circuit :=
  mk 0 [.witness (.const 1) "w" [] [(0, some (.bits 8))] (.prim (.uint 255)),
        .bind 1 "h" (.phash false [.bytes 1] [.var 0])] [.var 0]
/-- 6. Default level, `Bounds2`: `v <₈ 5` folds to 1, removing the last use of `v`. -/
def ex6 := mk 1 [.bind 1 "v" fails] [.lt 8 (.var 1) (.const 5)]
/-- 7. `--O2`, `forwardAllOpt`: `v` is substituted into a witness argument. -/
def ex7 := mk 1 [.bind 1 "v" fails, .witness (.const 1) "w" [.var 1] [(2, some .bool)] (.prim .bool)] [.var 2]
/-- 8. `--O2`, `mergeChecks`: the two asserts become `assert c`, removing the uses of `b`. -/
def c8 : Expr := .eq (.var 0) (.const 1000)
def ex8 := mk 1 [.bind 1 "b" fails, .bind 2 "n" (.select (.var 1) (.const 0) (.const 1)),
  .assert (.select (.var 1) c8 (.const 1)) "x", .assert (.select (.var 2) c8 (.const 1)) "y"] []

#guard agrees ex1 [1000]
#guard agrees ex2 [1000]
#guard agrees ex3 [1000]
#guard agrees ex4 [1000]
#guard agrees ex5 [] [1000]
#guard agrees ex6 [1000]
#guard agrees ex7 [1000] [1]
#guard agrees ex8 [1000]

-- An honest input is accepted everywhere (the circuits are not simply broken).
#guard levels.all fun lvl => zkirAccepts (buildPassWith lvl false ex1) [3] [] == some true
#guard levels.all fun lvl => zkirAccepts (buildPassWith lvl false ex5) [] [200] == some true

/-! ### The surface repro

`u := Field.unsafeToUint w 255` is unchecked, `u <. 10` fails for `u = 1000`
(the comparison's width is 8 bits), and the result does not depend on it. -/

ledger
  c : Cell Field

witness w : Field

circuit f : Field := do
  const u := Field.unsafeToUint (← w) 255
  const v := u <. 10
  c.write 1
  return disclose (if v then 0 else 0)

contract prune_sound

#guard agrees f.circuit [] [1000]
#guard levels.all fun lvl => zkirAccepts (buildPassWith lvl false f.circuit) [] [7] == some true

/-! ### The executor agrees

`Exec.run` evaluates every binding, so with `w = 1000` it refuses the call at
every level, and the shipped ZKIR now refuses the same private transcript; with
`w = 7` both accept. (Before, the executor refused while the ZKIR accepted, at
every level, `--no-opt` included.) -/

/-- The executor with `w` answering `x` and a ledger that runs anything. -/
def execAccepts (c : Circuit) (x : Nat) : Bool :=
  let O : Exec.Oracles Unit Unit :=
    ⟨Exec.liftWitness fun _ _ s => some ([Fr.ofNat x], s), fun _ l => some ([], l)⟩
  (Exec.run Crypto.prims O c [] () ()).isSome

#guard levels.all fun lvl =>
  let s := buildPassWith lvl false f.circuit
  !execAccepts s 1000 && zkirAccepts s [] [1000] == some false &&
    execAccepts s 7 && zkirAccepts s [] [7] == some true

/-! ### The audit's `--O3` case as a contract

`hashRanges` drops the range check of `x`, a `Uint<0..256>` witness value, because
a later persistent hash reads it in one byte; that hash is in a binding nothing
uses. The hash can fail, so it is kept, and the forged `x = 1000` is refused at
the hash (test/prune-sound.sh runs it through the executor and Midnight's
checker at every level). -/
namespace Hash
ledger
  c : Cell Field
witness w : Uint 255
circuit f : Unit := do
  const x ← w
  const _h := persistentHash #v[x]
  c.write (disclose x.toField)
contract prune_hash
end Hash

#guard levels.all fun lvl =>
  zkirAccepts (buildPassWith lvl false Hash.f.circuit) [] [1000] == some false &&
    zkirAccepts (buildPassWith lvl false Hash.f.circuit) [] [200] == some true

/-! ### What pruning still drops

A dead binding that cannot fail (`Bounds.totalB`): arithmetic, transient
hashes, a comparison of range-checked values, a `select` on a condition known
to be 0 or 1, or on one a later statement needs to be 0 or 1. -/

def dropped := mk 1
  [.constrain (.var 0) (.bits 8),
   .bind 1 "a" (.add (.var 0) (.const 1)),
   .bind 2 "h" (.hash [.var 0]),
   .bind 3 "l" (.lt 8 (.var 0) (.const 5)),
   .witness (.const 1) "g" [] [(4, none)] (.prim .field),
   .bind 5 "n" (.select (.var 4) (.const 0) (.const 1)),
   .ledger (.var 4) [] [.addi (.var 0)]]
  []
#guard (Emit.pruned dropped).body.size == 4

-- Kept: a comparison of an unchecked value, a persistent hash, a `select` on a
-- condition nothing makes 0 or 1.
def kept := mk 2
  [.bind 2 "l" fails,
   .bind 3 "p" (.phash false [.bytes 1] [.var 0]),
   .bind 4 "n" (.select (.var 1) (.const 0) (.const 1))]
  []
#guard (Emit.pruned kept).body.size == 4

-- But a comparison is dropped when a statement kept after it needs its operand
-- to be 0 or 1: if it is not, the circuit fails there anyway.
def keptLater := mk 1
  [.bind 1 "l" fails,
   .bind 2 "n" (.select (.var 0) (.const 0) (.const 1))]
  []
#guard (Emit.pruned keptLater).body.size == 2

/-- A chain of 32 dead bindings, each the sum of the last: the analysis is one
    forward and one backward pass, linear in the statements. -/
def chain32 := mk 1
  ((List.range 32).map fun i => .bind (i + 1) "c" (.add (.var i) (.var i))) []
#guard (Emit.pruned chain32).body.size == 1

end Examples.PruneSound
