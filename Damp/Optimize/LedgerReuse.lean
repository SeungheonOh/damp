/-
Ledger-level reuse: drop a ledger read whose answer is already known.

Two rewrites, one forward scan:

* **Repeated reads.** A *plain read* `dup n; idx ci false path; popeq c a`
  (`n = 0` the contract state, `n = 2` the call context: `Cell.read`,
  `Counter.read`, the kernel's context reads) under guard `g`, when an earlier
  plain read of the same path, alignment and guard is still valid: its read
  variables are bound to the earlier ones.
* **Read after write.** A plain read of the contract state along `[k]` after a
  *cell write* `push false k; push true v; ins false 1` under the same guard,
  for a single-limb alignment `v.align` equal to the read's: its read
  variables are bound to the written operands (`select g e 0` unless `g` is the
  constant 1; operands of at most `maxExprSize` nodes, so the circuit grows by
  a bounded amount per rewritten read).

What is known is a list of `LFact`s. A fact is forgotten when a variable it
mentions is rebound; a fact about the contract state is forgotten at every
ledger statement that is not a plain read (it may write); a fact about the
call context survives every ledger statement, since no request changes the
call context. A witness call (cross-contract calls included) cannot change the
ledger state in the executor's model, so it forgets only the facts mentioning
its results.

This is NOT a `Pass.Sound` pass: the rewritten circuit sends fewer ledger
statements, so its public transcript differs. It is `Pass.SoundLedger`
(`Damp/Proofs/Optimize/LedgerReuse.lean`): against the modelled ledger it
keeps outputs, private transcript, private state and ledger state.
-/
import Damp.Optimize.Pass
import Damp.IR.LedgerCheck

namespace Damp.IR
open Damp.Impact
open Damp.Zkir (AlignAtom)

/-- A ledger read whose answer is known: under `guard`, the plain read of
    initial value `n` along `path` under alignment `align` answers `vals`
    (and, with the guard off, `vals` are zeros). -/
structure LFact where
  guard : Expr
  n : Nat
  path : List (Aligned Expr)
  align : List AlignAtom
  vals : List Expr
  deriving Inhabited

mutual
/-- The number of nodes of an expression. -/
def Expr.size : Expr → Nat
  | .var _ | .const _ | .invalid _ => 1
  | .add a b | .mul a b | .lt _ a b | .eq a b => a.size + b.size + 1
  | .neg a | .disclose a | .divmod _ _ a => a.size + 1
  | .select c a b => c.size + a.size + b.size + 1
  | .hash xs | .phash _ _ xs => Expr.sizeList xs + 1
def Expr.sizeList : List Expr → Nat
  | [] => 0
  | x :: xs => x.size + Expr.sizeList xs
end

/-- The largest written operand copied into a later read's place. -/
def maxExprSize : Nat := 16

/-- How many facts are kept (older ones are dropped, which is always sound). -/
def maxFacts : Nat := 32

def alignedSame (x y : Aligned Expr) : Bool := x.align == y.align && x.vals == y.vals

def pathSame : List (Aligned Expr) → List (Aligned Expr) → Bool
  | [], [] => true
  | x :: xs, y :: ys => alignedSame x y && pathSame xs ys
  | _, _ => false

def pathVars (path : List (Aligned Expr)) : List Var := path.flatMap fun k => Expr.varsList k.vals

def LFact.vars (f : LFact) : List Var := f.guard.vars ++ pathVars f.path ++ Expr.varsList f.vals

/-- Forget the facts that mention any of `vs`. -/
def forgetVars (vs : List Var) (fs : List LFact) : List LFact :=
  fs.filter fun f => !(f.vars.any vs.contains)

/-- Every atom of the alignment is one field element (no byte string over 31 bytes). -/
def singleLimb (a : List AlignAtom) : Bool :=
  a.all fun | .bytes n => n ≤ 31 | _ => true

/-- A plain read `dup n; idx ci false path; popeq c a (rs as variables)`,
    `n ≤ 2`, reading into distinct variables that the path does not mention,
    the `idx` cached only on the effects or the call context (`n ≥ 1`, whose
    read cache is full): `(n, path, a)`. -/
def plainRead? (rs : List Var) : List (Op Expr) → Option (Nat × List (Aligned Expr) × List AlignAtom)
  | [.dup n, .idx ci false path, .popeq _ a res] =>
      if n ≤ 2 && (!ci || 1 ≤ n) && !rs.isEmpty && res == rs.map Expr.var && decide rs.Nodup &&
          !((pathVars path).any rs.contains)
      then some (n, path, a) else none
  | _ => none

/-- A cell write `push false k; push true v; ins false 1`: `(k, v)`. -/
def cellWrite? : List (Op Expr) → Option (Aligned Expr × Aligned Expr)
  | [.push false k, .push true v, .ins false 1] => some (k, v)
  | _ => none

/-- The fact a cell write establishes, if the pass may use it. -/
def writeFact (g : Expr) (k v : Aligned Expr) : Option LFact :=
  if singleLimb v.align && v.vals.length == v.align.length && v.vals.all (fun e => e.size ≤ maxExprSize) then
    some { guard := g, n := 0, path := [k], align := v.align,
           vals := if g == .const 1 then v.vals else v.vals.map fun e => .select g e (.const 0) }
  else none

/-- A fact that answers the plain read `(n, path, a)` under `g` into `rs`. -/
def findFact (g : Expr) (n : Nat) (path : List (Aligned Expr)) (a : List AlignAtom) (rs : List Var) :
    List LFact → Option LFact
  | [] => none
  | f :: fs =>
      if f.guard == g && f.n == n && pathSame f.path path && f.align == a && f.vals.length == rs.length &&
          !((Expr.varsList f.vals).any rs.contains)
      then some f else findFact g n path a rs fs

/-- Bind each read variable to its known value. -/
def bindReads (rs : List Var) (vals : List Expr) : List Stmt :=
  (rs.zip vals).map fun (r, e) => .bind r "ledger" e

def addFact (f : LFact) (fs : List LFact) : List LFact := (f :: fs).take maxFacts

/-- The facts kept after a plain read that no fact answered. -/
def missFacts (g : Expr) (rs : List Var) (n : Nat) (path : List (Aligned Expr)) (a : List AlignAtom)
    (fs : List LFact) : List LFact :=
  if g.vars.any rs.contains then forgetVars rs fs
  else addFact { guard := g, n, path, align := a, vals := rs.map Expr.var } (forgetVars rs fs)

/-- The facts kept after any other ledger statement. -/
def otherFacts (g : Expr) (rs : List Var) (ops : List (Op Expr)) (fs : List LFact) : List LFact :=
  let fs := forgetVars rs (fs.filter (·.n == 2))
  match rs, cellWrite? ops with
  | [], some (k, v) => match writeFact g k v with
    | some f => addFact f fs
    | none => fs
  | _, _ => fs

/-- The scan. -/
def ledgerReuseGo : List LFact → List Stmt → List Stmt
  | _, [] => []
  | fs, s :: rest =>
      match s with
      | .bind v _ _ => s :: ledgerReuseGo (forgetVars [v] fs) rest
      | .assert .. | .constrain .. => s :: ledgerReuseGo fs rest
      | .witness _ _ _ outs _ => s :: ledgerReuseGo (forgetVars (outs.map Prod.fst) fs) rest
      | .ledger g rs ops =>
          match plainRead? rs ops with
          | some (n, path, a) =>
              match findFact g n path a rs fs with
              | some f => bindReads rs f.vals ++ ledgerReuseGo (forgetVars rs fs) rest
              | none => s :: ledgerReuseGo (missFacts g rs n path a fs) rest
          | none => s :: ledgerReuseGo (otherFacts g rs ops fs) rest

/-- Drop ledger reads whose answer is already known (see the file header). -/
def Circuit.ledgerReuse (c : Circuit) : Circuit :=
  { c with body := (ledgerReuseGo [] c.body.toList).toArray }

end Damp.IR
