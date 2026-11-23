/-
A frame analysis of Impact programs, for the ledger passes.

`frameKeeps π ops` decides, by abstract interpretation of the program's stack,
that a successful run of `ops` (any operand values) leaves the part of the
contract state at the constant path `π` (a list of keys, as the VM's aligned
values) exactly as it was: `svWalk state' π = svWalk state π`
(`Damp/Proofs/Ledger/OptFrame.lean`, `frame_ledgerOracle`).

Each stack entry gets a tag (`FTag`):

* `pre d` (`d < |π|`): a container whose walk along the rest of `π`, from
  position `d`, reaches what the initial contract state reaches along all of
  `π`. The contract state itself starts as `pre 0`.
* `key k`: a cell holding exactly `k` (a constant operand).
* `other`: nothing known.

Reading anything is always allowed (`idx`, `size`, `member`, ...: the result is
`other`, or `pre (d+1)` when a `pre d` container is indexed by the next key of
`π`). Writing is the only danger: an `ins` or `rem` into a `pre d` container
must use a constant key whose atoms differ from `π[d]`'s (so the protected
entry is untouched), or put back, at `π[d]` itself, a `pre (d+1)` value (a
nested container modified elsewhere). Any other write into a `pre` container
makes the check fail. At the end, the top of the stack (the new contract
state) must be `pre 0`. Both continuations of every `branch` are checked.

A write to another top-level field (a cell write, a counter increment, a map
insert, a Merkle tree insertion, a list push, ...), a write of the effects, and
every read pass the check for `π` = a field it does not write; so do writes
inside a nested map at a constant key other than `π`'s second.
-/
import Damp.IR.Basic
import Damp.IR.Impact
import Damp.Ledger.Vm

namespace Damp.IR
open Damp.Impact Damp.Ledger

/-- What the frame analysis knows about a stack entry (see the file header). -/
inductive FTag where
  | pre (d : Nat)
  | key (k : AV)
  | other
  deriving DecidableEq, Inhabited

/-- The aligned value of a constant operand, as the VM gets it: `none` unless
    every value is a constant and the result fits its alignment. -/
def constAV (k : Aligned Expr) : Option AV := do
  let vs ← k.vals.mapM fun | .const c => some (Fr.ofInt c) | _ => none
  AV.ofAligned ⟨k.align, vs⟩

def keyTag (k : Aligned Expr) : FTag :=
  match constAV k with
  | some kv => .key kv
  | none => .other

/-- One step of `idx` from an entry tagged `curr` along a key tagged `k`. -/
def fwalk (π : List AV) (curr k : FTag) : FTag :=
  match curr, k with
  | .pre d, .key kv => if π[d]? = some kv ∧ d + 1 < π.length then .pre (d + 1) else .other
  | _, _ => .other

/-- `idx` along keys tagged `ks` from `curr`, the stack below being `ts`
    (pushing the path when `push`). -/
def fidx (π : List AV) (push : Bool) : List FTag → FTag → List FTag → List FTag
  | [], curr, ts => curr :: ts
  | k :: ks, curr, ts => fidx π push ks (fwalk π curr k) (if push then k :: curr :: ts else ts)

/-- Writing into a container tagged `cont` at a key tagged `key` a value tagged
    `curr`: the tag of the result, `none` if that may change the protected part. -/
def fput (π : List AV) (cont key curr : FTag) : Option FTag :=
  match cont with
  | .pre d =>
      match key, π[d]? with
      | .key kv, some j =>
          if kv = j then (if curr = .pre (d + 1) ∧ d + 1 < π.length then some (.pre d) else none)
          else if kv.atoms ≠ j.atoms then some (.pre d) else none
      | _, _ => none
  | _ => some .other

/-- The loop of `ins`. -/
def fins (π : List AV) : Nat → FTag → List FTag → Option (FTag × List FTag)
  | 0, curr, ts => some (curr, ts)
  | n + 1, curr, key :: cont :: ts => do
      let c ← fput π cont key curr
      fins π n c ts
  | _ + 1, _, _ => none

/-- `rem` of a key tagged `key` from a container tagged `cont`. -/
def frem (π : List AV) (cont key : FTag) : Option FTag :=
  match cont with
  | .pre d =>
      match key, π[d]? with
      | .key kv, some j => if kv.atoms ≠ j.atoms then some (.pre d) else none
      | _, _ => none
  | _ => some .other

/-- Pop `n` entries and push an `other`. -/
def fpopPush (n : Nat) (ts : List FTag) : Option (List FTag) :=
  if n ≤ ts.length then some (.other :: ts.drop n) else none

/-- One instruction other than `branch` and `jmp`. -/
def fstep (π : List AV) : Op Expr → List FTag → Option (List FTag)
  | .dup n, ts => (ts[n]?).map (· :: ts)
  | .swap n, ts => do
      let top ← ts[0]?
      let oth ← ts[n + 1]?
      pure ((ts.set 0 oth).set (n + 1) top)
  | .idx _ push path, curr :: ts => some (fidx π push (path.map keyTag) curr ts)
  | .idxStack pre, sk :: curr :: ts => some (fidx π false (pre.map keyTag ++ [sk]) curr ts)
  | .ins _ n, curr :: ts => (fins π n curr ts).map fun (c, ts) => c :: ts
  | .rem _, key :: cont :: ts => (frem π cont key).map (· :: ts)
  | .push _ v, ts => some (keyTag v :: ts)
  | .pushNull _, ts | .pushState _ _, ts => some (.other :: ts)
  | .popeq .., _ :: ts | .pop, _ :: ts | .log, _ :: ts => some ts
  | .lt, ts | .eq, ts | .and, ts | .or, ts | .add, ts | .sub, ts | .member, ts
  | .concat _, ts | .concatCached _, ts => fpopPush 2 ts
  | .type, ts | .size, ts | .neg, ts | .root, ts | .addi _, ts | .subi _, ts => fpopPush 1 ts
  | .ckpt, ts => some ts
  | _, _ => none

/-- The whole program, both continuations of each `branch`; `fuel` bounds the
    number of instructions on any path. At the end the top must be `pre 0`. -/
def fcheck (π : List AV) : Nat → List (Op Expr) → List FTag → Bool
  | 0, _, _ => false
  | _ + 1, [], ts => ts.head? == some (.pre 0)
  | fuel + 1, op :: rest, ts =>
      match op with
      | .branch k =>
          match ts with
          | _ :: ts' => fcheck π fuel rest ts' && fcheck π fuel (rest.drop k) ts'
          | [] => false
      | .jmp k => fcheck π fuel (rest.drop k) ts
      | _ =>
          match fstep π op ts with
          | some ts' => fcheck π fuel rest ts'
          | none => false

/-- The largest program the analysis looks at, and the most branches in it
    (each `branch` doubles the paths checked). -/
def frameMaxOps : Nat := 64
def frameMaxBranches : Nat := 6

def Op.isBranch : Op Expr → Bool
  | .branch _ => true
  | _ => false

/-- A successful run of `ops` leaves the contract state's part at `π` as it was. -/
def frameKeeps (π : List AV) (ops : List (Op Expr)) : Bool :=
  !π.isEmpty && ops.length ≤ frameMaxOps && (ops.filter Op.isBranch).length ≤ frameMaxBranches &&
    fcheck π (ops.length + 1) ops [.pre 0, .other, .other]

/-- The longest prefix of constant keys of a path, at most `n` of them, as the VM gets them. -/
def constPrefix : Nat → List (Aligned Expr) → List AV
  | 0, _ => []
  | _, [] => []
  | n + 1, k :: ks =>
      match constAV k with
      | some kv => kv :: constPrefix n ks
      | none => []

/-- The witnesses that are barriers for every ledger pass. The model's witnesses do not touch the
    ledger (`Exec.Oracles.witness` sees only the private state), but in the runtime the built-in
    `createZswapOutput` inserts its coin's commitment into the call context's `com_indices`
    (`insertCommitment`, compact-runtime `zswap.js`), which a later coin-storing write
    (`writeCoin`, `insertCoin`, ...) reads back; and a cross-contract call (`call:…`) runs another
    contract (its isolation from the caller's state is the assumption `CallIsolated`,
    Damp/Proofs/Ledger/Calls.lean). The other built-ins, `createZswapInput` and `ownPublicKey`,
    work only on the call's Zswap local state, which no ledger statement reads. No ledger pass
    moves a ledger statement above one of these, merges two statements across one, or keeps a fact
    about the call context's `com_indices` across one. -/
def ctxWitness (name : String) : Bool :=
  name == "createZswapOutput" || name.startsWith "call:"

end Damp.IR
