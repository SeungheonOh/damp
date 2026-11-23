/-
Ledger-level merging: run two ledger statements as one Impact program.

Every ledger statement is one request to the ledger (`QueryContext::query`),
and every request pays a fixed price: the contract state is written back and
the effects re-encoded, whatever the program did. `Circuit.ledgerMerge` puts
the instructions of a ledger statement `L₂` at the end of an earlier one `L₁`
(`.ledger g (rs₁ ++ rs₂) (ops₁ ++ ops₂)`), when

* both have the same guard `g` (the same expression), and `g` does not mention
  what `L₁` reads;
* `L₂`'s operands do not mention what `L₁` reads (they are evaluated before
  either program runs), and `L₁`'s do not mention what `L₂` reads (they are
  the public inputs, evaluated after);
* each statement reads as many variables as its `popeq`s give field elements
  (`widthOk`);
* only statements that are not ledger statements (at most `mergeWindow`) lie
  between them, and `L₂` can move above them: it does not read what they
  bind, they neither read nor bind what it reads, and none is a witness that
  changes the query context in the runtime (`ctxWitness`: `createZswapOutput`
  inserts its commitment into the call context) (`lcommutes`);
* the two programs pass `mergeable`, below.

One request is not two requests in a row. Between two requests the runtime
checks the first program's final stack (exactly three values, the state
strong), decodes and re-encodes the effects, and starts the second program
with a fresh read cache in which only the call context and the effects are
cached. Inside one request none of this happens. `mergeable ops₁ ops₂` is an
abstract interpretation of the two programs (`mcheck`, all paths through
their branches) that makes the difference invisible:

* `ops₁` ends, on every path, with exactly three stack entries: a strong one
  on top, below it the effects in the form the runtime re-encodes them to
  (tag `dec`: as they were at the start, or changed only by writes of entries
  already in their slot's form, `insv`), weak and fully cached, and at the
  bottom the call context exactly as it was, weak and fully cached
  (`mboundary`); every jump of `ops₁` stays inside `ops₁`;
* every cached instruction of `ops₂` (`idx`, `ins`, `rem` with the cached
  flag, `idxStack`) hits the cache in any run from a state whose effects and
  call context are fully cached, whatever the contract state's cache: it
  works on a fully cached entry (the effects, the context, a pushed value or
  something read from those), or on a container that an earlier `idx`
  pushing its path visited at the same constant key.

Then `ops₂` behaves after `ops₁` exactly as it does alone after the first
request (`Damp/Proofs/Ledger/OptMerge.lean`, `ledgerOracle_merge`). Each
stack entry gets a tag (`MTag`): what its value is (`orig i`: initial value
`i`, `key k`: a cell holding the constant `k`, `cell al`: a cell of alignment
`al`, `nul`, `dec`: effects in decoded form, `dmap i`: the decoded map of
slot `i`), its strength if known, whether its cache key is fully cached, and
the constant keys at which it was visited. The effects stay `dec` through the
claims of slots 0 to 2 (a 32-byte hash mapped to null) and the mints of slots
4 and 5 (a 32-byte hash mapped to a `u64` cell); a `TokenType` key (slots 6 to
8) is in its slot's form only for some values, and is not followed.

Not a `Pass.Sound` pass: the circuit sends fewer requests, so its public
transcript (grouping of instructions into requests) and gas differ. It is
`Pass.SoundLedger` (`Damp/Proofs/Optimize/LedgerMerge.lean`).
-/
import Damp.Optimize.LedgerFrame
import Damp.Ledger.Query

namespace Damp.IR
open Damp.Impact Damp.Ledger

/-- What the merge analysis knows of a stack entry's value. -/
inductive MVal where
  /-- Initial stack value `i` (0 the call context, 2 the contract state). -/
  | orig (i : Nat)
  /-- A cell holding exactly this value. -/
  | key (k : AV)
  /-- A cell holding a valid aligned value of this alignment (a pushed operand). -/
  | cell (al : List Zkir.AlignAtom)
  /-- Null. -/
  | nul
  /-- Effects in the form the runtime re-encodes them to (`decodeEffects v = some v`). -/
  | dec
  /-- The map of slot `i` of such effects, in the same form (`effectMap i m = some m`). -/
  | dmap (i : Nat)
  | other
  deriving DecidableEq, Inhabited

/-- What the merge analysis knows of a stack entry: its value, its strength
    (if known), whether its cache key is fully cached, and keys `k` such that
    the cache holds the entry's key extended by `k`. -/
structure MTag where
  v : MVal
  strong : Option Bool
  fc : Bool
  vis : List AV
  deriving DecidableEq, Inhabited

/-- A freshly computed value: strong, cache key `None`. -/
def MTag.new : MTag := ⟨.other, some true, true, []⟩

def mkeyVal (k : Aligned Expr) : MVal :=
  match constAV k with
  | some kv => .key kv
  | none => .cell k.align

/-! The effects' decoded form through the instructions that write them (`Kernel.claimZswapNullifier`
and the other claims of slots 0 to 2 insert `hash ↦ null`, `mintShielded`/`mintUnshielded` add a
`u64` amount at a hash in slots 4 and 5: `Damp/Lang/Ledger.lean`). An entry written into a decoded
slot map stays decoded when its key and value are already in the slot's own form. -/

/-- A key in slot `i`'s form: a 32-byte hash for slots 0 to 2, 4 and 5 (or a constant that is). -/
def effKeyOk (i : Nat) : MVal → Bool
  | .key kv => effectKey i kv == some kv
  | .cell al => (i ≤ 2 || i == 4 || i == 5) && al == [.bytes 32]
  | _ => false

/-- A value in slot `i`'s form: null for the sets (slots 0 to 3), a `u64` cell for the mints (4, 5). -/
def effValOk (i : Nat) : MVal → Bool
  | .nul => i ≤ 3
  | .key kv => (i == 4 || i == 5) && kv.align == [.bytes 8] && kv.atoms.length == 1 && kv.toU64.isSome
  | .cell al => (i == 4 || i == 5) && al == [.bytes 8]
  | _ => false

/-- The value `idx` finds at key `key` of `curr`. -/
def idxv (curr key : MVal) : MVal :=
  match curr, key with
  | .dec, .key kv => match kv.toU8 with
    | some i => .dmap i
    | none => .other
  | _, _ => .other

/-- The value `ins` builds: `curr` inserted at `key` into `cont`. -/
def insv (cont key curr : MVal) : MVal :=
  match cont, key, curr with
  | .dmap i, k, v => if effKeyOk i k && effValOk i v then .dmap i else .other
  | .dec, .key kv, .dmap i => if kv.toU8 == some i then .dec else .other
  | _, _, _ => .other

/-- A literal key of an `idx` path: a weak cell, cache key `None`. -/
def litTag (k : Aligned Expr) : MTag := ⟨mkeyVal k, some false, true, []⟩

/-- The strength of `a && b`. -/
def sand : Option Bool → Option Bool → Option Bool
  | some false, _ => some false
  | _, some false => some false
  | some true, some true => some true
  | _, _ => none

/-- A cached instruction working at key `key` of container `cont` hits. -/
def mhit (cont key : MTag) : Bool :=
  cont.fc || (match key.v with
    | .key kv => cont.vis.contains kv
    | _ => false)

def addVis (k : MVal) (vis : List AV) : List AV :=
  match k with
  | .key kv => kv :: vis
  | _ => vis

/-- The walk of `idx` along keys tagged `ks` from `curr`, the stack below being
    `ts`; with `check`, a cached step must hit. -/
def midx (check cached push : Bool) : List MTag → MTag → List MTag → Option (List MTag)
  | [], curr, ts => some (curr :: ts)
  | k :: ks, curr, ts =>
      if check && cached && !mhit curr k then none
      else
        midx check cached push ks ⟨idxv curr.v k.v, curr.strong, curr.fc, []⟩
          (if push then { k with fc := true, vis := [] } :: { curr with vis := addVis k.v curr.vis } :: ts else ts)

/-- The loop of `ins`: the strength and full caching of the result. -/
def mins (check cached : Bool) : Nat → MTag → List MTag → Option (MTag × List MTag)
  | 0, curr, ts => some (curr, ts)
  | n + 1, curr, key :: cont :: ts =>
      if check && cached && !mhit cont key then none
      else mins check cached n ⟨insv cont.v key.v curr.v, sand curr.strong cont.strong, curr.fc && cont.fc, []⟩ ts
  | _ + 1, _, _ => none

/-- Pop `n` entries and push a fresh value. -/
def mpopPush (n : Nat) (ts : List MTag) : Option (List MTag) :=
  if n ≤ ts.length then some (MTag.new :: ts.drop n) else none

/-- One instruction other than `branch` and `jmp`. -/
def mstep (check : Bool) : Op Expr → List MTag → Option (List MTag)
  | .dup n, ts => (ts[n]?).map (· :: ts)
  | .swap n, ts => do
      let top ← ts[0]?
      let oth ← ts[n + 1]?
      pure ((ts.set 0 oth).set (n + 1) top)
  | .idx c push path, curr :: ts => midx check c push (path.map litTag) curr ts
  | .idxStack pre, sk :: curr :: ts => midx check true false (pre.map litTag ++ [sk]) curr ts
  | .ins c n, curr :: ts => (mins check c n curr ts).map fun r => ({ r.1 with vis := [] } :: r.2)
  | .rem c, key :: cont :: ts =>
      if check && c && !mhit cont key then none else some ({ cont with v := .other } :: ts)
  | .push st v, ts => some (⟨mkeyVal v, some st, true, []⟩ :: ts)
  | .pushNull st, ts => some (⟨.nul, some st, true, []⟩ :: ts)
  | .pushState st _, ts => some (⟨.other, some st, true, []⟩ :: ts)
  | .popeq .., _ :: ts | .pop, _ :: ts | .log, _ :: ts => some ts
  | .add, ts => if 2 ≤ ts.length then some (⟨.cell [.bytes 8], some true, true, []⟩ :: ts.drop 2) else none
  | .lt, ts | .eq, ts | .and, ts | .or, ts | .sub, ts | .member, ts
  | .concat _, ts | .concatCached _, ts => mpopPush 2 ts
  | .type, ts | .size, ts | .neg, ts | .root, ts | .addi _, ts | .subi _, ts => mpopPush 1 ts
  | .ckpt, ts => some ts
  | _, _ => none

/-- The whole program, both continuations of each `branch`; every jump stays
    inside the program; `fin` must hold at every end. -/
def mcheck (check : Bool) (fin : List MTag → Bool) : Nat → List (Op Expr) → List MTag → Bool
  | 0, _, _ => false
  | _ + 1, [], ts => fin ts
  | fuel + 1, op :: rest, ts =>
      match op with
      | .branch k =>
          match ts with
          | _ :: ts' => k ≤ rest.length && mcheck check fin fuel rest ts' && mcheck check fin fuel (rest.drop k) ts'
          | [] => false
      | .jmp k => k ≤ rest.length && mcheck check fin fuel (rest.drop k) ts
      | _ =>
          match mstep check op ts with
          | some ts' => mcheck check fin fuel rest ts'
          | none => false

/-- The stack a request starts with (top first): the contract state, strong;
    the effects and the call context, weak and fully cached. -/
def minit : List MTag :=
  [⟨.orig 2, some true, false, []⟩, ⟨.dec, some false, true, []⟩, ⟨.orig 0, some false, true, []⟩]

/-- What the first program must leave for the second to run as after a request of its own. -/
def mboundary : List MTag → Bool
  | [st, eff, ctx] =>
      st.strong == some true && eff.v == .dec && eff.strong == some false && eff.fc &&
        ctx.v == .orig 0 && ctx.strong == some false && ctx.fc
  | _ => false

/-- The largest merged program, and the most branches in it (each doubles the paths checked:
    `mcheck` explores at most `2 ^ 8` paths of at most `1024` instructions). -/
def maxMergeOps : Nat := 1024
def maxMergeBranches : Nat := 8

/-- `ops₂` may run after `ops₁` in the same request (see the file header). -/
def mergeable (ops₁ ops₂ : List (Op Expr)) : Bool :=
  ops₁.length + ops₂.length ≤ maxMergeOps &&
    ((ops₁ ++ ops₂).filter Op.isBranch).length ≤ maxMergeBranches &&
    mcheck false mboundary (ops₁.length + 1) ops₁ minit &&
    mcheck true (fun _ => true) (ops₂.length + 1) ops₂ minit

/-- The alignments of a program's `popeq`s, in order. -/
def opsAligns {α : Type} : List (Op α) → List (List Zkir.AlignAtom)
  | [] => []
  | .popeq _ align _ :: ops => align :: opsAligns ops
  | _ :: ops => opsAligns ops

/-- As many read variables as the `popeq`s give field elements. -/
def widthOk (rs : List Var) (ops : List (Op Expr)) : Bool :=
  ((opsAligns ops).map fun a => (a.map atomWidth).sum).sum == rs.length

/-- Every variable a ledger program's instructions mention (operands and `popeq` results). -/
def opsVars (ops : List (Op Expr)) : List Var :=
  ops.flatMap fun op => (op.encode Expr.const).flatMap Expr.vars

/-- The variables a statement reads. -/
def Stmt.mUses : Stmt → List Var
  | .bind _ _ e => e.vars
  | .assert c _ => c.vars
  | .constrain e _ => e.vars
  | .witness g _ args _ _ => g.vars ++ Expr.varsList args
  | .ledger g _ ops => g.vars ++ opsVars ops

/-- The variables a statement binds. -/
def Stmt.mBinds : Stmt → List Var
  | .bind v _ _ => [v]
  | .witness _ _ _ outs _ => outs.map Prod.fst
  | .ledger _ rs _ => rs
  | _ => []

def Stmt.isLedger : Stmt → Bool
  | .ledger .. => true
  | _ => false

/-- The ledger statement `s` may move above `x`. -/
def lcommutes (s x : Stmt) : Bool :=
  (match x with
    | .witness _ name _ _ _ => !ctxWitness name
    | _ => true) &&
  !(s.mUses.any x.mBinds.contains) && !(s.mBinds.any fun v => x.mUses.contains v || x.mBinds.contains v)

/-- `.ledger g rs₁ ops₁` followed by `s`, as one statement. -/
def mergeInto (g : Expr) (rs₁ : List Var) (ops₁ : List (Op Expr)) : Stmt → Option Stmt
  | .ledger g₂ rs₂ ops₂ =>
      if g₂ == g && !ops₁.isEmpty && !ops₂.isEmpty && !(g.vars.any rs₁.contains) &&
          !((opsVars ops₂).any rs₁.contains) && !((opsVars ops₁).any rs₂.contains) &&
          widthOk rs₁ ops₁ && widthOk rs₂ ops₂ && mergeable ops₁ ops₂
      then some (.ledger g (rs₁ ++ rs₂) (ops₁ ++ ops₂)) else none
  | _ => none

/-- The statements up to the next ledger statement (at most `n` of them), that
    statement, and the rest. -/
def nextLedger : Nat → List Stmt → Option (List Stmt × Stmt × List Stmt)
  | 0, _ => none
  | _, [] => none
  | n + 1, s :: rest =>
      if s.isLedger then some ([], s, rest)
      else (nextLedger n rest).map fun (gap, l, rest') => (s :: gap, l, rest')

/-- How many statements may lie between two ledger statements that are merged. -/
def mergeWindow : Nat := 64

/-- The scan: merge the next ledger statement into the current one while possible. -/
def lmergeGo : Nat → List Stmt → List Stmt
  | 0, stmts => stmts
  | _ + 1, [] => []
  | fuel + 1, s :: rest =>
      match s with
      | .ledger g rs ops =>
          match nextLedger mergeWindow rest with
          | some (gap, l, rest') =>
              if gap.all (lcommutes l) then
                match mergeInto g rs ops l with
                | some m => lmergeGo fuel (m :: gap ++ rest')
                | none => s :: lmergeGo fuel rest
              else s :: lmergeGo fuel rest
          | none => s :: lmergeGo fuel rest
      | _ => s :: lmergeGo fuel rest

/-- Merge ledger statements into one request where the VM cannot tell (see the file header). -/
def Circuit.ledgerMerge (c : Circuit) : Circuit :=
  { c with body := (lmergeGo (2 * c.body.size + 1) c.body.toList).toArray }

end Damp.IR
