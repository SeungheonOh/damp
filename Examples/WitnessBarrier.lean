import Damp
import Damp.Ledger.Merkle

/-! The witness barriers of the ledger passes are needed: counterexamples.

`Pass.SoundLedger` (`Damp/Proofs/Optimize/LedgerSound.lean`) quantifies over
every witness oracle that does what the runtime's witnesses do
(`WitnessesOK`, `Damp/Executor/Witnesses.lean`). `demoW` below is such an
oracle (`demoW_ok`): its user witness `peek` answers what contract-state field
1 holds (as a user's witness reading `WitnessContext.ledger` does), and its
`createZswapOutput` inserts an entry into call-context slot 1 (as the
runtime's `insertCommitment` does).

For each pass, a copy with its witness barrier removed is run through the
executor against the VM model with `demoW`: it changes what the original
circuit does, while the pass itself does not. So the barriers are not
folklore: without them the passes are unsound for an oracle the hypothesis
allows, and the proofs fail at exactly the step that uses them:

* `ledgerDeadStore` without `stateWitness`: `steps_ctxmap` needs, at the
  witness, `CtxOnly wit name` (the witness sees only the call context); for a
  user's witness `WitnessesOK` gives only `ReadsLedger wit name`, whose answer
  `g args x l.context l.state` depends on `l.state`, the field the dropped
  write changed. The goal left is
  `wit "peek" a x { l with state := st₁ } = (wit "peek" a x l).map …`, false
  for `demoW`.
* `ledgerMerge` without `isolatedWitness`: `step_commute` needs `hiso :
  Isolated O.witness name`; for `peek` the goal `∃ g, ∀ args x l, demoW "peek"
  args x l = (g args x).map …` is false (the answer depends on `l`).
* `ledgerReuse` without the filter at `ctxWitness`: `inv_witness` must show a
  fact about slot 1 survives: `readSpec 2 path' a q' = readSpec 2 path' a q`
  with `q'.context` differing from `q.context` at slot 1, false for `demoW`.
* `ledgerHoist` without `ctxWitness`: `step_ctx_patch` needs
  `t.ledger.context = s.ledger.context` after the witness, false after
  `createZswapOutput`.
-/
namespace Examples.WitnessBarrier
open Damp Damp.IR Damp.Impact Damp.Ledger Damp.Exec

private def key (i : Nat) : Aligned Expr := fieldKey i
private def one : Expr := .const 1

private def rd (i v : Nat) : Stmt :=
  .ledger one [v] [.dup 0, .idx false false [key i], .popeq false [.field] [.var v]]
private def wr (i : Nat) (e : Expr) : Stmt :=
  .ledger one [] [.push false (key i), .push true ⟨[.field], [e]⟩, .ins false 1]
/-- A lookup of the commitment `x0` in the context's `com_indices` (slot 1). -/
private def ctxIdx (v : Nat) : Stmt :=
  .ledger one [v] [.dup 2, .idx true false [key 1, ⟨[.bytes 32], [.const 0, .var 0]⟩],
    .popeq true [.bytes 8] [.var v]]
private def peek (v : Nat) : Stmt := .witness one "peek" [] [(v, none)] (.prim .field)
private def zout : Stmt := .witness one "createZswapOutput" [.var 0] [] (.tuple [])

private def mk (n : Nat) (body : List Stmt) (outputs : List Expr) : Circuit where
  name := "t"
  args := []
  inputs := (List.range n).map fun v => { name := s!"x{v}", var := v, range := none }
  body := body.toArray
  result := .tuple []
  outputs := outputs

/-! ### An oracle the hypothesis allows -/

/-- What a user's witness reading field 1 of the contract state answers. -/
def peekVal (st : SV) : Fr :=
  match st with
  | .array fs => match (fs[1]? : Option SV) with
    | some (SV.cell v) => Fr.ofNat (v.atoms.headD 0)
    | _ => 0
  | _ => 0

/-- `createZswapOutput`'s commitment entry: 99 at index 0, in slot 1. -/
def bump (c : SV) : SV :=
  match c with
  | .array cs => .array (cs.set 1 (.map [(AV.ofHash 99, .cell (AV.ofU64 0))]))
  | c => c

def demoW : WitnessOracle Unit LedgerState := fun n _ x l =>
  if n == "createZswapOutput" then some ([], x, { l with context := bump l.context })
  else if witnessClass n == .isolated then some ([], x, l)
  else some ([peekVal l.state], x, l)

theorem witnessClass_zswap {n : String} (h : witnessClass n = .zswapOutput) : n = "createZswapOutput" := by
  unfold witnessClass at h
  by_cases h1 : (n == "createZswapOutput") = true
  · exact beq_iff_eq.mp h1
  · simp only [h1, Bool.false_eq_true, ite_false] at h
    split at h <;> simp at h

theorem bump_agree (c : SV) : CtxAgreeExcept 1 c (bump c) := by
  cases c with
  | array cs =>
    refine Or.inr ⟨cs, _, rfl, rfl, by simp, fun i hi => ?_⟩
    simp [Ne.symm hi]
  | _ => exact Or.inl rfl

/-- `demoW` does what the runtime's witnesses do. -/
theorem demoW_ok : WitnessesOK demoW := by
  intro n
  cases hc : witnessClass n with
  | isolated =>
    have hn : (n == "createZswapOutput") = false := by
      cases h : (n == "createZswapOutput")
      · rfl
      · rw [beq_iff_eq.mp h] at hc; simp [witnessClass] at hc
    exact ⟨fun _ x => some ([], x), fun a x l => by simp [demoW, hn, hc]⟩
  | zswapOutput =>
    have hn := witnessClass_zswap hc
    subst hn
    exact ⟨fun _ x c => some ([], x, bump c), fun a x l => by simp [demoW],
      fun a x c r x' c' h => by simp at h; obtain ⟨-, -, rfl⟩ := h; exact bump_agree c⟩
  | user =>
    have hn : (n == "createZswapOutput") = false := by
      cases h : (n == "createZswapOutput")
      · rfl
      · rw [beq_iff_eq.mp h] at hc; simp [witnessClass] at hc
    exact ⟨fun _ x _ st => some ([peekVal st], x), fun a x l => by simp [demoW, hn, hc]⟩

private def σ₀ : LedgerState where
  context := .array [.cell ⟨[.bytes 32], [12345]⟩, .map [], .cell (AV.ofU64 7)]
  effects := .array (List.replicate 9 (.map []))
  state := .array [.null, .cell ⟨[.field], [3]⟩, .cell ⟨[.field], [4]⟩]

/-- Outputs, private transcript and final ledger state of a run. -/
private def run (c : Circuit) (inputs : List Nat) : String :=
  match Exec.run Crypto.prims (oracles merkleHooks demoW) c (inputs.map Fr.ofNat) () σ₀ with
  | none => "fails"
  | some r => reprStr (r.outputs.map (·.val), r.priv.map (·.val), r.ledger.state, r.ledger.context)

/-! ### `ledgerDeadStore` and a user's witness -/

/-- `overwrites` without the barrier at a user's witness. -/
private def overwritesNB (k : Aligned Expr) : Nat → List Stmt → Bool
  | 0, _ => false
  | _, [] => false
  | n + 1, s :: rest =>
      match s with
      | .ledger (.const 1) [] [.push false k', .push true _, .ins false 1] => alignedSame k' k
      | .ledger .. => false
      | _ => overwritesNB k n rest

private def deadStoreNB : List Stmt → List Stmt
  | [] => []
  | s :: rest =>
      match droppableWrite? s with
      | some k => if overwritesNB k deadStoreWindow rest then deadStoreNB rest else s :: deadStoreNB rest
      | none => s :: deadStoreNB rest

private def cDead := mk 0 [wr 1 (.const 1), peek 5, wr 1 (.const 2)] [.var 5]
-- the witness sees 1; without the barrier the first write is dropped and it sees 3
#guard run cDead [] == run cDead.ledgerDeadStore []
#guard run cDead [] != run { cDead with body := (deadStoreNB cDead.body.toList).toArray } []
#guard (deadStoreNB cDead.body.toList).length == 2

/-! ### `ledgerMerge` and a user's witness -/

private def lmergeGoNB : Nat → List Stmt → List Stmt
  | 0, stmts => stmts
  | _ + 1, [] => []
  | fuel + 1, s :: rest =>
      match s with
      | .ledger g rs ops =>
          match nextLedger mergeWindow rest with
          | some (gap, l, rest') =>
              -- `lcommutes true`: lets `l` pass a user's witness, as a context read may
              if gap.all (lcommutes true l) then
                match mergeInto g rs ops l with
                | some m => lmergeGoNB fuel (m :: gap ++ rest')
                | none => s :: lmergeGoNB fuel rest
              else s :: lmergeGoNB fuel rest
          | none => s :: lmergeGoNB fuel rest
      | _ => s :: lmergeGoNB fuel rest

private def cMerge := mk 0 [rd 1 10, peek 5, wr 1 (.const 7)] [.var 10, .var 5]
-- the witness sees 3; with the write merged above it, it sees 7
#guard run cMerge [] == run cMerge.ledgerMerge []
#guard run cMerge [] != run { cMerge with body := (lmergeGoNB 7 cMerge.body.toList).toArray } []
#guard (lmergeGoNB 7 cMerge.body.toList).length == 2

/-! ### `ledgerHoist` and `createZswapOutput` -/

private def findNB (g : Expr) (rs : List Var) (ops : List (Op Expr)) : Nat → List Stmt → Option (List Stmt × Stmt × List Stmt)
  | 0, _ => none
  | _, [] => none
  | n + 1, x :: l =>
      if x.ctxRead && x.guardIs g && (mergeInto g rs ops x).isSome then some ([], x, l)
      else (findNB g rs ops n l).bind fun (mid, r, rest) =>
        -- `lcommutes true` with `createZswapOutput` treated as isolated
        let ok := match x with
          | .witness _ "createZswapOutput" _ _ _ => true
          | _ => lcommutes true r x
        if ok && !x.emptyLedger then some (x :: mid, r, rest) else none

private def hoistNB : Nat → List Stmt → List Stmt
  | 0, l => l
  | _ + 1, [] => []
  | fuel + 1, s :: rest =>
      match s with
      | .ledger g rs ops =>
          match findNB g rs ops hoistWindow rest with
          | some (mid, r, rest') => s :: r :: hoistNB fuel (mid ++ rest')
          | none => s :: hoistNB fuel rest
      | _ => s :: hoistNB fuel rest

private def cHoist := mk 1 [rd 1 10, zout, ctxIdx 12] [.var 12]
-- the lookup finds the commitment `createZswapOutput` inserted; hoisted above it, it finds nothing
#guard run cHoist [99] != "fails"
#guard run cHoist [99] == run cHoist.ledgerHoist [99]
#guard run cHoist [99] != run { cHoist with body := (hoistNB 4 cHoist.body.toList).toArray } [99]

/-! ### `ledgerReuse` and `createZswapOutput` -/

/-- `ledgerReuseGo` without the filter at `ctxWitness`. -/
private def reuseNB : List LFact → List Stmt → List Stmt
  | _, [] => []
  | fs, s :: rest =>
      match s with
      | .bind v _ _ => s :: reuseNB (forgetVars [v] fs) rest
      | .assert .. | .constrain .. => s :: reuseNB fs rest
      | .witness _ _ _ outs _ => s :: reuseNB (forgetVars (outs.map Prod.fst) fs) rest
      | .ledger g rs ops =>
          match plainRead? rs ops with
          | some (n, path, a) =>
              match findFact g n path a rs fs with
              | some f => bindReads rs f.vals ++ reuseNB (forgetVars rs fs) rest
              | none => s :: reuseNB (missFacts g rs n path a fs) rest
          | none => s :: reuseNB (otherFacts g rs ops fs) rest

-- with the commitment already present, a lookup before and after `createZswapOutput`: the second
-- sees the new index
private def σ₁ : LedgerState :=
  { σ₀ with context := .array [.cell ⟨[.bytes 32], [12345]⟩, .map [(AV.ofHash 99, .cell (AV.ofU64 5))],
      .cell (AV.ofU64 7)] }
private def run₁ (c : Circuit) (inputs : List Nat) : String :=
  match Exec.run Crypto.prims (oracles merkleHooks demoW) c (inputs.map Fr.ofNat) () σ₁ with
  | none => "fails"
  | some r => reprStr (r.outputs.map (·.val), r.ledger.context)
private def cReuse := mk 1 [ctxIdx 10, zout, ctxIdx 12] [.var 10, .var 12]
#guard run₁ cReuse [99] == run₁ cReuse.ledgerReuse [99]
#guard run₁ cReuse [99] != run₁ { cReuse with body := (reuseNB [] cReuse.body.toList).toArray } [99]

end Examples.WitnessBarrier
