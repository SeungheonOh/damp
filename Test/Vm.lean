/-
Differential test of `Damp/Ledger/Vm.lean` (the model of Midnight's on-chain
VM) and `Damp/Ledger/Query.lean` against the real VM. See
docs/ledger-model.md and test/vm.sh.

  lake exe damp-vm-test <vectors.json> [--verbose]

Each vector (written by executor/test/vm-vectors.mjs) is a VM stack, a
program in Damp's instructions, and what the real VM did with it, twice: as a
bare program (`runProgram`: success, final stack with strengths, values read)
and as a query (`QueryContext.query`: success, new state, effects, values
read). The model runs the same program (`runOps`, and `Op.toR` then `query`)
and must agree on all of it. Maps and Merkle tree leaves are compared as sets.

The `root` instruction is a parameter of the model (`Hooks.root`); here it is
`merkleHooks` (`Damp/Ledger/Merkle.lean`), the real Merkle root.

One part of a query is abstracted on purpose: the runtime decodes the effects
into typed Rust values at the end of a query and rejects keys and values of
the wrong type ("failed to decode for built-in type ..."); the model checks only
their outer shape. A vector where the runtime rejects for that reason and the
model accepts is counted separately, not as a disagreement. Likewise the
effects after a successful query are compared but reported separately, since
the runtime re-encodes them (normalising alignments).
-/
import Damp.Ledger.Query
import Damp.Ledger.Merkle

open Lean (Json)
open Damp Damp.Ledger Damp.Impact
open Damp.Zkir (AlignAtom)

namespace Damp.VmTest

/-! ## Reading vectors -/

def natOf (s : String) : Except String Nat :=
  match s.toNat? with
  | some n => pure n
  | none => throw s!"not a number: {s}"

def frOf (s : String) : Except String Fr := do
  let n ← natOf s
  if n < Fr.modulus then pure (Fr.ofNat n) else throw s!"{s} is not below the modulus"

def atomOf (s : String) : Except String AlignAtom :=
  if s == "f" then pure .field
  else if s == "c" then pure .compress
  else if s.startsWith "b" then return .bytes (← natOf (s.drop 1).toString)
  else throw s!"bad atom {s}"

def arr (j : Json) (k : String) : Except String (List Json) := do
  let a ← j.getObjValAs? (Array Json) k
  pure a.toList

def strs (j : Json) (k : String) : Except String (List String) := do
  let a ← j.getObjValAs? (Array String) k
  pure a.toList

def avOf (j : Json) : Except String AV := do
  let align ← (← strs j "a").mapM atomOf
  let atoms ← (← strs j "x").mapM natOf
  pure ⟨align, atoms⟩

def alignedOf (j : Json) : Except String (Aligned Fr) := do
  let align ← (← strs j "align").mapM atomOf
  let vals ← (← strs j "vals").mapM frOf
  pure ⟨align, vals⟩

def arrStr (j : Json) (i : Nat) : Except String String := do
  Lean.fromJson? (← j.getArrVal? i)

partial def svOf (j : Json) : Except String SV := do
  match ← j.getObjValAs? String "t" with
  | "n" => pure .null
  | "c" => return .cell (← avOf (← j.getObjVal? "v"))
  | "m" =>
      let es ← arr j "e"
      let es ← es.mapM fun e => do
        let k ← e.getArrVal? 0
        let v ← e.getArrVal? 1
        pure (← avOf k, ← svOf v)
      pure (.map es)
  | "a" => return .array (← (← arr j "e").mapM svOf)
  | "b" =>
      let h ← j.getObjValAs? Nat "h"
      let ls ← (← arr j "l").mapM fun e => do
        let i ← arrStr e 0
        let x ← arrStr e 1
        pure (← natOf i, ← natOf x)
      pure (.bmt h ls)
  | t => throw s!"bad state value tag {t}"

partial def litOf (j : Json) : Except String (StateLit Fr) := do
  match ← j.getObjValAs? String "t" with
  | "n" => pure .null
  | "c" => return .cell (← alignedOf (← j.getObjVal? "v"))
  | "m" => pure .emptyMap
  | "a" => return .array (← (← arr j "e").mapM litOf)
  | "b" => return .emptyMerkleTree (← j.getObjValAs? Nat "h")
  | t => throw s!"bad literal tag {t}"

def opOf (j : Json) : Except String (Op Fr) := do
  let o ← j.getObjValAs? String "o"
  let b (k : String) : Except String Bool := j.getObjValAs? Bool k
  let n : Except String Nat := j.getObjValAs? Nat "n"
  match o with
  | "lt" => pure .lt | "eq" => pure .eq | "type" => pure .type | "size" => pure .size
  | "and" => pure .and | "or" => pure .or | "neg" => pure .neg | "log" => pure .log
  | "root" => pure .root | "pop" => pure .pop | "add" => pure .add | "sub" => pure .sub
  | "member" => pure .member | "ckpt" => pure .ckpt
  | "popeq" => return .popeq (← b "cached") [] []
  | "addi" => return .addi (← frOf (← j.getObjValAs? String "imm"))
  | "subi" => return .subi (← frOf (← j.getObjValAs? String "imm"))
  | "push" => return .push (← b "storage") (← alignedOf (← j.getObjVal? "v"))
  | "pushNull" => return .pushNull (← b "storage")
  | "pushState" => return .pushState (← b "storage") (← litOf (← j.getObjVal? "v"))
  | "rem" => return .rem (← b "cached")
  | "dup" => return .dup (← n)
  | "swap" => return .swap (← n)
  | "idx" => return .idx (← b "cached") (← b "pushPath") (← (← arr j "path").mapM alignedOf)
  | "idxStack" => return .idxStack (← (← arr j "path").mapM alignedOf)
  | "ins" => return .ins (← b "cached") (← n)
  | "branch" => return .branch (← n)
  | "jmp" => return .jmp (← n)
  | "concat" => return .concat (← n)
  | "concatCached" => return .concatCached (← n)
  | _ => throw s!"bad op {o}"

/-! ## Comparing -/

def insertSorted (x : String) : List String → List String
  | [] => [x]
  | y :: ys => if x < y || x == y then x :: y :: ys else y :: insertSorted x ys

def sortStrs (xs : List String) : List String := xs.foldr insertSorted []

def atomStr : AlignAtom → String
  | .bytes n => s!"b{n}" | .field => "f" | .compress => "c"

def avStr (v : AV) : String :=
  s!"<{",".intercalate (v.align.map atomStr)}:{",".intercalate (v.atoms.map toString)}>"

/-- A canonical text for a state value: map entries and tree leaves sorted. -/
partial def canon : SV → String
  | .null => "null"
  | .cell v => avStr v
  | .map es => "{" ++ ";".intercalate (sortStrs (es.map fun (k, v) => avStr k ++ "=" ++ canon v)) ++ "}"
  | .array es => "[" ++ ",".intercalate (es.map canon) ++ "]"
  | .bmt h ls => s!"tree{h}(" ++ ";".intercalate (sortStrs (ls.map fun (i, x) => s!"{i}={x}")) ++ ")"

structure Vec where
  id : Nat
  group : String
  kind : String
  root : Bool
  init : List (SV × Bool)
  ops : Except String (List (Op Fr))
  vm : Json
  query : Json

def stackOf (values : Array SV) (j : List Json) : Except String (List (SV × Bool)) :=
  j.mapM fun e => do
    let i ← e.getObjValAs? Nat "v"
    let s ← e.getObjValAs? Bool "s"
    match values[i]? with
    | some v => pure (v, s)
    | none => throw s!"no value {i}"

def readsOf (j : Json) : Except String (List AV) := do (← arr j "reads").mapM avOf

def H : Hooks := merkleHooks

inductive Verdict where
  | pass
  | skip
  | fail (why : String)

def compareVm (values : Array SV) (v : Vec) : Except String Verdict := do
  let expOk ← v.vm.getObjValAs? Bool "ok"
  let got : Option VmState := match v.ops with
    | .ok ops => runOps H ops (VmState.init v.init)
    | .error _ => none
  match expOk, got with
  | false, none => pure .pass
  | false, some _ => pure (.fail s!"VM: real fails ({v.vm.getObjValAs? String "err" |>.toOption.getD ""}), model succeeds")
  | true, none => pure (.fail "VM: real succeeds, model fails")
  | true, some s =>
      let expStack ← stackOf values (← arr v.vm "stack")
      let gotStack := s.stack.reverse.map fun e => (e.val, e.strong)
      if expStack.length != gotStack.length then
        return .fail s!"VM: stack height {gotStack.length}, real {expStack.length}"
      for ((ev, es), (gv, gs)) in expStack.zip gotStack do
        if canon ev != canon gv then return .fail s!"VM: stack value {canon gv}, real {canon ev}"
        if es != gs then return .fail s!"VM: strength {gs} of {canon gv}, real {es}"
      let reads ← readsOf v.vm
      if reads != s.reads then
        return .fail s!"VM: reads {s.reads.map avStr}, real {reads.map avStr}"
      pure .pass

/-- Whether the query agrees, and separately whether the effects do. -/
def compareQuery (values : Array SV) (v : Vec) : Except String (Verdict × Bool) := do
  let expOk ← v.query.getObjValAs? Bool "ok"
  let q : Option LedgerState := match v.init with
    | [(c, _), (e, _), (s, _)] => some { context := c, effects := e, state := s }
    | _ => none
  let got := match v.ops, q with
    | .ok ops, some q => do
        let rops ← ops.mapM Op.toR
        query H rops q
    | _, _ => none
  match expOk, got with
  | false, none => pure (.pass, true)
  | false, some _ =>
      let err := (v.query.getObjValAs? String "err").toOption.getD ""
      if (err.splitOn "failed to decode for built-in type").length > 1 then pure (.skip, true)
      else pure (.fail s!"query: real fails ({err}), model succeeds", true)
  | true, none => pure (.fail "query: real succeeds, model fails", true)
  | true, some (reads, q') =>
      let state ← (do let i ← v.query.getObjValAs? Nat "state"; pure values[i]!)
      let effects ← (do let i ← v.query.getObjValAs? Nat "effects"; pure values[i]!)
      let expReads ← readsOf v.query
      let effOk := canon effects == canon q'.effects
      if canon state != canon q'.state then
        return (.fail s!"query: state {canon q'.state}, real {canon state}", effOk)
      if expReads != reads then
        return (.fail s!"query: reads {reads.map avStr}, real {expReads.map avStr}", effOk)
      pure (.pass, effOk)

def vecOf (values : Array SV) (j : Json) : Except String Vec := do
  let init ← stackOf values (← arr j "init")
  pure {
    id := ← j.getObjValAs? Nat "id"
    group := ← j.getObjValAs? String "group"
    kind := ← j.getObjValAs? String "kind"
    root := ← j.getObjValAs? Bool "root"
    init
    ops := do (← arr j "ops").mapM opOf
    vm := ← j.getObjVal? "vm"
    query := ← j.getObjVal? "query"
  }

def run (file : String) (verbose : Bool) : IO UInt32 := do
  let text ← IO.FS.readFile file
  let j ← IO.ofExcept (Json.parse text)
  let values ← IO.ofExcept (do (← arr j "values").mapM svOf)
  let values := values.toArray
  let vecs ← IO.ofExcept (arr j "vectors")
  let mut vmPass := 0
  let mut vmSkip := 0
  let mut qPass := 0
  let mut qSkip := 0
  let mut effAgree := 0
  let mut effCompared := 0
  let mut fails := 0
  let mut realOk := 0
  for vj in vecs do
    match vecOf values vj with
    | .error e =>
        IO.println s!"FAIL (unreadable vector): {e}"
        fails := fails + 1
    | .ok v =>
        if (v.vm.getObjValAs? Bool "ok").toOption == some true then realOk := realOk + 1
        let r1 := compareVm values v
        let r2 := compareQuery values v
        let mut why : List String := []
        match r1 with
        | .ok .pass => vmPass := vmPass + 1
        | .ok .skip => vmSkip := vmSkip + 1
        | .ok (.fail w) => why := why ++ [w]
        | .error e => why := why ++ [s!"VM: unreadable: {e}"]
        match r2 with
        | .ok (.pass, eff) =>
            qPass := qPass + 1
            if (v.query.getObjValAs? Bool "ok").toOption == some true then
              effCompared := effCompared + 1
              if eff then effAgree := effAgree + 1
              else if verbose then IO.println s!"note: effects differ in vector {v.id} [{v.group}] {v.kind}"
        | .ok (.skip, _) => qSkip := qSkip + 1
        | .ok (.fail w, _) => why := why ++ [w]
        | .error e => why := why ++ [s!"query: unreadable: {e}"]
        unless why.isEmpty do
          fails := fails + 1
          if fails ≤ 60 then
            IO.println s!"FAIL vector {v.id} [{v.group}] {v.kind}: {"; ".intercalate why}"
  let n := vecs.length
  IO.println s!"{n} vectors ({realOk} succeed in the real VM)"
  IO.println s!"VM (runProgram):         {vmPass} agree, {n - vmPass - vmSkip} disagree"
  IO.println s!"query (QueryContext):    {qPass} agree, {qSkip} rejected by the runtime's typed effects decoding (abstracted), {n - qPass - qSkip} disagree"
  IO.println s!"effects after a query:   {effAgree} of {effCompared} successful queries agree (typed re-encoding abstracted)"
  IO.println (if fails = 0 then "ALL AGREE" else s!"{fails} vector(s) disagree")
  return if fails = 0 then 0 else 1

end Damp.VmTest

def main (args : List String) : IO UInt32 := do
  match args with
  | [file] => Damp.VmTest.run file false
  | [file, "--verbose"] => Damp.VmTest.run file true
  | _ =>
      IO.eprintln "usage: damp-vm-test <vectors.json> [--verbose]"
      return 2
