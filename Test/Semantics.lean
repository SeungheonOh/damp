/-
Differential test of `Damp/Zkir/Semantics.lean` against Midnight's real ZKIR
evaluator. See docs/zkir-semantics.md and test/semantics.sh.

  lake exe damp-semantics-test <vectors.json> [--emitted] <file.zkir>... [--other <file.zkir>...]

1. Cryptography: `Damp.Crypto` against values computed by the runtime (and by
   Node for SHA-256).
2. Every `.zkir` given: parsed by `Damp/Zkir/Json.lean` and printed back by
   `IrSource.toJson`; the result must be the same JSON. Those after
   `--emitted` must also pass `IrSource.checkSingleAssignment`.
3. Every vector: the Lean evaluator with `Damp.Crypto.prims`, compared with
   what the real `check` did on the same preimage. `IrSource.preprocess` gives
   the verdict and the outputs; a staged run built from the same pieces
   (`bindInputs`, `Instr.step`, `Outcome.activeInputs`, `transientCommit`)
   names the first thing that failed, in the order the Rust checks it, so the
   kind of rejection can be compared too.
-/
import Damp.Zkir.Semantics
import Damp.Zkir.Json
import Damp.Crypto.Prims

open Lean (Json)
open Damp Damp.Zkir

namespace Damp.SemanticsTest

/-! ## Reading vectors -/

def str (j : Json) (k : String) : Except String String := j.getObjValAs? String k

def frOf (s : String) : Except String Fr :=
  match s.toNat? with
  | some n => if n < Fr.modulus then pure (Fr.ofNat n) else throw s!"{s} is not below the modulus"
  | none => throw s!"not a number: {s}"

def frs (j : Json) (k : String) : Except String (List Fr) := do
  let xs ← j.getObjValAs? (Array String) k
  xs.toList.mapM frOf

def optFrs (j : Json) (k : String) : Except String (Option (List Fr)) :=
  match j.getObjVal? k with
  | .ok .null | .error _ => pure none
  | .ok _ => some <$> frs j k

def hexBytes (s : String) : Except String (List Nat) :=
  match Zkir.hexBytes s.toList with
  | some bs => pure bs
  | none => throw s!"bad hex {s}"

def toHex (bs : List Nat) : String := String.join (bs.map Zkir.hexByte)

/-! ## The staged run -/

inductive Verdict where
  | accept (o : Outcome)
  | reject (reason : String) (detail : String)

def Verdict.reason : Verdict → String
  | .accept _ => "accept"
  | .reject r _ => r

def opName (i : Instr) : String :=
  match i.toJson.getObjValAs? String "op" with
  | .ok s => s
  | .error _ => "?"

/-- `xs` is a prefix of `ys`. -/
def isPrefix : List Fr → List Fr → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => x == y && isPrefix xs ys

/-- Index of the first position where two lists differ. -/
def firstDiff : List Fr → List Fr → Nat → Nat
  | x :: xs, y :: ys, n => if x == y then firstDiff xs ys (n + 1) else n
  | _, _, n => n

/-- Instructions that ran (op name, and for guarded ones whether the guard held). -/
abbrev Coverage := Std.HashMap String Nat

def guardTag (m : Memory) : Instr → String
  | .privateInput _ _ g | .publicInput _ _ g =>
      match g with
      | none => " (no guard)"
      | some g => match bool m g with
        | some true => " (guard true)" | some false => " (guard false)" | none => " (guard not boolean)"
  | .impact g _ => match bool m g with
      | some true => " (guard true)" | some false => " (guard false)" | none => " (guard not boolean)"
  | _ => ""

/-- Run as `IrSource::preprocess` does, stopping at the first failure:
    inputs, then each instruction (an active `impact` must extend a prefix of
    the claimed public transcript inputs), then the transcripts must be used
    up, then the commitment. -/
def staged (p : Prims) (src : IrSource) (pre : Preimage) (cov : Coverage) : Verdict × Coverage := Id.run do
  let some mem := bindInputs (fun _ => none) src.inputs pre.inputs
    | return (.reject "inputs" s!"{pre.inputs.length} inputs for {src.inputs.length}", cov)
  let mut s : State := { mem, priv := pre.privateTranscript, pub := pre.publicTranscriptOutputs }
  let mut cov := cov
  let mut k := 0
  for i in src.instructions.toList do
    let tag := opName i ++ guardTag s.mem i
    -- `IrSource.run` checks output arities up front; the Rust checks each `output` as it runs it.
    if !({ src with instructions := #[i] } : IrSource).outputsDeclared then
      cov := cov.insert s!"{opName i} fails" (cov.getD s!"{opName i} fails" 0 + 1)
      return (.reject "premise" s!"instruction {k} ({opName i}) does not match the declared outputs", cov)
    match i.step p s with
    | none =>
        cov := cov.insert s!"{opName i} fails" (cov.getD s!"{opName i} fails" 0 + 1)
        return (.reject "premise" s!"instruction {k} ({opName i}) fails", cov)
    | some s' =>
        cov := cov.insert tag (cov.getD tag 0 + 1)
        s := s'
        let o : Outcome := { outputs := s.outputs, groups := s.groups }
        if !isPrefix o.activeInputs pre.publicTranscriptInputs then
          return (.reject "pt-mismatch"
            s!"instruction {k} ({opName i}): public input {firstDiff o.activeInputs pre.publicTranscriptInputs 0} differs from the transcript", cov)
    k := k + 1
  let o : Outcome := { outputs := s.outputs, groups := s.groups }
  if !s.priv.isEmpty || !s.pub.isEmpty || o.activeInputs.length != pre.publicTranscriptInputs.length then
    return (.reject "unconsumed"
      s!"left: {s.priv.length} private, {s.pub.length} public outputs, {pre.publicTranscriptInputs.length - o.activeInputs.length} public inputs", cov)
  if src.commCommitment then
    match pre.commitment with
    | none => return (.reject "commitment" "no commitment", cov)
    | some (c, r) =>
        if c != p.transientCommit (pre.inputs ++ o.outputs) r then
          return (.reject "commitment" "commitment does not open to inputs and outputs", cov)
  return (.accept o, cov)

/-- The real checker's skip list: `null` for an active impact, its width otherwise. -/
def skipsOf (o : Outcome) : List (Option Nat) :=
  o.groups.map fun g => if g.active then none else some g.vals.length

/-! ## Main -/

structure Tally where
  ok : Nat := 0
  fail : Nat := 0

def Tally.add (t : Tally) (good : Bool) : Tally :=
  if good then { t with ok := t.ok + 1 } else { t with fail := t.fail + 1 }

def report (t : Tally) (good : Bool) (line : String) : IO Tally := do
  IO.println s!"{if good then "ok  " else "FAIL"} {line}"
  return t.add good

def cryptoTests (c : Json) (t : Tally) : IO Tally := do
  let mut t := t
  let arr (k : String) : Array Json := (c.getObjValAs? (Array Json) k).toOption.getD #[]
  for (case, n) in (arr "transientHash").zipIdx do
    let xs ← IO.ofExcept (frs case "inputs")
    let e ← IO.ofExcept (str case "expected" >>= frOf)
    let got := Crypto.transientHash xs
    t ← report t (got == e) s!"crypto transient_hash #{n} ({xs.length} elements){if got == e then "" else s!": got {got}, runtime {e}"}"
  for (case, n) in (arr "transientCommit").zipIdx do
    let xs ← IO.ofExcept (frs case "inputs")
    let r ← IO.ofExcept (str case "opening" >>= frOf)
    let e ← IO.ofExcept (str case "expected" >>= frOf)
    let got := Crypto.transientCommit xs r
    t ← report t (got == e) s!"crypto transient_commit #{n} ({xs.length} elements, opening {r}){if got == e then "" else s!": got {got}, runtime {e}"}"
  for (case, n) in (arr "persistentHash").zipIdx do
    let al ← IO.ofExcept ((case.getObjValAs? (Array Json) "alignment") >>= fun a => a.toList.mapM Zkir.parseAtom)
    let xs ← IO.ofExcept (frs case "inputs")
    let note := (str case "note").toOption.getD ""
    let got := Crypto.persistentHash al xs
    match case.getObjVal? "expected" with
    | .ok (.str e) =>
        let e ← IO.ofExcept (hexBytes e)
        t ← report t (got == some e) s!"crypto persistent_hash #{n} [{note}]{if got == some e then "" else s!": got {(got.map toHex).getD "none"}, runtime {toHex e}"}"
    | _ =>
        IO.println s!"     crypto persistent_hash #{n} [{note}]: Lean gives {(got.map toHex).getD "none"} (decided by the real evaluator in the synthetic vectors)"
  for (case, n) in (arr "sha256").zipIdx do
    let bs ← IO.ofExcept (str case "bytes" >>= hexBytes)
    let e ← IO.ofExcept (str case "expected" >>= hexBytes)
    let got := Crypto.Sha256.hashNat bs
    t ← report t (got == e) s!"crypto sha256 #{n} ({bs.length} bytes){if got == e then "" else s!": got {toHex got}, node {toHex e}"}"
  return t

/-- The reader accepts exactly the operands the Rust loader accepts. -/
def readerTests (cases : Array Json) (t : Tally) : IO Tally := do
  let mut t := t
  for c in cases do
    let o ← IO.ofExcept (str c "operand")
    let text ← IO.ofExcept (str c "text")
    let real ← IO.ofExcept (c.getObjValAs? Bool "realAccepts")
    let mine := (Zkir.IrSource.parse text).toBool
    t ← report t (mine == real) s!"zkir reader operand {o}: real {if real then "accepts" else "rejects"}, lean {if mine then "accepts" else "rejects"}"
  return t

/-- Parse, print, compare. `emitted` circuits must also pass Damp's single-assignment check. -/
def roundTrip (emitted : Bool) (path : String) (t : Tally) : IO Tally := do
  let text ← IO.FS.readFile path
  match Zkir.IrSource.parse text, Json.parse text with
  | .ok src, .ok orig =>
      let back := src.toJson
      let sa := match src.checkSingleAssignment with | .ok _ => "" | .error e => s!" (not single-assignment: {e})"
      let same := back.compress == orig.compress
      report t (same && (sa.isEmpty || !emitted)) s!"zkir round trip {path}: {src.instructions.size} instructions{sa}{if same then "" else " (printed JSON differs)"}"
  | .error e, _ => report t false s!"zkir round trip {path}: {e}"
  | _, .error e => report t false s!"zkir round trip {path}: not JSON: {e}"

def runVector (cache : IO.Ref (Std.HashMap String IrSource)) (v : Json) (t : Tally) (cov : Coverage) :
    IO (Tally × Coverage) := do
  let get (k : String) : IO String := IO.ofExcept (str v k)
  let id ← get "id"
  let group ← get "group"
  let kind ← get "kind"
  let path ← get "zkir"
  let src ← match (← cache.get)[path]? with
    | some s => pure s
    | none => do
        let s ← IO.ofExcept (Zkir.IrSource.parse (← IO.FS.readFile path))
        cache.modify (·.insert path s)
        pure s
  let inputs ← IO.ofExcept (frs v "inputs")
  let priv ← IO.ofExcept (frs v "priv")
  let ptOut ← IO.ofExcept (frs v "ptOut")
  let ptIn ← IO.ofExcept (frs v "ptIn")
  let comm ← IO.ofExcept (optFrs v "commitment")
  let commitment := match comm with
    | some [c, r] => some (c, r)
    | _ => none
  let expectOutputs ← IO.ofExcept (optFrs v "expectOutputs")
  let real ← IO.ofExcept (v.getObjVal? "real")
  let realOk ← IO.ofExcept (real.getObjValAs? Bool "ok")
  let realReason ← IO.ofExcept (str real "reason")
  let realError := (str real "error").toOption.getD ""
  let realSkips : Option (List (Option Nat)) := (real.getObjValAs? (List (Option Nat)) "skips").toOption
  let pre : Preimage := { inputs, privateTranscript := priv, publicTranscriptOutputs := ptOut,
                          publicTranscriptInputs := ptIn, commitment }
  let p := Crypto.prims
  let direct := src.preprocess p pre
  let (verdict, cov) := staged p src pre cov
  let head := s!"{id} {group} | {kind}: real {realReason}"
  -- The staged run must agree with `preprocess` itself.
  let consistent := match direct, verdict with
    | some o, .accept o' => o == o'
    | none, .reject .. => true
    | _, _ => false
  if !consistent then
    return (← report t false s!"{head}; preprocess and the staged run disagree ({verdict.reason}, preprocess {if direct.isSome then "accepts" else "rejects"})", cov)
  match verdict with
  | .accept o =>
      if !realOk then
        return (← report t false s!"{head}, lean accept  [real: {realError}]", cov)
      let outsOk := expectOutputs.all (· == o.outputs)
      let skipsOk := realSkips.all (· == skipsOf o)
      let good := outsOk && skipsOk
      let detail :=
        (if outsOk then "" else s!"  outputs {o.outputs} ≠ {expectOutputs.getD []}") ++
        (if skipsOk then "" else s!"  impact skips {skipsOf o} ≠ real {realSkips.getD []}")
      let same := if expectOutputs.isSome then ", same outputs" else ""
      return (← report t good s!"{head}, lean accept{if good then same else ""}{detail}", cov)
  | .reject reason detail =>
      -- For a public-transcript mismatch the Rust names the index; it must be the same one.
      let idxOk := reason != "pt-mismatch" ||
        ((realError.splitOn "for input ").getD 1 "").takeWhile Char.isDigit ==
          ((detail.splitOn "public input ").getD 1 "").takeWhile Char.isDigit
      let good := !realOk && reason == realReason && idxOk
      return (← report t good s!"{head}, lean {reason} ({detail}){if good then "" else s!"  [real: {realError}]"}", cov)

end Damp.SemanticsTest

open Damp.SemanticsTest in
def main (args : List String) : IO UInt32 := do
  let vectorsPath :: rest := args
    | IO.eprintln "usage: damp-semantics-test <vectors.json> [--emitted] <file.zkir>... [--other <file.zkir>...]"; return 2
  -- Files after `--emitted` (the default) must be single-assignment; after `--other` need not be.
  let zkirs := (rest.foldl (fun (acc : Bool × List (Bool × String)) a =>
    if a == "--emitted" then (true, acc.2) else if a == "--other" then (false, acc.2) else (acc.1, (acc.1, a) :: acc.2))
    (true, [])).2.reverse
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile vectorsPath))
  let mut t : Tally := {}
  let crypto ← IO.ofExcept (j.getObjVal? "crypto")
  t ← cryptoTests crypto t
  let afterCrypto := t
  t ← readerTests ((j.getObjValAs? (Array Json) "reader").toOption.getD #[]) t
  for (emitted, z) in zkirs do
    t ← roundTrip emitted z t
  let afterZkir := t
  let vs ← IO.ofExcept (j.getObjValAs? (Array Json) "vectors")
  let cache ← IO.mkRef ({} : Std.HashMap String Zkir.IrSource)
  let mut cov : Coverage := {}
  for v in vs do
    (t, cov) ← runVector cache v t cov
  IO.println "\ninstructions run by the Lean evaluator over all vectors:"
  for (k, n) in cov.toList.toArray.qsort (fun a b => a.1 < b.1) do
    IO.println s!"  {k}: {n}"
  let sec (a b : Tally) := s!"{b.ok - a.ok} ok, {b.fail - a.fail} FAIL"
  IO.println s!"\ncrypto: {sec {} afterCrypto}"
  IO.println s!"zkir reader and round trip: {sec afterCrypto afterZkir}"
  IO.println s!"vectors: {sec afterZkir t}"
  IO.println (if t.fail == 0 then s!"semantics: all {t.ok} checks passed" else s!"semantics: {t.fail} of {t.ok + t.fail} checks FAILED")
  return if t.fail == 0 then 0 else 1
