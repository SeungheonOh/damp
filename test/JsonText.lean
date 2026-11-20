/-
Differential test of the JSON text layer (run by test/jsontext.sh).

`Damp/Proofs/JsonText.lean` and `Damp/Proofs/ZkirText.lean` prove that Damp's
total reference parser `Zkir.Text.parse` reads back any text that lexes as
`Zkir.Text.toks j`. What is written to disk is Lean core's `Json.pretty`, and
the reader Lean code uses is `Json.parse`; both are `partial`, so they are
tested here instead:

  files   for every `.zkir` and `contract.json` under the given directories:
          the text is in the fragment (`Text.frag`), it lexes as the tokens of
          the value `Json.parse` reads from it (the theorems' hypothesis), the
          reference parser and `Json.parse` read the same value, and for a
          `.zkir` file both readings give the same `IrSource`, whose tokens
          the text lexes as (`IrSource.ofText`'s hypothesis, with `src` the
          circuit read back);
  random  random values of the fragment (strings over quotes, backslashes,
          control characters, non-ASCII and astral characters; numbers up to
          2^300; nested arrays and objects): `Json.pretty` at several widths
          and `Json.compress` lex as their tokens (compress up to member
          order) and both parsers read back the value;
  mutated random edits of those texts (no `-`, `.`, `e`, `E` or `u` inserted,
          which lead outside the fragment): both parsers accept or both
          reject, and agree when they accept.

usage: lake env lean --run test/JsonText.lean DIR... [--random N]
-/
import Damp.Compile.Export

open Lean (Json)
open Damp.Zkir

/-- Same value: both in the fragment and the same tokens (member order is the
    tree's key order, so this ignores only the shape of the balanced tree). -/
def same (a b : Json) : Bool := Text.frag a && Text.frag b && Text.toks a == Text.toks b

def lexIs (t : String) (ts : List Text.Tok) : Bool :=
  match Text.lex t with
  | .ok x => x == ts
  | .error _ => false

structure Rng where
  s : Nat
  deriving Inhabited

def Rng.next (r : Rng) : Nat × Rng :=
  let s := (r.s * 6364136223846793005 + 1442695040888963407) % (1 <<< 64)
  (s / (1 <<< 33), ⟨s⟩)

def Rng.below (r : Rng) (n : Nat) : Nat × Rng :=
  let (x, r) := r.next
  (x % (max n 1), r)

def pool : Array Char :=
  #['a', 'b', 'z', 'A', '0', '9', ' ', '%', '.', '<', '>', '"', '\\', '/', '\n', '\r', '\t',
    '\x00', '\x01', '\x1f', '\x7f', 'é', '€', ' ', '😀', '{', '}', '[', ']', ':', ',']

def genStr (r : Rng) : String × Rng := Id.run do
  let (n, r) := r.below 8
  let mut r := r
  let mut s := ""
  for _ in [0:n] do
    let (i, r') := r.below pool.size
    r := r'
    s := s.push pool[i]!
  (s, r)

def genNat (r : Rng) : Nat × Rng :=
  let (k, r) := r.below 4
  match k with
  | 0 => r.below 10
  | 1 => r.below 100000
  | 2 => let (a, r) := r.next; let (b, r) := r.next; (a * (1 <<< 31) + b, r)
  | _ => let (a, r) := r.next; (a * (1 <<< 270) + 12345, r)

partial def gen (d : Nat) (r : Rng) : Json × Rng := Id.run do
  let (k, r) := r.below (if d == 0 then 5 else 9)
  if k == 0 then return (.null, r)
  if k == 1 then let (b, r) := r.below 2; return (.bool (b == 1), r)
  if k == 2 then let (n, r) := genNat r; return ((n : Json), r)
  if k ≤ 4 then let (s, r) := genStr r; return (.str s, r)
  let (n, r) := r.below 5
  let mut r := r
  if k ≤ 6 then
    let mut xs : Array Json := #[]
    for _ in [0:n] do
      let (x, r') := gen (d - 1) r
      r := r'
      xs := xs.push x
    return (.arr xs, r)
  let mut kvs : List (String × Json) := []
  for _ in [0:n] do
    let (key, r') := genStr r
    let (x, r'') := gen (d - 1) r'
    r := r''
    unless kvs.any (·.1 == key) do kvs := kvs ++ [(key, x)]
  return (Json.mkObj kvs, r)

def mutate (t : String) (r : Rng) : String × Rng := Id.run do
  let cs := t.toList.toArray
  let (k, r) := r.below 3
  let (i, r) := r.below (cs.size + 1)
  let ins : Array Char := #[' ', ',', ':', '"', '\\', '[', ']', '{', '}', '0', '7', 'n', 't', 'f', 'x', '\n']
  let (c, r) := r.below ins.size
  let cs := match k with
    | 0 => cs.eraseIdxIfInBounds i
    | 1 => cs.insertIdxIfInBounds i ins[c]!
    | _ => if i < cs.size then cs.set! i ins[c]! else cs
  (String.ofList cs.toList, r)

/-- Both parsers on one text: `none` if they agree, else a description. -/
def agree (t : String) : Option String :=
  match Json.parse t, Text.parse t with
  | .ok a, .ok b => if same a b then none else some "different values"
  | .error _, .error _ => none
  | .ok _, .error e => some s!"only Json.parse accepts ({e})"
  | .error e, .ok _ => some s!"only Text.parse accepts ({e})"

partial def files (p : System.FilePath) : IO (Array System.FilePath) := do
  if ← p.isDir then
    let mut out := #[]
    for e in ← p.readDir do
      out := out ++ (← files e.path)
    return out
  else if p.extension == some "zkir" || p.fileName == some "contract.json" then
    return #[p]
  else return #[]

def checkFile (p : System.FilePath) : IO (Option String) := do
  let t ← IO.FS.readFile p
  let some j := (Json.parse t).toOption | return some "Json.parse fails"
  unless Text.frag j do return some "not in the fragment"
  unless lexIs t (Text.toks j) do return some "text does not lex as the tokens of its value"
  if let some e := agree t then return some e
  if p.extension == some "zkir" then
    match IrSource.ofJson j, (Text.parse t >>= IrSource.ofJson) with
    | .ok s, .ok s' =>
        unless s.toJson.compress == s'.toJson.compress do return some "readers give different circuits"
        unless lexIs t (Text.toks s.toJson) do return some "text does not lex as the circuit's tokens"
    | _, _ => return some "IrSource.ofJson fails"
  else
    -- contract.json: Damp's reader on both readings of the text.
    match Damp.Export.ofJson j, Damp.Export.parse t with
    | .ok c, .ok c' =>
        unless (Damp.Export.contract c).compress == (Damp.Export.contract c').compress do
          return some "contract readers differ"
        unless (Damp.Export.contract c).compress == j.compress do
          return some "contract read back does not print as the file"
    | .error e, _ => return some s!"Export.ofJson fails: {e}"
    | _, .error e => return some s!"Export.parse fails: {e}"
  return none

def main (args : List String) : IO UInt32 := do
  let (dirs, n) := match args.reverse with
    | k :: "--random" :: rest => (rest.reverse, k.toNat!)
    | _ => (args, 2000)
  let mut bad := 0
  let mut nfiles := 0
  let mut nzkir := 0
  for d in dirs do
    for p in ← files d do
      nfiles := nfiles + 1
      if p.extension == some "zkir" then nzkir := nzkir + 1
      if let some e := ← checkFile p then
        IO.println s!"FAIL {p}: {e}"
        bad := bad + 1
  IO.println s!"files: {nfiles} ({nzkir} .zkir), {bad} failures"
  let mut r : Rng := ⟨20261119⟩
  let mut rbad := 0
  let mut mut_agree := 0
  let mut mut_ok := 0
  for i in [0:n] do
    let (j, r') := gen 4 r
    r := r'
    let texts := [j.pretty, j.pretty 10, j.pretty 200, Text.render j]
    for t in texts do
      unless lexIs t (Text.toks j) do
        IO.println s!"FAIL random {i}: pretty/render text does not lex as its tokens: {t}"; rbad := rbad + 1
      match Json.parse t, Text.parse t with
      | .ok a, .ok b =>
          unless same a j && same b j do IO.println s!"FAIL random {i}: read back differs: {t}"; rbad := rbad + 1
      | _, _ => IO.println s!"FAIL random {i}: a parser rejects: {t}"; rbad := rbad + 1
    -- compress lists members ascending: its tokens are `toks` up to member order.
    match Json.parse j.compress, Text.parse j.compress with
    | .ok a, .ok b => unless same a j && same b j do IO.println s!"FAIL random {i}: compress"; rbad := rbad + 1
    | _, _ => IO.println s!"FAIL random {i}: compress rejected"; rbad := rbad + 1
    for _ in [0:5] do
      let (t, r') := mutate j.pretty r
      r := r'
      match agree t with
      | none =>
          mut_agree := mut_agree + 1
          if (Json.parse t).isOk then mut_ok := mut_ok + 1
      | some e => IO.println s!"FAIL mutated {i}: {e}: {t.quote}"; rbad := rbad + 1
  IO.println s!"random: {n} values, 4 texts each and compress; {mut_agree} mutated texts agreed ({mut_ok} accepted by both); {rbad} failures"
  return if bad + rbad == 0 then 0 else 1
