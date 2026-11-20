/-
JSON text: a total reference lexer, parser and printer for the JSON Damp writes.

Everything Damp ships is JSON text: each `.zkir` file is
`src.toJson.pretty ++ "\n"` and `contract.json` is `(Export.contract c).pretty ++ "\n"`.
Lean core's printer and parser of JSON text (`Json.pretty`, `Json.compress`,
`Json.parse`) are `partial` definitions, so nothing can be proved about what
they compute. This file gives total definitions of the same layer:

* `Text.toks j` — the token sequence of `j`, in the order `Json.pretty`
  prints it (array elements in order; object members in *descending* key
  order, which is the order `Json.render` produces: it folds the members
  ascending and conses each onto a list);
* `Text.render j` — those tokens without whitespace, strings escaped exactly
  as `Json.renderString` escapes them;
* `Text.lex` — a lexer that skips JSON whitespace (space, tab, newline,
  carriage return) between tokens, as `Json.parse` does;
* `Text.parseToks` — a recursive-descent parser over tokens that builds an
  object by inserting its members in text order and rejects duplicate keys,
  as `Json.parse` does;
* `Text.parse = Text.lex >=> Text.parseToks`.

Scope (`Text.frag`): numbers must be natural numbers with exponent 0 (what
`(n : Json)` builds; Damp writes no other numbers) and object keys must be
distinct. Strings are unrestricted. Outside that fragment the reference parser
is deliberately narrower than `Json.parse`: it rejects negative numbers,
fractions, exponents and leading zeros, and `\u` escapes of surrogate code
points (which `Json.parse` combines into pairs or replaces by U+FFFD).

`Damp/Proofs/JsonText.lean` proves the round trip; `test/jsontext.sh` checks on
every emitted file, and on random values, that `Json.pretty`'s output lexes to
`Text.toks` and that `Text.parse` and `Json.parse` agree.

Total: no `partial`, no `sorry`.
-/
import Lean.Data.Json
import Damp.Zkir.Json

namespace Damp.Zkir.Text
open Lean (Json JsonNumber)
open Std.DTreeMap.Internal (Impl)

/-- A JSON token. -/
inductive Tok where
  | lbrace | rbrace | lbrack | rbrack | colon | comma
  | str (s : String)
  | num (n : Nat)
  | tru | fls | null
  deriving DecidableEq, Repr, Inhabited

/-! ## Printing -/

/-- One character of a string body, escaped as `Json.renderString` escapes it
    (`escapeAux` in Lean core's `Lean/Data/Json/Printer.lean`). -/
def escChar (c : Char) : List Char :=
  if c = '"' then ['\\', '"']
  else if c = '\\' then ['\\', '\\']
  else if c = '\n' then ['\\', 'n']
  else if c = '\x0d' then ['\\', 'r']
  else if 0x20 ≤ c.val then [c]
  else
    let n := c.toNat
    ['\\', 'u', Nat.digitChar (n / 4096), Nat.digitChar ((n % 4096) / 256),
      Nat.digitChar ((n % 256) / 16), Nat.digitChar (n % 16)]

/-- The text of one token. -/
def Tok.text : Tok → List Char
  | .lbrace => ['{'] | .rbrace => ['}'] | .lbrack => ['['] | .rbrack => [']']
  | .colon => [':'] | .comma => [',']
  | .str s => '"' :: (s.toList.flatMap escChar ++ ['"'])
  | .num n => Nat.toDigits 10 n
  | .tru => "true".toList | .fls => "false".toList | .null => "null".toList

/-- Token groups separated by commas. -/
def sepBy : List (List Tok) → List Tok
  | [] => []
  | [g] => g
  | g :: gs => g ++ .comma :: sepBy gs

/-- The members of an object: `"key" : value`. -/
def member (k : String) (v : List Tok) : List Tok := .str k :: .colon :: v

/-- The tree of an object's members. -/
abbrev Tree := Impl String (fun _ => Json)

mutual
/-- The tokens of a JSON value, in the order `Json.pretty` prints them. -/
def toks : Json → List Tok
  | .null => [.null]
  | .bool true => [.tru]
  | .bool false => [.fls]
  | .num n => [.num n.mantissa.toNat]
  | .str s => [.str s]
  | .arr ⟨l⟩ => .lbrack :: (sepBy (toksL l) ++ [.rbrack])
  | .obj ⟨⟨t⟩⟩ => .lbrace :: (sepBy ((toksT t).map fun p => member p.1 p.2) ++ [.rbrace])
def toksL : List Json → List (List Tok)
  | [] => []
  | j :: l => toks j :: toksL l
/-- Members in descending key order (right subtree first). -/
def toksT : Tree → List (String × List Tok)
  | .leaf => []
  | .inner _ k v l r => toksT r ++ (k, toks v) :: toksT l
end

/-- Compact text of a value. -/
def render (j : Json) : String := String.ofList ((toks j).flatMap Tok.text)

/-! ## The fragment -/

mutual
/-- The values the round trip is about: every number a natural number with
    exponent 0, every object without repeated keys. -/
def frag : Json → Bool
  | .null | .bool _ | .str _ => true
  | .num n => decide (0 ≤ n.mantissa ∧ n.exponent = 0)
  | .arr ⟨l⟩ => fragL l
  | .obj ⟨⟨t⟩⟩ => decide ((Impl.Const.toList t).map Prod.fst).Nodup && fragT t
def fragL : List Json → Bool
  | [] => true
  | j :: l => frag j && fragL l
def fragT : Tree → Bool
  | .leaf => true
  | .inner _ _ v l r => fragT l && frag v && fragT r
end

/-! ## What reading the text back gives

`Json.parse` builds an object by inserting its members into an empty tree in
the order the text lists them; `reorder j` is `j` with every object rebuilt
that way, from the order `toks` lists the members in. It has the same members
(`Damp/Proofs/JsonText.lean`); only the shape of the balanced tree can
differ. -/

mutual
def reorder : Json → Json
  | .arr ⟨l⟩ => .arr ⟨reorderL l⟩
  | .obj ⟨⟨t⟩⟩ => Json.mkObj (reorderT t)
  | j => j
def reorderL : List Json → List Json
  | [] => []
  | j :: l => reorder j :: reorderL l
def reorderT : Tree → List (String × Json)
  | .leaf => []
  | .inner _ k v l r => reorderT r ++ (k, reorder v) :: reorderT l
end

/-! ## Depth

The nesting depth of a value; readers that descend into a value recurse on it
(`Export.ofJson`, `Damp/Compile/Export.lean`). -/

mutual
def depth : Json → Nat
  | .arr ⟨l⟩ => depthL l + 1
  | .obj ⟨⟨t⟩⟩ => depthT t + 1
  | _ => 0
def depthL : List Json → Nat
  | [] => 0
  | j :: l => max (depth j) (depthL l)
def depthT : Tree → Nat
  | .leaf => 0
  | .inner _ _ v l r => max (depthT l) (max (depth v) (depthT r))
end

theorem depth_le_depthL : ∀ (l : List Json) (j : Json), j ∈ l → depth j ≤ depthL l
  | [], _, h => absurd h List.not_mem_nil
  | x :: l, j, h => by
      rw [depthL]
      rcases List.mem_cons.mp h with rfl | h
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (depth_le_depthL l j h) (Nat.le_max_right _ _)

/-- An element of an array is shallower than the array. -/
theorem depth_lt_arr (a : Array Json) (j : Json) (h : j ∈ a.toList) : depth j < depth (.arr a) := by
  obtain ⟨l⟩ := a
  rw [depth]
  exact Nat.lt_succ_of_le (depth_le_depthL l j h)

theorem depth_le_get? : ∀ (t : Tree) (k : String) (v : Json),
    @Impl.Const.get? String Json ⟨compare⟩ t k = some v → depth v ≤ depthT t
  | .leaf, _, _, h => by simp [Impl.Const.get?] at h
  | .inner _ k' v' l r, k, v, h => by
      rw [depthT]
      unfold Impl.Const.get? at h
      split at h
      · exact Nat.le_trans (depth_le_get? l k v h) (Nat.le_max_left _ _)
      · exact Nat.le_trans (depth_le_get? r k v h)
          (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
      · cases h
        exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

/-- A field of an object is shallower than the object. -/
theorem depth_lt_getObjVal? (j : Json) (k : String) (v : Json) (h : j.getObjVal? k = .ok v) :
    depth v < depth j := by
  match j, h with
  | .obj ⟨⟨t⟩⟩, h =>
      rw [depth]
      simp only [Json.getObjVal?] at h
      split at h
      · rename_i v' hv
        cases h
        exact Nat.lt_succ_of_le (depth_le_get? t k _ hv)
      · cases h

/-! ## Lexing -/

def isWs (c : Char) : Bool := c = ' ' || c = '\t' || c = '\n' || c = '\x0d'

inductive LexSt where
  | top
  /-- Inside a string; the characters so far, last first. -/
  | str (acc : List Char)
  /-- After a backslash inside a string. -/
  | esc (acc : List Char)
  /-- Inside `\uXXXX`: `k ≥ 1` hex digits to go, value so far `v`. -/
  | uni (acc : List Char) (k : Nat) (v : Nat)
  /-- Inside a number; the digits so far, last first. -/
  | num (ds : List Char)
  /-- Inside `true`/`false`/`null`: the characters still expected (never empty). -/
  | kw (rest : List Char) (t : Tok)

def LexSt.rank : LexSt → Nat
  | .top => 0
  | _ => 1

/-- A number from its digits (first first); a leading zero is refused. -/
def finishNum (ds : List Char) : Except String Tok :=
  match ds with
  | '0' :: _ :: _ => .error "number with a leading zero"
  | _ => .ok (.num (Nat.ofDigitChars 10 ds 0))

/-- The character `\uXXXX` denotes, if it is not a surrogate. -/
def uniChar (v : Nat) : Except String Char :=
  if 0xD800 ≤ v ∧ v < 0xE000 then .error "\\u escape of a surrogate code point"
  else .ok (Char.ofNat v)

/-- The lexer: state, input, tokens so far (last first). -/
def lexGo : LexSt → List Char → List Tok → Except String (List Tok)
  | .top, [], out => .ok out.reverse
  | .top, c :: cs, out =>
      if isWs c then lexGo .top cs out
      else if c = '{' then lexGo .top cs (.lbrace :: out)
      else if c = '}' then lexGo .top cs (.rbrace :: out)
      else if c = '[' then lexGo .top cs (.lbrack :: out)
      else if c = ']' then lexGo .top cs (.rbrack :: out)
      else if c = ':' then lexGo .top cs (.colon :: out)
      else if c = ',' then lexGo .top cs (.comma :: out)
      else if c = '"' then lexGo (.str []) cs out
      else if c.isDigit then lexGo (.num [c]) cs out
      else if c = 't' then lexGo (.kw ['r', 'u', 'e'] .tru) cs out
      else if c = 'f' then lexGo (.kw ['a', 'l', 's', 'e'] .fls) cs out
      else if c = 'n' then lexGo (.kw ['u', 'l', 'l'] .null) cs out
      else .error s!"unexpected character {c}"
  | .str _, [], _ => .error "unterminated string"
  | .str acc, c :: cs, out =>
      if c = '"' then lexGo .top cs (.str (String.ofList acc.reverse) :: out)
      else if c = '\\' then lexGo (.esc acc) cs out
      else if c.val < 0x20 then .error "control character in string"
      else lexGo (.str (c :: acc)) cs out
  | .esc _, [], _ => .error "unterminated string"
  | .esc acc, c :: cs, out =>
      if c = '"' then lexGo (.str ('"' :: acc)) cs out
      else if c = '\\' then lexGo (.str ('\\' :: acc)) cs out
      else if c = '/' then lexGo (.str ('/' :: acc)) cs out
      else if c = 'b' then lexGo (.str ('\x08' :: acc)) cs out
      else if c = 'f' then lexGo (.str ('\x0c' :: acc)) cs out
      else if c = 'n' then lexGo (.str ('\n' :: acc)) cs out
      else if c = 'r' then lexGo (.str ('\x0d' :: acc)) cs out
      else if c = 't' then lexGo (.str ('\t' :: acc)) cs out
      else if c = 'u' then lexGo (.uni acc 4 0) cs out
      else .error "invalid escape"
  | .uni _ _ _, [], _ => .error "unterminated string"
  | .uni acc k v, c :: cs, out =>
      match hexDigit c with
      | none => .error "invalid \\u escape"
      | some d =>
          if k ≤ 1 then
            match uniChar (16 * v + d) with
            | .ok ch => lexGo (.str (ch :: acc)) cs out
            | .error e => .error e
          else lexGo (.uni acc (k - 1) (16 * v + d)) cs out
  | .num ds, [], out =>
      match finishNum ds.reverse with
      | .ok t => lexGo .top [] (t :: out)
      | .error e => .error e
  | .num ds, c :: cs, out =>
      if c.isDigit then lexGo (.num (c :: ds)) cs out
      else match finishNum ds.reverse with
        | .ok t => lexGo .top (c :: cs) (t :: out)
        | .error e => .error e
  | .kw _ _, [], _ => .error "unexpected end of input"
  | .kw rest t, c :: cs, out =>
      match rest with
      | [] => .error "unexpected keyword state"
      | [x] => if c = x then lexGo .top cs (t :: out) else .error s!"unexpected character {c}"
      | x :: y :: xs => if c = x then lexGo (.kw (y :: xs) t) cs out else .error s!"unexpected character {c}"
termination_by st cs => 2 * cs.length + st.rank
decreasing_by all_goals simp only [List.length_cons, LexSt.rank]; omega

def lex (s : String) : Except String (List Tok) := lexGo .top s.toList []

/-! ## Parsing tokens -/

mutual
/-- A value, with fuel; returns what follows it. -/
def pVal : Nat → List Tok → Except String (Json × List Tok)
  | 0, _ => .error "nesting too deep"
  | _ + 1, [] => .error "unexpected end of input"
  | n + 1, t :: ts =>
      match t with
      | .null => .ok (.null, ts)
      | .tru => .ok (.bool true, ts)
      | .fls => .ok (.bool false, ts)
      | .num k => .ok ((k : Json), ts)
      | .str s => .ok (.str s, ts)
      | .lbrack =>
          match ts with
          | .rbrack :: ts => .ok (.arr ⟨[]⟩, ts)
          | _ =>
              match pElems n ts with
              | .ok (vs, ts) => .ok (.arr ⟨vs⟩, ts)
              | .error e => .error e
      | .lbrace =>
          match ts with
          | .rbrace :: ts => .ok (Json.mkObj [], ts)
          | _ =>
              match pMembers n ts with
              | .ok (kvs, ts) =>
                  if (kvs.map Prod.fst).Nodup then .ok (Json.mkObj kvs, ts)
                  else .error "duplicate object key"
              | .error e => .error e
      | _ => .error "unexpected token"
/-- Array elements after `[`, through the closing `]`. -/
def pElems : Nat → List Tok → Except String (List Json × List Tok)
  | 0, _ => .error "nesting too deep"
  | n + 1, ts =>
      match pVal n ts with
      | .ok (v, .comma :: ts) =>
          match pElems n ts with
          | .ok (vs, ts) => .ok (v :: vs, ts)
          | .error e => .error e
      | .ok (v, .rbrack :: ts) => .ok ([v], ts)
      | .ok _ => .error "expected , or ]"
      | .error e => .error e
/-- Object members after `{`, through the closing `}`. -/
def pMembers : Nat → List Tok → Except String (List (String × Json) × List Tok)
  | 0, _ => .error "nesting too deep"
  | n + 1, .str k :: .colon :: ts =>
      match pVal n ts with
      | .ok (v, .comma :: ts) =>
          match pMembers n ts with
          | .ok (kvs, ts) => .ok ((k, v) :: kvs, ts)
          | .error e => .error e
      | .ok (v, .rbrace :: ts) => .ok ([(k, v)], ts)
      | .ok _ => .error "expected , or }"
      | .error e => .error e
  | _ + 1, _ => .error "expected a member"
end

def parseToks (ts : List Tok) : Except String Json :=
  match pVal (ts.length + 1) ts with
  | .ok (v, []) => .ok v
  | .ok _ => .error "trailing tokens"
  | .error e => .error e

/-- Parse JSON text (the reference parser). -/
def parse (s : String) : Except String Json := do
  parseToks (← lex s)

end Damp.Zkir.Text
