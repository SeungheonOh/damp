/-
A contract as data, and its JSON form for the executor.

The executor interprets the same circuit IR the ZKIR is emitted from, so the
order and encoding of transcript entries agree with the circuit by construction.
Integers are printed as decimal strings: they do not fit in JSON numbers.
-/
import Lean.Data.Json
import Damp.Lang.Ledger
import Damp.Lang.Calls
import Damp.Compile.Emit
import Damp.Zkir.JsonText

namespace Damp
open Lean (Json)
open IR

structure Contract where
  name : String
  ledger : List LedgerField
  circuits : List Circuit
  /-- Runs once at deployment, after every field has its default value. -/
  constructor : Option Circuit := none
  /-- The contract types (`interface`) the circuits call other contracts through. -/
  interfaces : List Interface := []
  deriving Inhabited

/-- Ledger fields must be declared in index order with no gaps, and every
    cross-contract call must go through a declared contract type, which the
    executor needs to run it. -/
def Contract.check (c : Contract) : Except String Unit := do
  let mut i := 0
  for f in c.ledger do
    unless f.index = i do throw s!"ledger field {f.name} has index {f.index}, expected {i}"
    i := i + 1
  for circ in c.circuits ++ c.constructor.toList do
    for s in circ.body do
      if let .witness _ name _ _ _ := s then
        if name.startsWith "call:" then
          let declared := c.interfaces.any fun i =>
            i.circuits.any fun k => callWitnessName i.name k.name == name
          unless declared do
            throw s!"{circ.name}: {name} is not a circuit of a contract type declared for contract {c.name}"

namespace Export

private def tag (kind : String) (fields : List (String × Json) := []) : Json :=
  Json.mkObj (("kind", Json.str kind) :: fields)

private def int (i : Int) : Json := .str (toString i)
private def nat (n : Nat) : Json := .str (toString n)

def ty : Ty → Json
  | .field => tag "field"
  | .bool => tag "bool"
  | .uint max => tag "uint" [("max", nat max)]
  | .bytes n => tag "bytes" [("length", n)]
  | .enum max => tag "enum" [("max", max)]

def atom : Zkir.AlignAtom → Json
  | .bytes n => tag "bytes" [("length", n)]
  | .field => tag "field"
  | .compress => tag "compress"

mutual
def shape : Shape → Json
  | .prim t => ty t
  | .struct name fieldNames fields =>
      tag "struct" [("name", name), ("fieldNames", .arr (fieldNames.map Json.str).toArray),
        ("fields", .arr (shapes fields).toArray)]
  | .tuple elems => tag "tuple" [("elems", .arr (shapes elems).toArray)]
  | .vector n elem => tag "vector" [("length", n), ("elem", shape elem)]
def shapes : List Shape → List Json
  | [] => []
  | s :: ss => shape s :: shapes ss
end

mutual
def expr : Expr → Json
  | .var v => tag "var" [("var", v)]
  | .const c => tag "const" [("value", int c)]
  | .invalid msg => tag "invalid" [("msg", msg)]
  | .disclose e => expr e
  | .add a b => tag "add" [("a", expr a), ("b", expr b)]
  | .mul a b => tag "mul" [("a", expr a), ("b", expr b)]
  | .neg a => tag "neg" [("a", expr a)]
  | .lt bits a b => tag "lt" [("bits", bits), ("a", expr a), ("b", expr b)]
  | .eq a b => tag "eq" [("a", expr a), ("b", expr b)]
  | .select c a b => tag "select" [("c", expr c), ("a", expr a), ("b", expr b)]
  | .divmod quot bits a => tag "divmod" [("quot", quot), ("bits", bits), ("a", expr a)]
  | .hash xs => tag "hash" [("xs", .arr (exprs xs).toArray)]
  | .phash high align xs =>
      tag "phash" [("high", high), ("align", .arr (align.map atom).toArray), ("xs", .arr (exprs xs).toArray)]
def exprs : List Expr → List Json
  | [] => []
  | x :: xs => expr x :: exprs xs
end

def range : Range → Json
  | .zero => tag "zero"
  | .bool => tag "bool"
  | .bits n => tag "bits" [("n", n)]
  | .below bound width => tag "below" [("bound", nat bound), ("width", width)]

def aligned (v : Impact.Aligned Expr) : Json :=
  Json.mkObj [("align", .arr (v.align.map atom).toArray), ("vals", .arr (v.vals.map expr).toArray)]

mutual
def stateLit : Impact.StateLit Expr → Json
  | .null => tag "null"
  | .cell v => tag "cell" [("value", aligned v)]
  | .emptyMap => tag "map"
  | .array es => tag "array" [("elems", .arr (stateLits es).toArray)]
  | .emptyMerkleTree d => tag "merkleTree" [("depth", d)]
def stateLits : List (Impact.StateLit Expr) → List Json
  | [] => []
  | e :: es => stateLit e :: stateLits es
end

def op : Impact.Op Expr → Json
  | .lt => tag "lt" | .eq => tag "eq" | .type => tag "type" | .size => tag "size"
  | .and => tag "and" | .or => tag "or" | .neg => tag "neg" | .log => tag "log"
  | .root => tag "root" | .pop => tag "pop" | .add => tag "add" | .sub => tag "sub"
  | .member => tag "member" | .ckpt => tag "ckpt"
  | .popeq cached align result =>
      tag "popeq" [("cached", cached), ("align", .arr (align.map atom).toArray),
        ("result", .arr (result.map expr).toArray)]
  | .addi i => tag "addi" [("immediate", expr i)]
  | .subi i => tag "subi" [("immediate", expr i)]
  | .push storage v => tag "push" [("storage", storage), ("value", aligned v)]
  | .pushNull storage => tag "pushNull" [("storage", storage)]
  | .rem cached => tag "rem" [("cached", cached)]
  | .dup n => tag "dup" [("n", n)]
  | .swap n => tag "swap" [("n", n)]
  | .idx cached pushPath path =>
      tag "idx" [("cached", cached), ("pushPath", pushPath), ("path", .arr (path.map aligned).toArray)]
  | .ins cached n => tag "ins" [("cached", cached), ("n", n)]
  | .pushState storage v => tag "pushState" [("storage", storage), ("value", stateLit v)]
  | .branch n => tag "branch" [("skip", n)]
  | .jmp n => tag "jmp" [("skip", n)]
  | .concat n => tag "concat" [("n", n)]
  | .idxStack pre => tag "idxStack" [("path", .arr (pre.map aligned).toArray)]
  | .concatCached n => tag "concatCached" [("n", n)]

def stmt : Stmt → Json
  | .bind v hint e => tag "bind" [("var", v), ("hint", hint), ("expr", expr e)]
  | .assert cond msg => tag "assert" [("cond", expr cond), ("msg", msg)]
  | .constrain e r => tag "constrain" [("expr", expr e), ("range", range r)]
  | .witness guard name args outs sh =>
      tag "witness" [("guard", expr guard), ("name", name), ("args", .arr (args.map expr).toArray),
        ("shape", shape sh),
        ("outs", .arr (outs.map fun (v, r) =>
          Json.mkObj [("var", v), ("range", match r with | some r => range r | none => .null)]).toArray)]
  | .ledger guard reads ops =>
      tag "ledger" [("guard", expr guard), ("reads", .arr (reads.map fun (v : Nat) => (v : Json)).toArray),
        ("ops", .arr (ops.map op).toArray)]

def circuit (c : Circuit) : Json :=
  Json.mkObj [
    ("name", c.name),
    ("proof", c.needsProof),
    ("args", .arr (c.args.map fun (n, sh) => Json.mkObj [("name", n), ("shape", shape sh)]).toArray),
    ("result", shape c.result),
    ("inputs", .arr (c.inputs.map fun i => (i.var : Json)).toArray),
    ("body", .arr (c.body.map stmt)),
    ("outputs", .arr (c.outputs.map expr).toArray)]

def ledgerKind : LedgerKind → Json
  | .cell sh => tag "cell" [("shape", shape sh)]
  | .counter => tag "counter"
  | .map k v => tag "map" [("key", shape k), ("value", shape v)]
  | .mapOf k v => tag "mapOf" [("key", shape k), ("value", ledgerKind v)]
  | .set e => tag "set" [("elem", shape e)]
  | .list e => tag "list" [("elem", shape e)]
  | .merkleTree d e => tag "merkleTree" [("depth", d), ("elem", shape e)]
  | .historicMerkleTree d e => tag "historicMerkleTree" [("depth", d), ("elem", shape e)]

def ledgerField (f : LedgerField) : Json :=
  let kind := ledgerKind f.kind
  Json.mkObj [("name", f.name), ("index", f.index), ("type", kind)]

def interfaceCircuit (k : InterfaceCircuit) : Json :=
  Json.mkObj [
    ("name", k.name),
    ("args", .arr (k.args.map fun (n, sh) => Json.mkObj [("name", n), ("shape", shape sh)]).toArray),
    ("result", shape k.result)]

def «interface» (i : Interface) : Json :=
  Json.mkObj [("name", i.name), ("circuits", .arr (i.circuits.map interfaceCircuit).toArray)]

/-- `interfaces` is written only when there are some, so contracts that call no
    other contract keep their `contract.json` byte for byte. -/
def contract (c : Contract) : Json :=
  Json.mkObj (([
    ("format", "damp-contract/5"),
    ("name", c.name),
    ("ledger", .arr (c.ledger.map ledgerField).toArray),
    ("circuits", .arr (c.circuits.map circuit).toArray),
    ("constructor", match c.constructor with | some k => circuit k | none => .null)] : List (String × Json)) ++
    (if c.interfaces.isEmpty then [] else [("interfaces", Json.arr (c.interfaces.map «interface»).toArray)]))

/-! ## Reading `contract.json` back

`Export.ofJson` reads what `Export.contract` writes. It is total: the readers
of recursive values take fuel, and `ofJson j` gives them `depth j + 1`, more
than the nesting depth of anything inside `j` (`Zkir.Text.depth`).
`contract.json` does not carry everything in a `Contract`: `disclose`
wrappers, the names and ranges of circuit inputs (only their variables are
written) and a circuit's `errors` are not written, so the reader returns the
contract with those erased (`Contract.exported`,
`Damp/Proofs/ExportJson.lean`). The `proof` field of a circuit is derived
(`Circuit.needsProof`) and is not read. -/

namespace Read

abbrev R := Except String

def field (j : Json) (k : String) : R Json := j.getObjVal? k

def arr (j : Json) (k : String) : R (List Json) := do
  match ← field j k with
  | .arr a => pure a.toList
  | _ => throw s!"field {k}: expected an array"

def str (j : Json) (k : String) : R String := do
  match ← field j k with
  | .str s => pure s
  | _ => throw s!"field {k}: expected a string"

def asStr : Json → R String
  | .str s => pure s
  | _ => throw "expected a string"

def num (j : Json) (k : String) : R Nat := do (← field j k).getNat?

def asNum (j : Json) : R Nat := j.getNat?

def bool (j : Json) (k : String) : R Bool := do
  match ← field j k with
  | .bool b => pure b
  | _ => throw s!"field {k}: expected a boolean"

/-- A natural number written as a decimal string. -/
def natStr (j : Json) (k : String) : R Nat := do
  match (← str j k).toNat? with
  | some n => pure n
  | none => throw s!"field {k}: expected a decimal natural number"

/-- An integer written as a decimal string. -/
def intStr (j : Json) (k : String) : R Int := do
  match (← str j k).toInt? with
  | some n => pure n
  | none => throw s!"field {k}: expected a decimal integer"

def kind (j : Json) : R String := str j "kind"

def ty (j : Json) : R Ty := do
  match ← kind j with
  | "field" => pure .field
  | "bool" => pure .bool
  | "uint" => return .uint (← natStr j "max")
  | "bytes" => return .bytes (← num j "length")
  | "enum" => return .enum (← num j "max")
  | k => throw s!"unknown type {k}"

def atom (j : Json) : R Zkir.AlignAtom := do
  match ← kind j with
  | "bytes" => return .bytes (← num j "length")
  | "field" => pure .field
  | "compress" => pure .compress
  | k => throw s!"unknown alignment atom {k}"

def atoms (j : Json) (k : String) : R (List Zkir.AlignAtom) := do (← arr j k).mapM atom

def shape : Nat → Json → R Shape
  | 0, _ => throw "nested too deep"
  | n + 1, j => do
      match ← kind j with
      | "struct" =>
          let name ← str j "name"
          let names ← (← arr j "fieldNames").mapM asStr
          let fields ← (← arr j "fields").mapM (shape n)
          pure (.struct name names fields)
      | "tuple" => return .tuple (← (← arr j "elems").mapM (shape n))
      | "vector" => return .vector (← num j "length") (← shape n (← field j "elem"))
      | _ => .prim <$> ty j

def expr : Nat → Json → R Expr
  | 0, _ => throw "nested too deep"
  | n + 1, j => do
      match ← kind j with
      | "var" => return .var (← num j "var")
      | "const" => return .const (← intStr j "value")
      | "invalid" => return .invalid (← str j "msg")
      | "add" => return .add (← expr n (← field j "a")) (← expr n (← field j "b"))
      | "mul" => return .mul (← expr n (← field j "a")) (← expr n (← field j "b"))
      | "neg" => return .neg (← expr n (← field j "a"))
      | "lt" => return .lt (← num j "bits") (← expr n (← field j "a")) (← expr n (← field j "b"))
      | "eq" => return .eq (← expr n (← field j "a")) (← expr n (← field j "b"))
      | "select" =>
          return .select (← expr n (← field j "c")) (← expr n (← field j "a")) (← expr n (← field j "b"))
      | "divmod" => return .divmod (← bool j "quot") (← num j "bits") (← expr n (← field j "a"))
      | "hash" => return .hash (← (← arr j "xs").mapM (expr n))
      | "phash" => return .phash (← bool j "high") (← atoms j "align") (← (← arr j "xs").mapM (expr n))
      | k => throw s!"unknown expression {k}"

def exprs (n : Nat) (j : Json) (k : String) : R (List Expr) := do (← arr j k).mapM (expr n)

def range (j : Json) : R Range := do
  match ← kind j with
  | "zero" => pure .zero
  | "bool" => pure .bool
  | "bits" => return .bits (← num j "n")
  | "below" => return .below (← natStr j "bound") (← num j "width")
  | k => throw s!"unknown range {k}"

def aligned (n : Nat) (j : Json) : R (Impact.Aligned Expr) := do
  return { align := ← atoms j "align", vals := ← exprs n j "vals" }

def stateLit : Nat → Json → R (Impact.StateLit Expr)
  | 0, _ => throw "nested too deep"
  | n + 1, j => do
      match ← kind j with
      | "null" => pure .null
      | "cell" => return .cell (← aligned n (← field j "value"))
      | "map" => pure .emptyMap
      | "array" => return .array (← (← arr j "elems").mapM (stateLit n))
      | "merkleTree" => return .emptyMerkleTree (← num j "depth")
      | k => throw s!"unknown state literal {k}"

def op (n : Nat) (j : Json) : R (Impact.Op Expr) := do
  match ← kind j with
  | "lt" => pure .lt | "eq" => pure .eq | "type" => pure .type | "size" => pure .size
  | "and" => pure .and | "or" => pure .or | "neg" => pure .neg | "log" => pure .log
  | "root" => pure .root | "pop" => pure .pop | "add" => pure .add | "sub" => pure .sub
  | "member" => pure .member | "ckpt" => pure .ckpt
  | "popeq" => return .popeq (← bool j "cached") (← atoms j "align") (← exprs n j "result")
  | "addi" => return .addi (← expr n (← field j "immediate"))
  | "subi" => return .subi (← expr n (← field j "immediate"))
  | "push" => return .push (← bool j "storage") (← aligned n (← field j "value"))
  | "pushNull" => return .pushNull (← bool j "storage")
  | "rem" => return .rem (← bool j "cached")
  | "dup" => return .dup (← num j "n")
  | "swap" => return .swap (← num j "n")
  | "idx" => return .idx (← bool j "cached") (← bool j "pushPath") (← (← arr j "path").mapM (aligned n))
  | "ins" => return .ins (← bool j "cached") (← num j "n")
  | "pushState" => return .pushState (← bool j "storage") (← stateLit n (← field j "value"))
  | "branch" => return .branch (← num j "skip")
  | "jmp" => return .jmp (← num j "skip")
  | "concat" => return .concat (← num j "n")
  | "idxStack" => return .idxStack (← (← arr j "path").mapM (aligned n))
  | "concatCached" => return .concatCached (← num j "n")
  | k => throw s!"unknown ledger operation {k}"

def witnessOut (j : Json) : R (Var × Option Range) := do
  let v ← num j "var"
  match ← field j "range" with
  | .null => pure (v, none)
  | r => return (v, some (← range r))

def stmt (n : Nat) (j : Json) : R Stmt := do
  match ← kind j with
  | "bind" => return .bind (← num j "var") (← str j "hint") (← expr n (← field j "expr"))
  | "assert" => return .assert (← expr n (← field j "cond")) (← str j "msg")
  | "constrain" => return .constrain (← expr n (← field j "expr")) (← range (← field j "range"))
  | "witness" =>
      return .witness (← expr n (← field j "guard")) (← str j "name") (← exprs n j "args")
        (← (← arr j "outs").mapM witnessOut) (← shape n (← field j "shape"))
  | "ledger" =>
      return .ledger (← expr n (← field j "guard")) (← (← arr j "reads").mapM asNum)
        (← (← arr j "ops").mapM (op n))
  | k => throw s!"unknown statement {k}"

def arg (n : Nat) (j : Json) : R (String × Shape) := return (← str j "name", ← shape n (← field j "shape"))

def input (j : Json) : R Input := return { name := "", var := ← asNum j, range := none }

/-- A circuit; input names and ranges are not written, so each input is read
    with the name `""` and no range. -/
def circuit (n : Nat) (j : Json) : R Circuit := do
  return { name := ← str j "name", args := ← (← arr j "args").mapM (arg n),
           inputs := ← (← arr j "inputs").mapM input, body := (← (← arr j "body").mapM (stmt n)).toArray,
           result := ← shape n (← field j "result"), outputs := ← exprs n j "outputs" }

def ledgerKind : Nat → Json → R LedgerKind
  | 0, _ => throw "nested too deep"
  | n + 1, j => do
      match ← kind j with
      | "cell" => return .cell (← shape n (← field j "shape"))
      | "counter" => pure .counter
      | "map" => return .map (← shape n (← field j "key")) (← shape n (← field j "value"))
      | "mapOf" => return .mapOf (← shape n (← field j "key")) (← ledgerKind n (← field j "value"))
      | "set" => return .set (← shape n (← field j "elem"))
      | "list" => return .list (← shape n (← field j "elem"))
      | "merkleTree" => return .merkleTree (← num j "depth") (← shape n (← field j "elem"))
      | "historicMerkleTree" => return .historicMerkleTree (← num j "depth") (← shape n (← field j "elem"))
      | k => throw s!"unknown ledger kind {k}"

def ledgerField (n : Nat) (j : Json) : R LedgerField :=
  return { name := ← str j "name", index := ← num j "index", kind := ← ledgerKind n (← field j "type") }

def interfaceCircuit (n : Nat) (j : Json) : R InterfaceCircuit :=
  return { name := ← str j "name", args := ← (← arr j "args").mapM (arg n), result := ← shape n (← field j "result") }

def «interface» (n : Nat) (j : Json) : R Interface :=
  return { name := ← str j "name", circuits := ← (← arr j "circuits").mapM (interfaceCircuit n) }

def constructor (n : Nat) : Json → R (Option Circuit)
  | .null => pure none
  | k => some <$> circuit n k

def interfaces (n : Nat) (j : Json) : R (List Interface) :=
  match j.getObjVal? "interfaces" with
  | .ok (.arr a) => a.toList.mapM («interface» n)
  | .ok _ => throw "interfaces: expected an array"
  | .error _ => pure []

/-- A contract, with fuel `n`. -/
def contract (n : Nat) (j : Json) : R Contract := do
  unless (← str j "format") == "damp-contract/5" do throw "unsupported contract format"
  return { name := ← str j "name", ledger := ← (← arr j "ledger").mapM (ledgerField n),
           circuits := ← (← arr j "circuits").mapM (circuit n),
           constructor := ← constructor n (← field j "constructor"), interfaces := ← interfaces n j }

end Read

/-- Read `contract.json` (as a JSON value): the inverse of `Export.contract`, up
    to what the file does not carry (`Contract.exported`). -/
def ofJson (j : Json) : Except String Contract := Read.contract (Zkir.Text.depth j + 1) j

/-- Read the text of `contract.json` with Damp's reference JSON parser. -/
def parse (text : String) : Except String Contract := do ofJson (← Zkir.Text.parse text)

theorem tag_eq (kind : String) (fields : List (String × Json)) :
    tag kind fields = Json.mkObj (("kind", Json.str kind) :: fields) := rfl
theorem int_eq (i : Int) : int i = .str (toString i) := rfl
theorem nat_eq (n : Nat) : nat n = .str (toString n) := rfl

end Export

/-- Every circuit of a contract, the constructor last. -/
def Contract.allCircuits (c : Contract) : List Circuit := c.circuits ++ c.constructor.toList

/-- What `Contract.write` computes before writing anything: `Contract.check`,
    then `Emit.circuit` on every circuit, failing on the first error. Returns
    each circuit with its emitted ZKIR. -/
def Contract.emitAll (c : Contract) : Except String (List (Circuit × Zkir.IrSource)) := do
  c.check
  (c.circuits ++ c.constructor.toList).mapM fun circ =>
    match Emit.circuit circ with
    | .ok src => pure (circ, src)
    | .error e => throw s!"{c.name}.{circ.name}: {e}"

/-- The `.zkir` files written for emitted circuits: file name and contents, for
    each circuit that needs a proof other than the constructor (every circuit
    is emitted and checked either way). -/
def zkirFiles (srcs : List (Circuit × Zkir.IrSource)) : List (String × String) :=
  srcs.filterMap fun (circ, src) =>
    if circ.needsProof && circ.name != "constructor" then
      some (s!"{circ.name}.zkir", src.toJson.pretty ++ "\n")
    else none

/-- Write the files for a contract and its emitted circuits:
    `zkir/<circuit>.zkir` (`zkirFiles`) and `contract.json` for the executor. -/
def Contract.writeFiles (c : Contract) (dir : System.FilePath) (srcs : List (Circuit × Zkir.IrSource)) :
    IO Unit := do
  IO.FS.createDirAll (dir / "zkir")
  for (name, text) in zkirFiles srcs do
    IO.FS.writeFile (dir / "zkir" / name) text
  IO.FS.writeFile (dir / "contract.json") ((Export.contract c).pretty ++ "\n")

/-- Write `zkir/<circuit>.zkir` for each circuit and `contract.json` for the
    executor: `Contract.emitAll`, then `Contract.writeFiles`. -/
def Contract.write (c : Contract) (dir : System.FilePath) : IO Unit := do
  let srcs ← IO.ofExcept c.emitAll
  c.writeFiles dir srcs

end Damp
