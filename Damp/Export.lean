/-
A contract as data, and its JSON form for the executor.

The executor interprets the same circuit IR the ZKIR is emitted from, so the
order and encoding of transcript entries agree with the circuit by construction.
Integers are printed as decimal strings: they do not fit in JSON numbers.
-/
import Lean.Data.Json
import Damp.Ledger
import Damp.Calls
import Damp.Emit

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

end Export

/-- Write `zkir/<circuit>.zkir` for each circuit and `contract.json` for the executor. -/
def Contract.write (c : Contract) (dir : System.FilePath) : IO Unit := do
  IO.ofExcept c.check
  IO.FS.createDirAll (dir / "zkir")
  for circ in c.circuits ++ c.constructor.toList do
    match Emit.circuit circ with
    | .ok src =>
        -- Checked either way; written only where a proof is needed.
        if circ.needsProof && circ.name != "constructor" then
          IO.FS.writeFile (dir / "zkir" / s!"{circ.name}.zkir") (src.toJson.pretty ++ "\n")
    | .error e => throw (IO.userError s!"{c.name}.{circ.name}: {e}")
  IO.FS.writeFile (dir / "contract.json") ((Export.contract c).pretty ++ "\n")

end Damp
