import Damp

/-! The caller of `Examples/Calls.lean`, twice: once with the declaration
syntax (`interface`, `ledger`, `constructor`, `circuit`, `contract`) and once
without it, as the plain definitions that syntax stands for. The two compile
to the same circuits, which the checks at the end confirm.

The second version is what a proof about a contract is really about: a
`CircuitM` function, the `IR.Circuit` built from it by `mkCircuit`, and a
`Contract` value listing the circuits. -/

namespace Examples.CallsPlain
open Damp

/-! ## With the syntax -/

namespace Sugar

interface Adder where
  addTo (x : Field) : Field
  clear : Unit

ledger
  adder : Cell Adder

constructor (a : Adder) := adder.write (disclose a)

circuit bump (x : Field) : Field := do
  const r ← (← adder.read).addTo (disclose x)
  return r

contract caller

end Sugar

/-! ## Without it -/

namespace Plain

/-! `interface Adder where …`: a reference to a contract is its address. -/

structure Adder where
  bytes : Bytes 32
  deriving Inhabited

instance : Value Adder where
  shape := .struct "Adder" ["bytes"] [.prim (.bytes 32)]
  toExprs a := a.bytes.limbs
  ofExprs xs := ⟨⟨xs.take (IR.byteLimbs 32)⟩⟩

instance : CmpEq Adder Adder := ⟨valueEq⟩

/-- The contract type as data: what the executor checks a callee against. -/
def Adder.declaration : Interface :=
  { name := "Adder"
    circuits := [
      { name := "addTo", args := [("x", Value.shape Field)], result := Value.shape Field },
      { name := "clear", args := [], result := Value.shape Unit } ] }

def Adder.ofAddress (b : Bytes 32) : Adder := ⟨b⟩
def Adder.address (r : Adder) : Bytes 32 := r.bytes
instance : ContractType Adder := ⟨Adder.declaration, Adder.ofAddress, Adder.address⟩

/-- One method per declared circuit; the call itself is `contractCall`. -/
def Adder.addTo (self : Adder) (x : Field) : CircuitM Field :=
  contractCall Field "Adder" "addTo" self.bytes.limbs (Value.toExprs x)

def Adder.clear (self : Adder) : CircuitM Unit :=
  contractCall Unit "Adder" "clear" self.bytes.limbs []

/-! `ledger`: fields are numbered in order. -/

def adder : Cell Adder := LedgerType.ofIndex 0
def ledgerFields : List LedgerField := [LedgerType.decl adder "adder"]

/-! `constructor`. -/

def constructorBody (a : Adder) : CircuitM Unit := adder.write (disclose a)
def constructorCircuit : IR.Circuit := mkCircuit "constructor" ["a"] constructorBody

/-! `circuit bump`: `const r ← e` is `let r ← valM e "r"`. -/

def bump (x : Field) : CircuitM Field := do
  let r ← valM ((← adder.read).addTo (disclose x)) "r"
  return r

def bump.circuit : IR.Circuit := mkCircuit "bump" ["x"] bump

/-! `contract caller`. (`contract` is a keyword once `Damp` is imported.) -/

def «contract» : Contract :=
  ⟨"caller", ledgerFields, [bump.circuit], some constructorCircuit, [Adder.declaration]⟩

end Plain

/-! ## They are the same -/

/-- The ZKIR emitted for a circuit, or why there is none. -/
private def emitted (c : IR.Circuit) : String :=
  match Emit.circuit c with
  | .ok src => src.toJson.pretty
  | .error e => s!"error: {e}"

-- What `circuit` checks in the editor: both circuits compile.
#guard circuitProblem Plain.bump.circuit == none
#guard circuitProblem Plain.constructorCircuit == none
-- The same ZKIR, and the same `contract.json`.
#guard emitted Plain.bump.circuit == emitted Sugar.bump.circuit
#guard (Export.contract Plain.contract).pretty == (Export.contract Sugar.contract).pretty

end Examples.CallsPlain
