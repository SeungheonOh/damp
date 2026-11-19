/-
Cross-contract calls: a circuit of one contract calling a circuit of another.

In Compact, a *contract type* (`contract Adder { circuit addTo(x: Field): Field; }`)
declares the circuits of another contract; a value of that type is the address
of a deployed contract, and `adder.addTo(x)` calls it. compactc 0.36.1 compiles
the call into

* two `private_input`s: the callee's results, then a random opening;
* `transient_hash [opening, arguments…, results…]`, the *communication
  commitment*, which the callee's own proof commits to as well;
* `kernel.claimContractCall(address, entryPoint, commitment)`: the kernel
  operation that records, among the transaction's effects, that this call was
  made, so the ledger can require a matching call transcript of the callee.

None of this needs a new kind of statement. The callee's results and the
opening are what a witness is: values the prover supplies, which the circuit
range-checks and binds by the commitment. So a call is, in the IR, a `witness`
statement with a reserved name (`call:<Interface>.<circuit>`) whose arguments
are the callee's address and the call's arguments, a `bind` of the transient
hash, and a `ledger` statement for the kernel operation. The emitter, the
optimizer and the executor's definition treat it as they treat those, and
their theorems cover it unchanged. The executor answers the witness itself, by
running the callee (`executor/src/executor.mjs`, `callWitness`).

The entry point is not a circuit name but its hash, `entryPoint` below; it is
computed while the circuit is built. `docs/calls.md` has the evidence for each
part.
-/
import Damp.Lang.Ledger
import Damp.Crypto.Sha256

namespace Damp
open IR

/-- A circuit declared in a contract type: its name, arguments and result. -/
structure InterfaceCircuit where
  name : String
  args : List (String × Shape)
  result : Shape
  deriving Inhabited

/-- A contract type (Compact's `contract T { … }`): the circuits a contract
    called through it must export, with these exact types. -/
structure Interface where
  name : String
  circuits : List InterfaceCircuit
  deriving Inhabited

/-- A contract type as a Lean type: what `interface T where …` declares for `T`.

    A reference to a contract is its 32-byte address and nothing else, in
    compactc's output as here: a contract-typed circuit argument is the two
    limbs of a `Bytes<32>` (range-checked to 8 and 248 bits), a contract-typed
    ledger cell has alignment `bytes 32`, and the call's claim pushes the
    address as a `bytes 32` atom. So converting between `Bytes 32` and any
    contract type costs nothing: no instruction and no check. Compact has no
    such conversion; Damp has it so that the contract called can be chosen at
    run time (an argument, a witness, a ledger value, a hash). It is unchecked:
    nothing in the caller's circuit says that the contract at that address has
    the declared circuits (`docs/calls.md`, "Casting an address"). -/
class ContractType (τ : Type) where
  declaration : Interface
  ofAddress : Bytes 32 → τ
  address : τ → Bytes 32

/-- The contract at address `b`, as a reference of contract type `τ`: free and unchecked. -/
def castContract (τ : Type) [ContractType τ] (b : Bytes 32) : τ := ContractType.ofAddress b

/-- The address of a contract reference. -/
def contractAddressOf [ContractType τ] (r : τ) : Bytes 32 := ContractType.address r

/-- What a call's witness is called: `call:<Interface>.<circuit>`. No user
    witness can have this name (a `witness` declaration takes an identifier). -/
def callWitnessName (iface circuit : String) : String := s!"call:{iface}.{circuit}"

/-- The 32 bytes naming a circuit as an entry point of its contract: the
    ledger's `EntryPointBuf::ep_hash`, a persistent commitment to the name's
    UTF-8 bytes with opening `"midnight:entry-point"` padded to 32 bytes, i.e.
    SHA-256 of `"midnight:entry-point"`, 12 zero bytes, then the name. -/
def entryPointHash (circuit : String) : List UInt8 :=
  Crypto.Sha256.hash ("midnight:entry-point".toUTF8.toList ++ List.replicate 12 0 ++ circuit.toUTF8.toList)

/-- `entryPointHash` as a `Bytes 32` constant (first byte least significant). -/
def entryPoint (circuit : String) : Bytes 32 := Bytes.ofBytes 32 (entryPointHash circuit)

/-- Call `circuit` of the contract at `ref` (the limbs of its address) through
    the contract type `iface`, with the field elements `args` of its arguments;
    the result has type `ρ`.

    The results are public, as in Compact (they are bound by the commitment the
    callee's proof shares); the arguments and the address are operands of the
    kernel claim, so a private one must be `disclose`d by the caller, as
    compactc requires. -/
def contractCall (ρ : Type) [Value ρ] (iface circuit : String) (ref : List Expr) (args : List Expr) :
    CircuitM ρ := do
  let (r, rand) ← askWitness (callWitnessName iface circuit) (ρ × Field) (ref ++ args)
  let results := (Value.toExprs r).map .disclose
  -- The communication commitment: the opening hides the rest, so it is public.
  let comm ← val (⟨.hash (.disclose rand.expr :: args ++ results)⟩ : Field) "comm"
  Kernel.claimContractCall ⟨⟨ref⟩⟩ (entryPoint circuit) comm
  return Value.ofExprs results

end Damp
