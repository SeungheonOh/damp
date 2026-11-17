import Damp

/-! Cross-contract calls (`docs/calls.md`): the Lean counterparts of
`test/oracle/adder.compact`, `rich.compact`, `caller.compact`, `relay.compact`
and `top.compact`. `caller` calls `adder` and `rich`; `top` calls `relay`,
which calls `adder`: a nested call. -/

namespace Examples.Adder
open Damp

ledger
  total : Cell Field

circuit addTo (x : Field) : Field := do
  require (disclose x !=. (13 : Field)) "unlucky"
  total.write (disclose ((← total.read) + x))
  total.read

circuit clear : Unit := total.write 0

contract adder

end Examples.Adder

namespace Examples.Rich
open Damp

struct Pt where
  x : Field
  y : Uint8

ledger
  last : Cell Pt
  tag : Cell (Bytes 32)

circuit mix (p : Pt) (b : Bytes 32) (k : Uint16) : Pt × Bytes 32 := do
  last.write (disclose p)
  tag.write (disclose b)
  return (⟨p.x + k.toField, p.y⟩, b)

contract rich

end Examples.Rich

namespace Examples.Caller
open Damp

struct Pt where
  x : Field
  y : Uint8

interface Adder where
  addTo (x : Field) : Field
  clear : Unit

interface Rich where
  mix (p : Pt) (b : Bytes 32) (k : Uint16) : Pt × Bytes 32

ledger
  adder : Cell Adder
  rich : Cell Rich
  last : Cell Field
  lastB : Cell (Bytes 32)

constructor (a : Adder) (r : Rich) := do
  adder.write (disclose a)
  rich.write (disclose r)

/-- The simple call. Its result is public: no `disclose` to store it. -/
circuit bump (x : Field) : Field := do
  const r ← (← adder.read).addTo (disclose x)
  last.write r
  return r

/-- A call under a condition: not made, and not claimed, when `go` is false. -/
circuit maybe (go : Boolean) (x : Field) : Field := do
  if% disclose go then do
    last.write (← (← adder.read).addTo (disclose x))
  last.read

/-- Two calls to the same contract: the second sees what the first left. -/
circuit twice (x y : Field) : Field := do
  const a ← (← adder.read).addTo (disclose x)
  const b ← (← adder.read).addTo (disclose y)
  return a + b

/-- The contract called is an argument, so it must be disclosed. -/
circuit via (a : Adder) (x : Field) : Field := (disclose a).addTo (disclose x)

/-- No arguments, no result. -/
circuit reset : Unit := do (← adder.read).clear

/-- Structure and bytes arguments, a structure and bytes back. -/
circuit fancy (p : Pt) (b : Bytes 32) (k : Uint16) : Field := do
  let (q, bb) ← (← rich.read).mix (disclose p) (disclose b) (disclose k)
  lastB.write bb
  return q.x + q.y.toField

contract caller

end Examples.Caller

namespace Examples.Relay
open Damp

interface Adder where
  addTo (x : Field) : Field

ledger
  adder : Cell Adder
  hops : Counter

constructor (a : Adder) := adder.write (disclose a)

/-- Called by `top`, and calls `adder`. -/
circuit relay (x : Field) : Field := do
  hops.increment 1
  (← adder.read).addTo (disclose x)

contract relay

end Examples.Relay

namespace Examples.Top
open Damp

interface Relay where
  relay (x : Field) : Field

ledger
  relay : Cell Relay
  got : Cell Field

constructor (r : Relay) := relay.write (disclose r)

circuit go (x : Field) : Field := do
  const r ← (← relay.read).relay (disclose x)
  got.write r
  return r

contract top

end Examples.Top

/-! The callee chosen at run time: an address from anywhere, cast to a contract
type (`docs/calls.md`, "Casting an address"). The counterpart of
`test/oracle/picker.compact`, which, since Compact cannot cast, takes the same
bytes already contract-typed. -/
namespace Examples.Picker
open Damp

interface Adder where
  addTo (x : Field) : Field

interface Clearer where
  clear : Unit

/-- `addTo` with another argument type than `adder.compact` has. -/
interface Wrong where
  addTo (x : Uint16) : Field

ledger
  refs : Map Field (Bytes 32)

circuit register (k : Field) (a : Bytes 32) : Unit := refs.insert (disclose k) (disclose a)

/-- The address is a `Bytes 32` argument: it must be disclosed, as compactc
    demands of a contract-typed argument that is called. -/
circuit viaArg (a : Bytes 32) (x : Field) : Field := (Adder.ofAddress (disclose a)).addTo (disclose x)

/-- The address is a ledger value: public already. -/
circuit viaMap (k : Field) (x : Field) : Field := do
  (Adder.ofAddress (← refs.lookup (disclose k))).addTo (disclose x)

/-- One address, two contract types, both called. -/
circuit both (a : Bytes 32) (x : Field) : Field := do
  const r ← (Adder.ofAddress (disclose a)).addTo (disclose x)
  (castContract Clearer (disclose a)).clear
  return r

circuit wrongSig (a : Bytes 32) (x : Uint16) : Field := (Wrong.ofAddress (disclose a)).addTo (disclose x)

contract picker

end Examples.Picker

/-! Disclosure: `disclose` is required exactly where compactc 0.36.1 requires it
(`docs/calls.md`): on a call's arguments, on the contract reference when it is
private, and on a condition the call is made under; not on a call's results. -/
namespace Examples.CallDiagnostics
open Damp

interface Adder where
  addTo (x : Field) : Field

ledger
  adder : Cell Adder
  total : Cell Field

witness secret : Field

/--
error: circuit cannot be compiled: a ledger operation stores or looks up a value that depends on argument `x`. If making it public is intended, wrap it in `disclose`
-/
#guard_msgs in
circuit argLeak (x : Field) : Field := do (← adder.read).addTo x

/--
error: circuit cannot be compiled: a ledger operation stores or looks up a value that depends on argument `a`. If making it public is intended, wrap it in `disclose`
-/
#guard_msgs in
circuit refLeak (a : Adder) (x : Field) : Field := a.addTo (disclose x)

/--
error: circuit cannot be compiled: whether a ledger operation runs depends on argument `go`. If making it public is intended, wrap it in `disclose`
-/
#guard_msgs in
circuit condLeak (go : Boolean) (x : Field) : Unit := do
  if% go then do
    let _ ← (← adder.read).addTo (disclose x)

/--
error: circuit cannot be compiled: a ledger operation stores or looks up a value that depends on the result of witness `secret`. If making it public is intended, wrap it in `disclose`
-/
#guard_msgs in
circuit witnessArg : Field := do (← adder.read).addTo (← secret)

/--
error: circuit cannot be compiled: a ledger operation stores or looks up a value that depends on argument `b`. If making it public is intended, wrap it in `disclose`
-/
#guard_msgs in
circuit castLeak (b : Bytes 32) (x : Field) : Field := (Adder.ofAddress b).addTo (disclose x)

-- A cast address that is public already (a constant, here) needs nothing.
circuit castConst (x : Field) : Field := (Adder.ofAddress (Bytes.ofBytes 32 [7])).addTo (disclose x)

-- Accepted, as by compactc: a call's result is public. It is stored, passed to
-- another call and returned without `disclose`.
circuit resultPublic (x : Field) : Field := do
  const r ← (← adder.read).addTo (disclose x)
  total.write r
  (← adder.read).addTo r

end Examples.CallDiagnostics
