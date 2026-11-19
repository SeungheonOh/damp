import Damp

/-! `bench/compact/composable_inner.compact` and `composable_outer.compact` (Compact's
test-center/composable/Basic): a contract that stores another contract's address and calls it. -/
namespace Bench.ComposableInner
open Damp

ledger
  v : Cell Field

circuit add (value : Field) : Field := do
  v.write ((← v.read) + disclose value)
  v.read

contract composable_inner

end Bench.ComposableInner

namespace Bench.ComposableOuter
open Damp

interface Inner where
  add (value : Field) : Field

ledger
  inner : Cell Inner

constructor (i : Inner) := do
  inner.write (disclose i)

circuit add (value : Field) : Field :=
  return (← (← inner.read).add (disclose value))

circuit setInner (i : Inner) : Inner := do
  const lastInner ← inner.read
  inner.write (disclose i)
  return lastInner

circuit echoStored : Inner := do
  const a ← inner.read
  return a

circuit echoInner (i : Inner) : Inner := do
  return disclose i

circuit addViaConst (value : Field) : Field := do
  const target ← inner.read
  target.add (disclose value)

contract composable_outer

end Bench.ComposableOuter
