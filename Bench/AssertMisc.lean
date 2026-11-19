import Damp

/-! `bench/compact/assert_misc.compact` (the ellen, myswitch and abel circuits of Compact's
examples/assert/example_one.compact). -/
namespace Bench.AssertMisc
open Damp

struct bobson where
  a : Vector Field 1
  b : Field
  c : Boolean

ledger
  round : Counter
  mapsy : Map Field Counter
  kris : Map Field bobson
  stan : Map Field bobson

circuit ellen (x : bobson) : Unit := do
  stan.insert 1 (disclose x)
  kris.insert 1 (disclose x)
  require (((← kris.lookup 1).a[0] !=. 0) ==. ((← stan.lookup 1).a[0] !=. 0)) "stan and kris"

circuit myswitch (x y : Field) (b : Boolean) : Field := do
  const r ← if% disclose b then do
      require (x !=. y) "same"
      round.increment (← (disclose x).toUint 65535)
      round.increment (← (disclose y).toUint 65535)
      return x
    else do
      require (y !=. x) "same"
      round.increment (← (disclose y).toUint 65535)
      round.increment (← (disclose x).toUint 65535)
      return y
  return r

circuit abel : Unit := do
  mapsy.insertDefault 1
  require ((← (← mapsy.lookup 1).read) !=. 2) "equal 1"
  (← mapsy.lookup 1).increment 1
  (← mapsy.lookup 1).increment 2

contract assert_misc

end Bench.AssertMisc
