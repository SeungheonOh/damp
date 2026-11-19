import Damp

/-! `bench/compact/block_time.compact` (Compact's test-center/compact/block-time.compact). -/
namespace Bench.BlockTime
open Damp

circuit testBlockTimeLt (time : Uint64) : Boolean :=
  blockTimeLt (disclose time)

circuit testBlockTimeGte (time : Uint64) : Boolean :=
  blockTimeGte (disclose time)

circuit testBlockTimeGt (time : Uint64) : Boolean :=
  blockTimeGt (disclose time)

circuit testBlockTimeLte (time : Uint64) : Boolean :=
  blockTimeLte (disclose time)

contract block_time

end Bench.BlockTime
