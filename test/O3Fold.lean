import Bench
open Damp

/-! Audit finding F3: `--O3` computes hashes of constants at compile time with `Damp.Crypto.prims`
(`Circuit.foldHashes`), and no test ran a call whose outcome depends on a folded constant.

`check` asserts that hashes of literals, which `--O3` folds into constants, equal the hashes of the
same values that `store` computed at run time (from an argument, so not folded) and wrote to the
ledger; it returns the folded values. A call of `check` after `store 42` succeeds exactly when
Damp's Poseidon and persistent hash agree with the runtime's on those inputs, and its proof data
must be accepted by Midnight's checker. Written at `--O2` (hashes computed in the circuit) and
`--O3` (folded) for test/o3-fold.sh.

Usage: lake env lean --run test/O3Fold.lean OUT_DIR -/
namespace O3Fold

ledger
  digest : Cell (Bytes 32)
  tdigest : Cell Field
  bdigest : Cell (Bytes 32)

/-- The hashes of `[v, 7]` and of the 32-byte string "damp", computed in the circuit. -/
circuit store (v : Field) (b : Bytes 32) : Unit := do
  digest.write (persistentHash #v[disclose v, (7 : Field)])
  tdigest.write (transientHash #v[disclose v, (7 : Field)])
  bdigest.write (persistentHash (disclose b))

/-- The same hashes of literals: constants at `--O3`. -/
circuit check : Bytes 32 × Field × Bytes 32 := do
  const h := persistentHash #v[(42 : Field), (7 : Field)]
  const t := transientHash #v[(42 : Field), (7 : Field)]
  const hb := persistentHash (Bytes.pad 32 "damp")
  require ((← digest.read) ==. h) "persistent hash of constants"
  require ((← tdigest.read) ==. t) "transient hash of constants"
  require ((← bdigest.read) ==. hb) "persistent hash of a byte string"
  return (h, t, hb)

contract o3_fold
end O3Fold

def main (args : List String) : IO UInt32 := do
  let out := System.FilePath.mk (args.headD "build")
  let c := O3Fold.contract
  for (dir, m) in [("o2", c.optimize .full false), ("o3", c.optimize .max false)] do
    let srcs ← IO.ofExcept m.emitAll
    m.writeFiles (out / dir / c.name) srcs
  return 0
