import Bench
open Damp

/-! Audit (docs/audit.md, finding F2): `hashRanges` (--O3) drops the range check of a value that a
later persistent hash reads in a narrow slot. The hash may sit in a binding nothing uses, which the
emitter then prunes (`Emit.pruneDeadBinds`): the shipped ZKIR neither checks the range nor hashes.
`Circuit.hashRanges_soundFor` is about `Circuit.run`, which evaluates every binding, so it does not
see the difference. -/
namespace AuditHash
ledger
  c : Cell Field
witness w : Uint 255
circuit f : Unit := do
  const x ← w
  const _h := persistentHash #v[x]
  c.write (disclose x.toField)
contract audit_hash
end AuditHash

def main (args : List String) : IO UInt32 := do
  let out := System.FilePath.mk (args.headD "build")
  let c := AuditHash.contract
  for (dir, m) in [("o2", c.optimize .full false), ("o3", c.optimize .max false)] do
    let srcs ← IO.ofExcept m.emitAll
    m.writeFiles (out / dir / c.name) srcs
  return 0
