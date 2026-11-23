import Bench
open Damp

/-! Audit (docs/audit.md, finding F1): the ledger passes treat every witness except
`createZswapOutput` and `call:…` as unable to see the ledger (`Exec.Oracles.witness` has no
access to the ledger state). In the shipped executor a user witness is called with
`createWitnessContext(ledgerView(currentQueryContext.state), ...)`: it sees the ledger state
as left by the ledger statements before it, exactly as compactc's generated code does.
`ledgerDeadStore` drops a write across such a witness and `ledgerMerge` moves a write above one,
so the witness sees a different state and the call returns a different result. -/
namespace AuditPeek

ledger
  c : Cell Field
  d : Cell Field

witness peekC : Field
witness peekD : Field

/-- `ledgerDeadStore` drops the first write (constant guard, key and value; the next ledger
    statement overwrites the key; only a user witness between). -/
circuit deadstore : Field := do
  c.write 1
  const x ← peekC
  c.write 2
  return disclose x

/-- `ledgerMerge` appends the write of `d` to the request writing `c`, above the witness. -/
circuit merge (v : Field) : Field := do
  c.write (disclose v)
  const x ← peekD
  d.write (disclose v + 7)
  return disclose x

/-- Control: no write after the witness. -/
circuit control : Field := do
  c.write 3
  const x ← peekC
  return disclose x

contract audit_peek
end AuditPeek

def main (args : List String) : IO UInt32 := do
  let out := System.FilePath.mk (args.headD "build")
  let c := AuditPeek.contract
  for (dir, m) in [("o2", c.optimize .full false), ("lo", c.optimize .full true)] do
    for circ in m.circuits ++ m.«constructor».toList do
      if let .error e := circ.checkLedger then throw (IO.userError s!"{c.name}: {e}")
    let srcs ← IO.ofExcept m.emitAll
    m.writeFiles (out / dir / c.name) srcs
  return 0
