/-
The executor's theorems, instantiated with the ledger the VM model induces.

`Damp/Proofs/Executor.lean` proves its results for any `Exec.Oracles`; with
`oracles H w` (`Damp/Ledger/Query.lean`) the ledger is no longer a parameter
but Midnight's VM as modelled in `Damp/Ledger/Vm.lean` (validated by
`test/vm.sh`), and the ledger state is a concrete `LedgerState`. The theorems
of `Damp/Proofs/Ledger/{Cell,Counter,Map}.lean` say what that oracle answers
for each ledger operation.
-/
import Damp.Proofs.Executor
import Damp.Proofs.Ledger.Map

namespace Damp.Ledger
open Damp.IR

/-- What the executor sends a ledger statement to is `ledgerOracle`. -/
theorem oracles_ledger {ω : Type} (H : Hooks) (w : String → List Fr → ω → Option (List Fr × ω)) :
    (oracles H w).ledger = ledgerOracle H := rfl

/-- `Exec.run_accepted` against the VM model: a call the executor completes,
    running its ledger statements on the modelled VM from ledger state
    `ledger`, is a run the circuit accepts, with the transcripts recorded. -/
theorem run_accepted_vm {ω : Type} (H : Hooks) (w : String → List Fr → ω → Option (List Fr × ω))
    (p : Zkir.Prims) (c : Circuit) (inputs : List Fr) (private_ : ω) (ledger : LedgerState)
    (r : Exec.Result ω LedgerState) (h : Exec.run p (oracles H w) c inputs private_ ledger = some r) :
    c.run p inputs r.priv r.pub = some { outputs := r.outputs, groups := r.groups } :=
  Exec.run_accepted p (oracles H w) c inputs private_ ledger r h

/-- `Exec.run_accepted_by_zkir` against the VM model. -/
theorem run_accepted_by_zkir_vm {ω : Type} (H : Hooks) (w : String → List Fr → ω → Option (List Fr × ω))
    (p : Zkir.Prims) (c : Circuit) (src : Zkir.IrSource) (hsrc : Emit.circuit c.optimize = .ok src)
    (inputs : List Fr) (private_ : ω) (ledger : LedgerState) (r : Exec.Result ω LedgerState)
    (h : Exec.run p (oracles H w) c.optimize inputs private_ ledger = some r) :
    src.run p inputs r.priv r.pub = some { outputs := r.outputs, groups := r.groups } :=
  Exec.run_accepted_by_zkir p (oracles H w) c src hsrc inputs private_ ledger r h

end Damp.Ledger
