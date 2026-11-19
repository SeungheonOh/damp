-- The field and Midnight's circuit format
import Damp.Field
import Damp.Zkir.Basic
import Damp.Zkir.Checks
import Damp.Zkir.Json
import Damp.Zkir.Semantics
import Damp.Crypto.Prims
-- The intermediate representation and its meaning
import Damp.IR.Impact
import Damp.IR.Basic
import Damp.IR.Semantics
import Damp.IR.Disclosure
import Damp.IR.LedgerCheck
-- Optimization passes
import Damp.Optimize.Pass
import Damp.Optimize.Simplify
import Damp.Optimize.Bounds
import Damp.Optimize.Algebra
import Damp.Optimize.Asserts
import Damp.Optimize.Pipeline
-- From the IR to ZKIR and contract.json
import Damp.Compile.Emit
import Damp.Compile.Export
import Damp.Compile.Build
-- The executor's definition
import Damp.Executor.Spec
-- The language contracts are written in
import Damp.Lang.Contract
import Damp.Lang.Ledger
import Damp.Lang.Calls
import Damp.Lang.Syntax
import Damp.Lang.Tokens
-- Proofs
import Damp.Proofs.Field
import Damp.Proofs.Prune
import Damp.Proofs.Emit
import Damp.Proofs.Optimize.Simplify
import Damp.Proofs.Optimize.SimplifyExecutor
import Damp.Proofs.Optimize.Sound
import Damp.Proofs.Optimize.Bounds
import Damp.Proofs.Optimize.Algebra
import Damp.Proofs.Optimize.Asserts
import Damp.Proofs.Optimize.Pipeline
import Damp.Proofs.Compiler
import Damp.Proofs.Executor
import Damp.Proofs.ExecutorComplete
import Damp.Proofs.LedgerAgreement
import Damp.Proofs.Interface
