import Bench

/-! Builds every benchmark contract: `lake exe damp-bench [--no-opt | --O2 | --O3] [--ledger-opt] [OUT_DIR]`. -/
def main (args : List String) : IO UInt32 :=
  Damp.cli
    [Bench.Counter.contract, Bench.Tiny.contract, Bench.Threading.contract, Bench.GasCost.contract,
     Bench.BlockTime.contract, Bench.UnshieldedTokens.contract, Bench.Coracle.contract,
     Bench.ElectionCore.contract, Bench.ZerocashCore.contract, Bench.Pm20028.contract,
     Bench.Pm19287.contract, Bench.Types.contract, Bench.AssertMisc.contract,
     Bench.AdtCounter.contract, Bench.AdtListStruct.contract, Bench.AdtMapList.contract,
     Bench.AdtMerkle.contract, Bench.ComposableInner.contract, Bench.ComposableOuter.contract,
     Bench.Vectors.contract, Bench.Test01.contract, Bench.ProofData.contract,
     Bench.ZkirGeneration.contract]
    args
