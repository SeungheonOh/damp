import Examples

/-! Builds every example contract: `lake exe damp-examples [--keys] [OUT_DIR]`. -/
def main (args : List String) : IO UInt32 :=
  Damp.cli
    [Examples.Step.contract, Examples.Counter.contract, Examples.Shapes.contract,
     Examples.Loops.contract, Examples.Bytes.contract, Examples.Extras.contract, Examples.Vault.contract, Examples.Notes.contract, Examples.Structures.contract, Examples.StructuresNested.contract, Examples.Tuned.contract, Examples.Tokens.contract]
    args
