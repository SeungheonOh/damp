#!/usr/bin/env bash
# Midnight's loader reads Damp's ZKIR files as Damp's reader does.
#
# Builds every contract of Examples and Bench at every level (--no-opt, default,
# --O2, --O3) and at --O2 --ledger-opt. For every .zkir file: `zkir-v3 mock-compile` loads it with the Rust
# loader (zkir/src/ir.rs) and must succeed (it prints the circuit's rows); it also
# writes the loaded circuit back in the tool's binary format (.bzkir).
# test/LoaderDump.lean prints the circuit Damp's reader (`Zkir.IrSource.parse`)
# returns for the same file, and test/loader.py encodes it in the binary format and
# requires the bytes to equal the .bzkir: the loader and Damp's reader agree on every
# register, immediate (as a field element), type, guard, bit width, alignment, and
# on the number and order of inputs, outputs and instructions.
#
#   LOADER_OUT     output directory (default build/loader)
#   COMPACT_HOME   directory holding zkir-v3
set -euo pipefail
cd "$(dirname "$0")/.."

COMPACT_HOME="${COMPACT_HOME:-$HOME/.compact/versions/0.36.1/x86_64-unknown-linux-musl}"
export PATH="$COMPACT_HOME:$PATH"
out="${LOADER_OUT:-build/loader}"
rm -rf "$out"; mkdir -p "$out"

lake build damp-examples damp-bench Damp.Zkir.Json >/dev/null
for level in no-opt default O2 O3 O2-ledger-opt; do
  case $level in default) flag="";; O2-ledger-opt) flag="--O2 --ledger-opt";; *) flag="--$level";; esac
  lake exe damp-examples $flag "$out/examples-$level" >/dev/null
  lake exe damp-bench $flag "$out/bench-$level" >/dev/null
done

fail=0; n=0
while IFS= read -r f; do
  n=$((n + 1))
  if ! r=$(zkir-v3 mock-compile "$f" 2>&1); then
    echo "FAIL $f: zkir-v3 mock-compile: $r"; fail=1
  elif ! grep -q 'rows=' <<<"$r"; then
    echo "FAIL $f: no row count in: $r"; fail=1
  fi
done < <(find "$out" -name '*.zkir' | sort)
echo "$n files loaded by zkir-v3 mock-compile"

lake env lean --run test/LoaderDump.lean "$out" > "$out/damp-reading.tsv"
python3 -I test/loader.py "$out/damp-reading.tsv" || fail=1
exit $fail
