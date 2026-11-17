#!/usr/bin/env bash
# Differential test against Midnight's own compiler.
#
# Each example contract exists twice: as Lean (Examples/) and as Compact
# (test/oracle/*.compact). Both are turned into prover and verifier keys by
# Midnight's zkir tool; the test passes when the verifier keys are identical.
#
# Needs compactc and zkir-v3 from one Compact toolchain release.
#   COMPACT_HOME  directory holding compactc.bin and zkir-v3
set -euo pipefail
cd "$(dirname "$0")/.."

COMPACT_HOME="${COMPACT_HOME:-$HOME/.compact/versions/0.36.1/x86_64-unknown-linux-musl}"
export PATH="$COMPACT_HOME:$PATH"
out="${DAMP_OUT:-build/oracle}"   # set DAMP_OUT to run alongside another test run
rm -rf "$out"; mkdir -p "$out"

lake build damp-examples >/dev/null
lake exe damp-examples "$out/lean" >/dev/null

fail=0
for src in test/oracle/*.compact; do
  name=$(basename "$src" .compact)
  compactc.bin "$src" "$out/compact/$name" >/dev/null 2>&1
  mkdir -p "$out/lean/$name/keys"
  zkir-v3 compile-many "$out/lean/$name/zkir" "$out/lean/$name/keys" >/dev/null 2>&1
  for vk in "$out/compact/$name"/keys/*.verifier; do
    circuit=$(basename "$vk" .verifier)
    mine="$out/lean/$name/keys/$circuit.verifier"
    if [[ -f "$mine" ]] && cmp -s "$vk" "$mine"; then
      echo "ok    $name.$circuit  $(sha256sum "$mine" | cut -c1-16)"
    elif [[ -f "$mine" ]] && grep -qx "$name.$circuit" test/oracle/known-differences; then
      # A documented difference: compactc's circuit with exactly that difference
      # undone must give Damp's key.
      norm="$out/normalized/$name"; mkdir -p "$norm/zkir" "$norm/keys"
      python3 -I test/zkir-normalize.py "$out/compact/$name/zkir/$circuit.zkir" "$norm/zkir/$circuit.zkir"
      zkir-v3 compile-many "$norm/zkir" "$norm/keys" >/dev/null 2>&1
      if cmp -s "$norm/keys/$circuit.verifier" "$mine"; then
        echo "ok~   $name.$circuit  $(sha256sum "$mine" | cut -c1-16)  (differs from compactc's only as test/oracle/known-differences says)"
      else
        echo "FAIL  $name.$circuit  (even after test/zkir-normalize.py)"
        fail=1
      fi
    else
      echo "FAIL  $name.$circuit"
      fail=1
    fi
  done
done
exit $fail
