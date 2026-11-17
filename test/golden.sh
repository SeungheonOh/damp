#!/usr/bin/env bash
# Regression test that needs nothing from Midnight: the ZKIR emitted for every
# example must equal the checked-in copy under test/golden/.
#   ./test/golden.sh            compare
#   ./test/golden.sh --update   accept the current output as the new reference
set -euo pipefail
cd "$(dirname "$0")/.."

out=build/golden
rm -rf "$out"; mkdir -p "$out"
lake build damp-examples >/dev/null
lake exe damp-examples "$out" >/dev/null

if [[ "${1:-}" == "--update" ]]; then
  rm -rf test/golden; mkdir -p test/golden
  for d in "$out"/*/; do
    name=$(basename "$d")
    mkdir -p "test/golden/$name"
    cp "$d"zkir/*.zkir "test/golden/$name/" 2>/dev/null || true
    cp "$d"contract.json "test/golden/$name/"
  done
  echo "updated test/golden"
  exit 0
fi

fail=0
for ref in test/golden/*/*; do
  name=$(basename "$(dirname "$ref")"); file=$(basename "$ref")
  if [[ "$file" == contract.json ]]; then got="$out/$name/$file"; else got="$out/$name/zkir/$file"; fi
  if [[ -f "$got" ]] && cmp -s "$ref" "$got"; then
    echo "ok    $name/$file"
  else
    echo "FAIL  $name/$file   (diff $ref $got)"
    fail=1
  fi
done
exit $fail
