#!/usr/bin/env bash
# Copy fresh Damp + compactc outputs from ../build/oracle into artifacts/.
# Run ../test/oracle.sh first (or pass --oracle to have this script run it).
set -euo pipefail
here="$(cd "$(dirname "$0")/.." && pwd)"
damp="$(cd "$here/.." && pwd)"
if [[ "${1:-}" == "--oracle" ]]; then (cd "$damp" && ./test/oracle.sh); fi
for name in counter vault; do
  for kind in lean compact; do
    rm -rf "$here/artifacts/$kind-$name"
    cp -r "$damp/${DAMP_OUT:-build/oracle}/$kind/$name" "$here/artifacts/$kind-$name"
  done
done
echo "artifacts refreshed from $damp/build/oracle"
