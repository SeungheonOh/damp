#!/usr/bin/env bash
# What the optimizer buys, and that it changes nothing observable.
#
# Builds every example at every level (--no-opt, default, --O2, --O3), prints the size of
# each circuit at each (instructions, and rows of the proof system's table as
# reported by Midnight's `zkir-v3 mock-compile`), then runs the same calls
# against both builds of the `tuned` contract and requires equal results and
# acceptance by the ZKIR checker.
set -euo pipefail
cd "$(dirname "$0")/.."

COMPACT_HOME="${COMPACT_HOME:-$HOME/.compact/versions/0.36.1/x86_64-unknown-linux-musl}"
export PATH="$COMPACT_HOME:$PATH"
out=build/opt
rm -rf "$out"; mkdir -p "$out"

lake build damp-examples >/dev/null
lake exe damp-examples --no-opt "$out/plain" >/dev/null
lake exe damp-examples "$out/opt" >/dev/null
lake exe damp-examples --O2 "$out/full" >/dev/null
lake exe damp-examples --O3 "$out/max" >/dev/null

rows() { zkir-v3 mock-compile "$1" 2>&1 | grep -oE 'rows[^0-9]*[0-9]+' | grep -oE '[0-9]+' | head -1; }
count() { python3 -I -c 'import json,sys; print(len(json.load(open(sys.argv[1]))["instructions"]))' "$1"; }

printf '%-24s %-32s %-32s\n' circuit 'instructions' 'rows'
printf '%-24s %-32s %-32s\n' '' 'plain -> default -> O2 -> O3' 'plain -> default -> O2 -> O3'
for f in "$out"/plain/*/zkir/*.zkir; do
  rel=${f#"$out"/plain/}
  g="$out/opt/$rel"
  name="$(dirname "$(dirname "$rel")").$(basename "$rel" .zkir)"
  h="$out/full/$rel"
  m="$out/max/$rel"
  printf '%-24s %5s -> %5s -> %5s -> %-6s %5s -> %5s -> %5s -> %-6s\n' "$name" "$(count "$f")" "$(count "$g")" "$(count "$h")" "$(count "$m")" "$(rows "$f")" "$(rows "$g")" "$(rows "$h")" "$(rows "$m")"
done
find "$out" -name '*.bzkir' -delete   # written by mock-compile; the checker reads the JSON

ln -sfn ../executor/node_modules build/node_modules
(cd executor && node test/opt.mjs "../$out")
