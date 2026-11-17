#!/usr/bin/env bash
# Full run against a FRESH local network: down, up, then every scenario.
# Logs go to out/*.log; each scenario also writes out/*-result.json.
set -uo pipefail
cd "$(dirname "$0")/.."
mkdir -p out
docker compose -p damp-local -f compose.yml down
docker compose -p damp-local -f compose.yml up -d --wait || exit 1
status=0
run() { local name=$1; shift; echo "=== $name: $*"; if "$@" > "out/$name.log" 2>&1; then echo "    ok"; else echo "    FAILED (see out/$name.log)"; status=1; fi
        grep -E 'DEPLOYED|CALL |FINAL|RESULT|INTEROP|rejected as expected|NEGATIVE CONTROL FAILED|failed:|ERROR' "out/$name.log" | grep -v RPC-CORE | sed 's/^/    /'; }
run baseline-counter node src/run.mjs compact
run damp-counter     node src/run.mjs damp
run checks           node src/checks.mjs
run damp-vault       node src/vault.mjs damp
run baseline-vault   node src/vault.mjs compact
exit $status
