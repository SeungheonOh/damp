#!/usr/bin/env bash
# Every test suite, in order, one line each: name, result, time. Exits nonzero if any failed.
# Each suite's output goes to $FULL_LOG/<suite>.log (default build/full). The suites keep their own
# output-directory variables (DAMP_OUT, BENCH_OUT, LO_OUT, ...).
set -uo pipefail
cd "$(dirname "$0")/.."
log="${FULL_LOG:-build/full}"
mkdir -p "$log"
fail=0
# `audit` is test/audit/run.sh (docs/audit.md): it reads test/vm.sh's recorded states, so it runs after vm.
for t in all golden executor semantics opt vm bench jsontext loader ledger-opt calls-isolation prune-sound \
         witness-effects o3-fold audit; do
  start=$SECONDS
  script="./test/$t.sh"; [[ $t == audit ]] && script=./test/audit/run.sh
  if "$script" >"$log/$t.log" 2>&1; then r=ok; else r=FAIL; fail=1; fi
  printf '%-5s %-15s %4ds  %s\n' "$r" "$t" $((SECONDS - start)) "$(grep -v '^\s*$' "$log/$t.log" | tail -1 | cut -c1-100)"
done
exit $fail
