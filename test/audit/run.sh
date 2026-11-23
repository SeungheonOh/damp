#!/usr/bin/env bash
# The audit's tests (docs/audit.md). Run under the memory wrapper, from anywhere:
#   timeout 1800 systemd-run --user --scope -q -p MemoryMax=10G -p MemorySwapMax=0 test/audit/run.sh
# One line per test: PASS/FAIL, and for a FAIL the finding it exposes. The three tests marked
# "regression" failed at ccd590e (findings F2 and F1); both findings are fixed (docs/audit.md, "Status
# after fixes"), so every row must now PASS, and a FAIL is a regression. They must not be weakened.
# AUDIT_OUT overrides the output directory (default build/audit). AUDIT_VM_VECTORS points at a
# test/vm.sh vectors.json (default build/vm-ledger/vectors/vectors.json; skipped if absent).
set -uo pipefail
cd "$(dirname "$0")/../.."
out="${AUDIT_OUT:-build/audit}"
rm -rf "$out"; mkdir -p "$out"
fail=0
row() { printf '%-5s %-26s %s\n' "$1" "$2" "$3"; [[ $1 == PASS || $1 == SKIP ]] || fail=1; }

lake build Bench damp-semantics-test damp-vm-test >"$out/build.log" 2>&1 || { echo "lake build failed (see $out/build.log)"; exit 2; }
ln -sfn ../executor/node_modules build/node_modules

# F2 (fixed; regression): the shipped (pruned) ZKIR must not accept inputs the unoptimized ZKIR rejects.
if lake env lean test/audit/Prune.lean >"$out/prune.log" 2>&1; then row PASS prune-widening ""
else row FAIL prune-widening "regression F2: $(grep -c 'did not evaluate' "$out/prune.log") guards failed (see $out/prune.log)"; fi

# F2 end to end (fixed; regression): --O3 hashRanges + an unused hash; Midnight's checker must refuse a forged out-of-range value.
if lake env lean --run test/audit/HashRange.lean "$out/hr" >"$out/hr.log" 2>&1 &&
   (cd executor && node test/audit-o3-range.mjs "../$out/hr") >>"$out/hr.log" 2>&1; then row PASS o3-range-forgery ""
else row FAIL o3-range-forgery "regression F2: $(grep -m1 FAIL "$out/hr.log")"; fi

# F1 (fixed; regression): user witnesses read the ledger mid-call; --ledger-opt must not move/drop writes across them.
if lake env lean --run test/audit/LedgerWitness.lean "$out/lw" >"$out/lw.log" 2>&1 &&
   (cd executor && node test/audit-ledger-witness.mjs "../$out/lw") >>"$out/lw.log" 2>&1; then row PASS ledger-opt-witness ""
else row FAIL ledger-opt-witness "regression F1: $(tail -1 "$out/lw.log")"; fi

# Edge: IrSource.run vs Midnight's checker on operator edge cases (expected to pass).
if (cd executor && node test/audit-zkir-edges.mjs "../$out/zedge") >"$out/zedge.log" 2>&1 &&
   .lake/build/bin/damp-semantics-test "$out/zedge/vectors.json" --other "$out"/zedge/synthetic/*.zkir >>"$out/zedge.log" 2>&1
then row PASS zkir-edge-vectors "$(grep -m1 '^vectors:' "$out/zedge.log")"
else row FAIL zkir-edge-vectors "$(grep -m1 '^vectors:' "$out/zedge.log")"; fi

# Hypothesis σ.WF on every state test/vm.sh recorded from the real runtime (expected to pass).
vm="${AUDIT_VM_VECTORS:-${DAMP_VM_OUT:-build/vm-ledger}/vectors/vectors.json}"
if [[ -f $vm ]]; then
  if AUDIT_VM_VECTORS="$vm" lake env lean test/audit/WfStates.lean >"$out/wf.log" 2>&1; then row PASS wf-real-states "$(grep -m1 '^WF' "$out/wf.log")"
  else row FAIL wf-real-states "$(grep -m1 '^WF' "$out/wf.log")"; fi
else row SKIP wf-real-states "no $vm (run test/vm.sh first)"; fi

exit $fail
