// Audit (docs/audit.md, F1): a user witness sees the ledger state mid-call (the executor passes
// `ledgerView(currentQueryContext.state)` in its witness context, as compactc's modules do), but
// `Exec.Oracles.witness` cannot see the ledger, so the ledger passes may move or drop writes
// across such a witness. Runs test/audit/LedgerWitness.lean's contract built at --O2 (o2) and
// --O2 --ledger-opt (lo) through the real runtime with the SAME witness implementations, and
// requires the same results. Failed at ccd590e; F1 is fixed (the model's witness oracle sees and
// returns the ledger state, `Exec.WitnessOracle`, and the ledger passes treat every witness that can
// read the ledger as a barrier), so this is now a regression that must pass.
//
// Usage: node test/audit-ledger-witness.mjs <dir holding o2/ and lo/>
import fs from 'node:fs/promises';
import path from 'node:path';
import * as rt from '@midnight-ntwrk/compact-runtime';
import { makeContract } from '../src/executor.mjs';
import { toJson } from '../harness/json.mjs';

const root = path.resolve(process.argv[2]);
const COIN_PK = '3c'.repeat(32);
const witnesses = {
  peekC: ({ privateState, ledger }) => [privateState, ledger.c],
  peekD: ({ privateState, ledger }) => [privateState, ledger.d],
};
let failures = 0, checks = 0;
const report = (ok, label, detail = '') => { checks++; if (!ok) failures++; console.log(`${ok ? 'ok  ' : 'FAIL'} ${label}${detail ? '  ' + detail : ''}`); };

const impl = {};
for (const l of ['o2', 'lo']) {
  const dir = path.join(root, l, 'audit_peek');
  const spec = JSON.parse(await fs.readFile(path.join(dir, 'contract.json'), 'utf-8'));
  const contract = makeContract(spec, witnesses);
  const init = await contract.initialState(rt.createConstructorContext({}, COIN_PK));
  impl[l] = { contract, init, state: init.currentContractState };
}
const ctxOf = (id, i) => rt.createCircuitContext({
  circuitId: id, contractAddress: rt.dummyContractAddress(),
  coinPublicKeyOrZswapState: i.init.currentZswapLocalState.coinPublicKey,
  contractState: i.state, privateState: i.init.currentPrivateState, time: 0,
});
for (const [circuit, args] of [['control', []], ['deadstore', []], ['merge', [10n]], ['merge', [20n]]]) {
  const out = {};
  for (const l of ['o2', 'lo']) {
    const r = await impl[l].contract.circuits[circuit](ctxOf(circuit, impl[l]), ...args);
    impl[l].state = r.context.callContext.currentQueryContext.state;
    out[l] = toJson(r.result, 0);
  }
  report(out.o2 === out.lo, `audit_peek.${circuit}(${args.join(',')}): same result`, `o2 ${out.o2} lo ${out.lo}`);
}
console.log(failures === 0 ? `audit-ledger-witness: ${checks} checks passed` : `audit-ledger-witness: ${failures} of ${checks} checks FAILED (regression: finding F1)`);
process.exit(failures === 0 ? 0 : 1);
