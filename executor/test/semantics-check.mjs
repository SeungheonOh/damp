// Child process for semantics-vectors.mjs: runs Midnight's real ZKIR checker
// (`check` from @midnightntwrk/zkir-v3 3.2.1, i.e. `IrSource::preprocess`) on
// serialized preimages, one JSON line per job on stdout.
//
// A preimage whose transcript runs out makes the Rust code index past the end
// of a slice; in wasm that panic aborts the instance ("RuntimeError:
// unreachable") and takes the process down. That is why this runs in its own
// process: the parent records the crash against the job that caused it and
// restarts us after it.
//
// Usage: node semantics-check.mjs <jobs.json> <first job index>

import fs from 'node:fs';
import { check, jsonIrToBinary } from '@midnightntwrk/zkir-v3';

const [jobsFile, startArg] = process.argv.slice(2);
const jobs = JSON.parse(fs.readFileSync(jobsFile, 'utf-8'));
const irCache = new Map();
const irOf = (zkirPath) => {
  if (!irCache.has(zkirPath)) irCache.set(zkirPath, jsonIrToBinary(fs.readFileSync(zkirPath, 'utf-8')));
  return irCache.get(zkirPath);
};

const errStr = (e) => (e instanceof Error ? `${e.name}: ${e.message}` : String(e));

for (let i = Number(startArg); i < jobs.length; i++) {
  const job = jobs[i];
  // Announce the job first, so that a crash can be attributed to it.
  fs.writeSync(2, `job ${i}\n`);
  const provider = {
    async lookupKey() { return { proverKey: new Uint8Array(0), verifierKey: new Uint8Array(0), ir: irOf(job.zkir) }; },
    async getParams() { throw new Error('check does not need parameters'); },
  };
  let line;
  try {
    const skips = await check(Uint8Array.from(Buffer.from(job.preimage, 'hex')), provider);
    line = { i, ok: true, skips: skips.map((s) => (s === undefined ? null : Number(s))) };
  } catch (e) {
    line = { i, ok: false, error: errStr(e) };
  }
  fs.writeSync(1, JSON.stringify(line) + "\n");
}
