// Reusable ZKIR oracle: given a compiled contract directory (compactc layout or
// anything with the same layout) and the ProofData for one call of an impure
// circuit, serialize the proof preimage and run the real ZKIR v3 `check`.
//
// Layout expected under compiledDir:
//   zkir/<circuitId>.bzkir   (binary IR; falls back to zkir/<circuitId>.zkir JSON)
//   keys/<circuitId>.prover, keys/<circuitId>.verifier   (optional; see below)
//
// Usage:
//   import { checkProofData } from './check.mjs';
//   const r = await checkProofData({ compiledDir, circuitId, proofData });
//   // r = { ok: true, outputs: [...] } | { ok: false, stage, error }
//
// proofData = { input, output, publicTranscript, privateTranscriptOutputs }
// (exactly the ProofData/CallProofData shape produced by compact-runtime; extra
// fields such as circuitId/initialQueryContext are ignored).

import fs from 'node:fs/promises';
import { existsSync } from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { proofDataIntoSerializedPreimage } from '@midnight-ntwrk/compact-runtime';
import { check as zkirCheck, prove as zkirProve, jsonIrToBinary } from '@midnightntwrk/zkir-v3';

const PARAMS_DIR =
  process.env.MIDNIGHT_ZK_PARAMS_DIR ?? path.join(os.homedir(), '.cache', 'midnight', 'zk-params');

const readOpt = async (p) => (existsSync(p) ? new Uint8Array(await fs.readFile(p)) : new Uint8Array(0));

export const readIr = async (compiledDir, circuitId) => {
  const b = path.join(compiledDir, 'zkir', `${circuitId}.bzkir`);
  if (existsSync(b)) return new Uint8Array(await fs.readFile(b));
  const j = path.join(compiledDir, 'zkir', `${circuitId}.zkir`);
  if (existsSync(j)) return jsonIrToBinary(await fs.readFile(j, 'utf-8'));
  throw new Error(`no zkir/${circuitId}.bzkir or .zkir under ${compiledDir}`);
};

/**
 * KeyMaterialProvider for @midnightntwrk/zkir-v3. `keyLocation` passed to
 * lookupKey is the string given as the last arg of
 * proofDataIntoSerializedPreimage (we use the circuit id).
 */
export const makeKeyProvider = (compiledDir) => ({
  async lookupKey(keyLocation) {
    return {
      proverKey: await readOpt(path.join(compiledDir, 'keys', `${keyLocation}.prover`)),
      verifierKey: await readOpt(path.join(compiledDir, 'keys', `${keyLocation}.verifier`)),
      ir: await readIr(compiledDir, keyLocation),
    };
  },
  async getParams(k) {
    const p = path.join(PARAMS_DIR, `bls_midnight_2p${k}`);
    if (!existsSync(p)) throw new Error(`SRS params for k=${k} not found at ${p}`);
    return new Uint8Array(await fs.readFile(p));
  },
});

export const serializePreimage = (proofData, circuitId) =>
  proofDataIntoSerializedPreimage(
    proofData.input,
    proofData.output,
    proofData.publicTranscript,
    proofData.privateTranscriptOutputs,
    circuitId,
  );

const withTimeout = (p, ms) => {
  let t;
  return Promise.race([
    p,
    new Promise((_, rej) => {
      t = setTimeout(() => rej(new Error(`zkir check timed out after ${ms}ms`)), ms);
    }),
  ]).finally(() => clearTimeout(t));
};

const errStr = (e) => (e instanceof Error ? `${e.name}: ${e.message}` : String(e));

/**
 * `check` only uses the IR (it never reads keys/.prover/.verifier or SRS params).
 * Pass `prove: true` to additionally run the real prover (reads keys/<c>.prover and
 * ~/.cache/midnight/zk-params/bls_midnight_2p<k>; ~1s for small circuits). There is no
 * proof *verifier* in these npm packages, so the proof bytes are only returned.
 * @returns {Promise<{ok: true, outputs: (bigint|undefined)[], proof?: Uint8Array} | {ok: false, stage: 'serialize'|'check'|'prove', error: string}>}
 */
export async function checkProofData({ compiledDir, circuitId, proofData, timeoutMs = 60_000, prove = false }) {
  let preimage;
  try {
    preimage = serializePreimage(proofData, circuitId);
  } catch (e) {
    return { ok: false, stage: 'serialize', error: errStr(e) };
  }
  let outputs;
  try {
    outputs = await withTimeout(zkirCheck(preimage, makeKeyProvider(compiledDir)), timeoutMs);
  } catch (e) {
    return { ok: false, stage: 'check', error: errStr(e) };
  }
  if (!prove) return { ok: true, outputs };
  try {
    const proof = await withTimeout(zkirProve(preimage, makeKeyProvider(compiledDir)), timeoutMs * 5);
    return { ok: true, outputs, proof };
  } catch (e) {
    return { ok: false, stage: 'prove', error: errStr(e) };
  }
}
