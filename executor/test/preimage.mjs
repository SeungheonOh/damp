// The serialized proof preimage that Midnight's prover and ZKIR checker take,
// read and written field by field.
//
// Layout (midnight-transient-crypto 3.0.1, `ProofPreimage`, serialized with
// midnight-serialize 1.2.1 under the tag `proof-preimage`):
//   "midnight:proof-preimage:"
//   inputs, private_transcript, public_transcript_inputs, public_transcript_outputs : Vec<Fr>
//   binding_input : Fr
//   communications_commitment : Option<(Fr, Fr)>        (byte 0 | byte 1 then two Fr)
//   key_location : string                                 (length, then UTF-8)
// A Vec length and every Fr are SCALE compact integers (`ScaleBigInt`): below
// 2^6 one byte (v<<2), below 2^14 two bytes ((v<<2)|1, LE), below 2^30 four
// bytes ((v<<2)|2, LE), otherwise a byte ((k-4)<<2)|3 followed by the k
// significant little-endian bytes.
//
// This is how the field-element view of a call is obtained without Damp's own
// encoder: the runtime (`proofDataIntoSerializedPreimage`) turns the recorded
// transcript into field elements, and we only parse its output.

const TAG = 'midnight:proof-preimage:';

function readCompact(buf, pos) {
  const b0 = buf[pos];
  switch (b0 & 3) {
    case 0: return [BigInt(b0 >> 2), pos + 1];
    case 1: return [BigInt((b0 | (buf[pos + 1] << 8)) >> 2), pos + 2];
    case 2: return [BigInt(((b0 | (buf[pos + 1] << 8) | (buf[pos + 2] << 16)) >>> 0) + buf[pos + 3] * 2 ** 24) >> 2n, pos + 4];
    default: {
      const k = (b0 >> 2) + 4;
      let v = 0n;
      for (let i = k - 1; i >= 0; i--) v = (v << 8n) | BigInt(buf[pos + 1 + i]);
      return [v, pos + 1 + k];
    }
  }
}

function writeCompact(out, v) {
  v = BigInt(v);
  if (v < 0n) throw new Error('negative compact integer');
  if (v < 1n << 6n) out.push(Number(v << 2n));
  else if (v < 1n << 14n) { const x = Number((v << 2n) | 1n); out.push(x & 0xff, x >> 8); }
  else if (v < 1n << 30n) {
    const x = (v << 2n) | 2n;
    for (let i = 0n; i < 4n; i++) out.push(Number((x >> (8n * i)) & 0xffn));
  } else {
    const bytes = [];
    for (let x = v; x > 0n; x >>= 8n) bytes.push(Number(x & 0xffn));
    out.push(((bytes.length - 4) << 2) | 3, ...bytes);
  }
}

export function parsePreimage(bytes) {
  const buf = Uint8Array.from(bytes);
  const tag = Buffer.from(buf.subarray(0, TAG.length)).toString('latin1');
  if (tag !== TAG) throw new Error(`not a proof preimage: ${tag}`);
  let pos = TAG.length;
  const int = () => { const [v, p] = readCompact(buf, pos); pos = p; return v; };
  const vec = () => { const n = Number(int()); return Array.from({ length: n }, int); };
  const inputs = vec();
  const privateTranscript = vec();
  const publicTranscriptInputs = vec();
  const publicTranscriptOutputs = vec();
  const bindingInput = int();
  const flag = buf[pos++];
  let commitment = null;
  if (flag === 1) commitment = [int(), int()];
  else if (flag !== 0) throw new Error(`bad option flag ${flag}`);
  const n = Number(int());
  const keyLocation = Buffer.from(buf.subarray(pos, pos + n)).toString('utf-8');
  pos += n;
  if (pos !== buf.length) throw new Error(`trailing bytes in preimage (${buf.length - pos})`);
  return { inputs, privateTranscript, publicTranscriptInputs, publicTranscriptOutputs, bindingInput, commitment, keyLocation };
}

export function serializePreimage(p) {
  const out = [...Buffer.from(TAG, 'latin1')];
  const vec = (xs) => { writeCompact(out, xs.length); xs.forEach((x) => writeCompact(out, x)); };
  vec(p.inputs); vec(p.privateTranscript); vec(p.publicTranscriptInputs); vec(p.publicTranscriptOutputs);
  writeCompact(out, p.bindingInput);
  if (p.commitment) { out.push(1); writeCompact(out, p.commitment[0]); writeCompact(out, p.commitment[1]); } else out.push(0);
  const key = Buffer.from(p.keyLocation, 'utf-8');
  writeCompact(out, key.length);
  out.push(...key);
  return Uint8Array.from(out);
}

/** One field element in the runtime's untagged serialized form, as hex (e.g. `CommunicationCommitment`). */
export const frToHex = (x) => { const out = []; writeCompact(out, x); return Buffer.from(out).toString('hex'); };
export const frFromHex = (h) => {
  const buf = Uint8Array.from(Buffer.from(h, 'hex'));
  const [v, pos] = readCompact(buf, 0);
  if (pos !== buf.length) throw new Error(`trailing bytes in serialized field element ${h}`);
  return v;
};
