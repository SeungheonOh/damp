// JSON helpers that survive bigint / Uint8Array / Map values.
//   bigint      -> "123n"
//   Uint8Array  -> "0x<hex>"   (empty array -> "0x")
//   Map         -> {"$map": [[k, v], ...]}
export const replacer = (_k, v) => {
  if (typeof v === 'bigint') return `${v}n`;
  if (v instanceof Uint8Array) return '0x' + Buffer.from(v).toString('hex');
  if (v instanceof Map) return { $map: [...v.entries()] };
  return v;
};

export const toJson = (x, indent = 2) => JSON.stringify(x, replacer, indent);

/** Pick the four ProofData fields (drops QueryContext objects etc. from CallProofData). */
export const proofDataOf = (cpd) => ({
  input: cpd.input,
  output: cpd.output,
  publicTranscript: cpd.publicTranscript,
  privateTranscriptOutputs: cpd.privateTranscriptOutputs,
});
