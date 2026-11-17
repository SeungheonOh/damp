// Generic executor for Damp contracts.
//
// One interpreter for every contract: it walks the circuit IR exported by the
// Lean compiler (contract.json), the same statement list the ZKIR was emitted
// from. It calls witnesses, runs ledger operations through the Compact runtime
// and records the proof data the prover checks against the circuit.
//
// What it does is DEFINED by `Exec.run` in Damp/Executor.lean (with
// `Expr.eval` and `Range.holds` from Damp/Semantics.lean); the section "the
// definition" below mirrors it clause by clause, and test/executor.sh checks
// the two against each other. See docs/executor.md.
//
// Inside a circuit every value is a field element (BigInt). Types only matter
// at the boundary: arguments, results, witness values and ledger cells.

import * as rt from '@midnight-ntwrk/compact-runtime';

/** The contract.json format this executor reads (Damp/Export.lean writes it). */
export const FORMAT = 'damp-contract/5';

export const MODULUS = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001n;
const mod = (x) => ((x % MODULUS) + MODULUS) % MODULUS;

const bitLen = (n) => (n === 0n ? 0 : n.toString(2).length);

// ---------------------------------------------------------------- bytes
//
// `n` bytes occupy ceil(n/31) field elements ("limbs"), most significant limb
// first: with X the bytes read as a little-endian integer,
// limb[j] = (X >> 248·(L−1−j)) mod 2^248.

const LIMB = 248n;
const LIMB_MASK = (1n << LIMB) - 1n;
const byteLimbs = (n) => Math.ceil(n / 31);

function bytesToLimbs(bytes, n) {
  let x = 0n;
  for (let i = Math.min(bytes.length, n) - 1; i >= 0; i--) x = (x << 8n) | BigInt(bytes[i]);
  const count = byteLimbs(n);
  return Array.from({ length: count }, (_, j) => (x >> (LIMB * BigInt(count - 1 - j))) & LIMB_MASK);
}

function limbsToBytes(limbs, n) {
  let x = 0n;
  for (const limb of limbs) x = (x << LIMB) | limb;
  const out = new Uint8Array(n);
  for (let i = 0; i < n; i++) { out[i] = Number(x & 0xffn); x >>= 8n; }
  return out;
}

const stripTrailingZeros = (bytes) => {
  let end = bytes.length;
  while (end > 0 && bytes[end - 1] === 0) end--;
  return bytes.slice(0, end);
};

// ---------------------------------------------------------------- primitive types

const descriptor = (ty) => {
  switch (ty.kind) {
    case 'field': return rt.CompactTypeField;
    case 'bool': return rt.CompactTypeBoolean;
    case 'uint': {
      const max = BigInt(ty.max);
      return new rt.CompactTypeUnsignedInteger(max, Math.ceil(bitLen(max) / 8));
    }
    case 'bytes': return new rt.CompactTypeBytes(ty.length);
    case 'enum': return new rt.CompactTypeEnum(ty.max, Math.max(1, Math.ceil(bitLen(BigInt(ty.max)) / 8)));
    default: throw new Error(`unknown type ${ty.kind}`);
  }
};

const widthOf = (ty) => (ty.kind === 'bytes' ? byteLimbs(ty.length) : 1);

/** Field elements of a primitive JS value. */
const toFields = (ty, v) => {
  switch (ty.kind) {
    case 'bool': return [v ? 1n : 0n];
    case 'bytes': return bytesToLimbs(v, ty.length);
    default: return [BigInt(v)];
  }
};

/** Primitive JS value from field elements; `next()` yields them in order. */
const fromFields = (ty, next) => {
  switch (ty.kind) {
    case 'bool': return next() === 1n;
    case 'bytes': return limbsToBytes(Array.from({ length: byteLimbs(ty.length) }, next), ty.length);
    case 'enum': return Number(next());
    default: return next();
  }
};

const zeroLeaf = (ty) => {
  switch (ty.kind) {
    case 'bool': return false;
    case 'bytes': return new Uint8Array(ty.length);
    case 'enum': return 0;
    default: return 0n;
  }
};

// ---------------------------------------------------------------- shapes
//
// A shape describes a value at the circuit boundary. JS conventions follow
// Compact's: structs are objects, vectors and tuples are arrays, Field and Uint
// are bigints, Boolean is a boolean, Bytes is a Uint8Array, an enum is the
// number of its variant.

/** Flatten a JS value to its primitive leaves, in circuit order. */
function flatten(shape, v, out = []) {
  switch (shape.kind) {
    case 'struct': shape.fields.forEach((f, i) => flatten(f, v[shape.fieldNames[i]], out)); break;
    case 'tuple': shape.elems.forEach((e, i) => flatten(e, v[i], out)); break;
    case 'vector':
      if (v.length !== shape.length) throw new rt.CompactError(`expected a vector of length ${shape.length}`);
      for (let i = 0; i < shape.length; i++) flatten(shape.elem, v[i], out);
      break;
    default: out.push({ ty: shape, val: v });
  }
  return out;
}

/** Rebuild a JS value from primitive leaves; `leaf(ty)` yields each in order. */
function build(shape, leaf) {
  switch (shape.kind) {
    case 'struct': return Object.fromEntries(shape.fields.map((f, i) => [shape.fieldNames[i], build(f, leaf)]));
    case 'tuple': return shape.elems.map((e) => build(e, leaf));
    case 'vector': return Array.from({ length: shape.length }, () => build(shape.elem, leaf));
    default: return leaf(shape);
  }
}

/** AlignedValue for primitive leaves. Going through the runtime's descriptors also type-checks them. */
const alignedOfLeaves = (leaves) => ({
  value: leaves.flatMap((l) => descriptor(l.ty).toValue(l.val)),
  alignment: leaves.flatMap((l) => descriptor(l.ty).alignment()),
});

const alignedOfShape = (shape, v) => alignedOfLeaves(flatten(shape, v));
const fieldsOfLeaves = (leaves) => leaves.flatMap((l) => toFields(l.ty, l.val));

// ---------------------------------------------------------------- aligned values from the IR

const atomJson = (a) =>
  a.kind === 'bytes'
    ? { tag: 'atom', value: { tag: 'bytes', length: a.length } }
    : { tag: 'atom', value: { tag: a.kind } };

const atomWidth = (a) => (a.kind === 'bytes' ? Math.max(1, byteLimbs(a.length)) : 1);

/** AlignedValue for field elements under an alignment from the IR. */
function alignedOfFields(align, vals) {
  let k = 0;
  const value = align.map((a) => {
    const limbs = vals.slice(k, (k += atomWidth(a)));
    return a.kind === 'bytes' && a.length > 31
      ? stripTrailingZeros(limbsToBytes(limbs, a.length))
      : rt.bigIntToValue(limbs[0])[0];
  });
  return { value, alignment: align.map(atomJson) };
}

/** Field elements of an AlignedValue read back from the ledger. */
function fieldsOfAligned(align, value) {
  return align.flatMap((a, i) =>
    a.kind === 'bytes' && a.length > 31 ? bytesToLimbs(value[i], a.length) : [rt.valueToBigInt([value[i]])]);
}

const asDescriptor = (aligned) => ({ alignment: () => aligned.alignment, toValue: () => aligned.value });

// ---------------------------------------------------------------- the definition
//
// From here to "ledger view", the code mirrors the Lean definition of what the
// executor does, clause by clause:
//
//   Damp/Semantics.lean   asBool, Expr.eval, Expr.evalList, Range.holds,
//                         ledgerGroups, bindInputs
//   Damp/Executor.lean    Exec.assign, Exec.blank, Exec.request, Exec.step,
//                         Exec.steps, Exec.run
//   Damp/Crypto/Prims.lean  persistentHash (the alignment parse)
//   Damp/Impact.lean      Op.mapM, Op.encode
//
// A Lean `none` is a thrown `Failure`: the call fails. Evaluation order is the
// Lean order (left to right through each `do` block), so the first failure is
// the one Lean meets. Each case names the clause it mirrors; docs/executor.md
// has the full correspondence. `test/executor.sh` checks the two against each
// other, statement by statement.

/** A `none` of the Lean definition. */
class Failure extends Error {}
const fail = (reason) => { throw new Failure(reason); };

/** `Fr.ofInt`. */
const frOfInt = (i) => mod(BigInt(i));

/** `Zkir.frBits` and `Zkir.fitsBits x n = n < frBits && x.val < 2 ^ n`. */
const FR_BITS = 255;
const fitsBits = (x, n) => Number(n) < FR_BITS && x < 1n << BigInt(n);

/** `asBool`: 0 is false, 1 is true, anything else fails. */
const asBool = (x, what) => {
  if (x === 0n) return false;
  if (x === 1n) return true;
  return fail(`${what} is ${x}, neither 0 nor 1`);
};

// ---------------------------------------------------------------- hashes (the `Prims`)

/** `Prims.transientHash`: Poseidon over field elements, by the runtime. */
const transientHash = (xs) =>
  rt.transientHash(asDescriptor({ value: xs.map(fieldAtomValue), alignment: xs.map(() => atomJson({ kind: 'field' })) }), null);

const fieldAtomValue = (x) => rt.bigIntToValue(x)[0] ?? new Uint8Array(0);

/**
 * `Crypto.binaryRepr` as a parse: the atoms of an AlignedValue read from field
 * elements under `align`, or null where Lean's `parseAtom` gives `none`.
 * Surplus elements are ignored, as upstream.
 */
function parseAligned(align, xs) {
  const value = [];
  let k = 0;
  for (const a of align) {
    switch (a.kind) {
      // | .compress, _ => none
      case 'compress': return null;
      // | .field, [] => none | .field, f :: rest => some (leBytes 32 f.val, rest)
      case 'field':
        if (k >= xs.length) return null;
        value.push(fieldAtomValue(xs[k++]));
        break;
      // | .bytes n, repr => parseBytesAtom n repr
      case 'bytes': {
        const n = Number(a.length), stray = n % 31, chunks = Math.floor(n / 31);
        if (xs.length - k < chunks + (stray !== 0 ? 1 : 0)) return null;
        // The stray element holds the last `stray` bytes and must fit them;
        // then `chunks` elements below 2^248, most significant first.
        let x = 0n;
        if (stray !== 0) {
          const f = xs[k++];
          if (f >= 1n << BigInt(8 * stray)) return null;
          x = f;
        }
        for (let j = 0; j < chunks; j++) {
          const f = xs[k++];
          if (f >= 1n << LIMB) return null;
          x = (x << LIMB) | f;
        }
        const bytes = new Uint8Array(n);
        for (let i = 0; i < n; i++) { bytes[i] = Number(x & 0xffn); x >>= 8n; }
        value.push(stripTrailingZeros(bytes));
        break;
      }
      default: throw new Error(`unknown alignment atom ${a.kind}`);
    }
  }
  return { value, alignment: align.map(atomJson) };
}

/** `Prims.persistentHash` (`Crypto.persistentHash`): 32 bytes, or null when the elements do not fit. */
function persistentHash(align, xs) {
  const aligned = parseAligned(align, xs);
  if (aligned === null) return null;
  const digest = new Uint8Array(32);   // the runtime strips trailing zero bytes
  digest.set(rt.persistentHash(asDescriptor(aligned), null));
  return digest;
}

/** `Zkir.bytesToNatives`: 31 bytes per element, least significant first. */
function bytesToNatives(bs) {
  const le = (chunk) => chunk.reduceRight((acc, b) => acc * 256n + BigInt(b), 0n);
  if (bs.length <= 31) return [mod(le(bs))];
  return [mod(le(bs.slice(0, 31))), ...bytesToNatives(bs.slice(31))];
}

// ---------------------------------------------------------------- Expr.eval

function evalExpr(e, env) {
  switch (e.kind) {
    // | .var v => some (env v)          (the environment starts as `fun _ => 0`)
    case 'var': return env.get(e.var) ?? 0n;
    // | .const c => some (Fr.ofInt c)
    case 'const': return frOfInt(e.value);
    // | .invalid _ => none
    case 'invalid': return fail(`invalid expression (${e.msg})`);
    // | .disclose e => e.eval   (not exported: Export.expr writes `e` itself)
    // | .add a b => do let x ← a.eval; let y ← b.eval; pure (x + y)
    case 'add': { const x = evalExpr(e.a, env); const y = evalExpr(e.b, env); return mod(x + y); }
    // | .mul a b => do let x ← a.eval; let y ← b.eval; pure (x * y)
    case 'mul': { const x = evalExpr(e.a, env); const y = evalExpr(e.b, env); return mod(x * y); }
    // | .neg a => do let x ← a.eval; pure (-x)
    case 'neg': return mod(-evalExpr(e.a, env));
    // | .lt bits a b => do let x ← a.eval; let y ← b.eval;
    //     if fitsBits x bits && fitsBits y bits then pure (Fr.ofBool (x.val < y.val)) else none
    case 'lt': {
      const x = evalExpr(e.a, env);
      const y = evalExpr(e.b, env);
      if (fitsBits(x, e.bits) && fitsBits(y, e.bits)) return x < y ? 1n : 0n;
      return fail(`comparison at ${e.bits} bits of ${x} and ${y}: ${Number(e.bits) < FR_BITS ? 'an operand does not fit' : 'the width is not below 255'}`);
    }
    // | .eq a b => do let x ← a.eval; let y ← b.eval; pure (Fr.ofBool (x = y))
    case 'eq': { const x = evalExpr(e.a, env); const y = evalExpr(e.b, env); return x === y ? 1n : 0n; }
    // | .select c a b => do let c ← c.eval; let x ← a.eval; let y ← b.eval;
    //     let c ← asBool c; pure (if c then x else y)        (both branches evaluated)
    case 'select': {
      const c = evalExpr(e.c, env);
      const x = evalExpr(e.a, env);
      const y = evalExpr(e.b, env);
      return asBool(c, 'select condition') ? x : y;
    }
    // | .hash xs => do let xs ← Expr.evalList xs; pure (p.transientHash xs)
    // | .divmod quot bits a => x ← a.eval; if bits ≤ 248 then x / 2^bits or x % 2^bits else none
    case 'divmod': {
      const x = evalExpr(e.a, env);
      if (e.bits > 248) fail(`division by 2^${e.bits}: the width may not exceed 248`);
      const n = BigInt(e.bits);
      return e.quot ? x >> n : x & ((1n << n) - 1n);
    }
    case 'hash': return transientHash(evalList(e.xs, env));
    // | .phash high align xs => do let xs ← Expr.evalList xs; let digest ← p.persistentHash align xs;
    //     match bytesToNatives digest with | [lo, hi] => pure (if high then hi else lo) | _ => none
    case 'phash': {
      const xs = evalList(e.xs, env);
      const digest = persistentHash(e.align, xs);
      if (digest === null) return fail(`persistent hash: [${xs}] do not fit the alignment`);
      const natives = bytesToNatives(digest);
      if (natives.length !== 2) return fail('persistent hash: digest is not two elements');
      return e.high ? natives[1] : natives[0];
    }
    default: throw new Error(`unknown expression ${e.kind}`);
  }
}

/** `Expr.evalList`: left to right, the first failure fails. */
const evalList = (xs, env) => xs.map((x) => evalExpr(x, env));

// ---------------------------------------------------------------- Range.holds

const showRange = (r) =>
  r.kind === 'bits' ? `bits ${r.n}` : r.kind === 'below' ? `below ${r.bound} (width ${r.width})` : r.kind;

function rangeHolds(r, x) {
  switch (r.kind) {
    // | .zero => x = 0
    case 'zero': return x === 0n;
    // | .bool => x = 0 || x = 1
    case 'bool': return x === 0n || x === 1n;
    // | .bits n => fitsBits x n
    case 'bits': return fitsBits(x, r.n);
    // | .below bound width => fitsBits x width && fitsBits (Fr.ofInt bound) width
    //                         && x.val < (Fr.ofInt bound).val
    case 'below': {
      if (r.width === undefined) throw new Error('range `below` without its width (contract.json older than damp-contract/5?)');
      const bound = frOfInt(r.bound);
      return fitsBits(x, r.width) && fitsBits(bound, r.width) && x < bound;
    }
    default: throw new Error(`unknown range ${r.kind}`);
  }
}

// ---------------------------------------------------------------- Exec.assign, bindInputs

/**
 * `Exec.assign`: bind each variable to its value, checking its range first.
 * `outs` is a list of `{ var, range }` (range null for none). The counts must match.
 */
function assign(env, outs, vals, what) {
  let k = 0;
  // | (v, range) :: rest, x :: xs => if r.holds x then assign (env.set v x) rest xs else none
  for (; k < outs.length && k < vals.length; k++) {
    const { var: v, range } = outs[k];
    if (range && !rangeHolds(range, vals[k])) fail(`${what}: value ${k} is ${vals[k]}, not in range ${showRange(range)}`);
    env.set(v, vals[k]);
  }
  // | [], [] => some env | _, _ => none
  if (outs.length !== vals.length) fail(`${what}: ${vals.length} value(s) for ${outs.length} variable(s)`);
}

/** `bindInputs (fun _ => 0)`: the counts must match. */
function bindInputs(vars, inputs) {
  if (vars.length !== inputs.length) fail(`${inputs.length} input(s) for ${vars.length} input variable(s)`);
  const env = new Map();
  vars.forEach((v, k) => env.set(v, inputs[k]));
  return env;
}

// ---------------------------------------------------------------- ledger instructions (Damp/Impact.lean)

/** `Aligned.mapM`, `StateLit.mapM`, `Op.mapM`: apply `f` to every operand, in order. */
const mapAligned = (v, f) => ({ align: v.align, vals: v.vals.map(f) });
function mapStateLit(v, f) {
  switch (v.kind) {
    case 'cell': return { ...v, value: mapAligned(v.value, f) };
    case 'array': return { ...v, elems: v.elems.map((e) => mapStateLit(e, f)) };
    default: return v;   // null, map, merkleTree: no operands
  }
}
function mapOp(op, f) {
  switch (op.kind) {
    case 'popeq': return { ...op, result: op.result.map(f) };
    case 'addi':
    case 'subi': return { ...op, immediate: f(op.immediate) };
    case 'push': return { ...op, value: mapAligned(op.value, f) };
    case 'idx': return { ...op, path: op.path.map((k) => mapAligned(k, f)) };
    case 'idxStack': return { ...op, path: op.path.map((k) => mapAligned(k, f)) };
    case 'pushState': return { ...op, value: mapStateLit(op.value, f) };
    default: return op;
  }
}

/** `Impact.atomCode`. */
const atomCode = (a) => (a.kind === 'bytes' ? a.length : a.kind === 'compress' ? -1 : -2);

/**
 * `Op.encode`: the field elements an instruction contributes to the public
 * inputs. Constants are `Fr.ofInt`; each operand goes through `f`, in the
 * order the encoding lists them.
 */
function encodeOp(op, f) {
  const c = frOfInt;
  const aligned = (v) => [c(v.align.length), ...v.align.map((a) => c(atomCode(a))), ...v.vals.map(f)];
  const stateLit = (v) => {
    switch (v.kind) {
      case 'null': return [c(0)];
      case 'cell': return [c(1), ...aligned(v.value)];
      case 'map': return [c(0x02)];
      case 'array': return [c(16 * v.elems.length + 3), ...v.elems.flatMap(stateLit)];
      case 'merkleTree': return [c(16 * v.depth + 4)];
      default: throw new Error(`unknown state value ${v.kind}`);
    }
  };
  const store = (s) => c(s ? 0x11 : 0x10);
  switch (op.kind) {
    case 'lt': return [c(0x01)];
    case 'eq': return [c(0x02)];
    case 'type': return [c(0x03)];
    case 'size': return [c(0x04)];
    case 'and': return [c(0x06)];
    case 'or': return [c(0x07)];
    case 'neg': return [c(0x08)];
    case 'log': return [c(0x09)];
    case 'root': return [c(0x0a)];
    case 'pop': return [c(0x0b)];
    case 'popeq': return [c(op.cached ? 0x0d : 0x0c), c(op.align.length), ...op.align.map((a) => c(atomCode(a))), ...op.result.map(f)];
    case 'addi': return [c(0x0e), f(op.immediate)];
    case 'subi': return [c(0x0f), f(op.immediate)];
    case 'push': return [store(op.storage), c(1), ...aligned(op.value)];
    case 'pushNull': return [store(op.storage), c(0)];
    case 'add': return [c(0x14)];
    case 'sub': return [c(0x15)];
    case 'member': return [c(0x18)];
    case 'rem': return [c(op.cached ? 0x1a : 0x19)];
    case 'dup': return [c(0x30 + op.n)];
    case 'swap': return [c(0x40 + op.n)];
    case 'idx': {
      const base = op.cached ? (op.pushPath ? 0x80 : 0x60) : (op.pushPath ? 0x70 : 0x50);
      return [c(base + Math.max(0, op.path.length - 1)), ...op.path.flatMap(aligned)];
    }
    case 'ins': return [c((op.cached ? 0xa0 : 0x90) + op.n)];
    case 'ckpt': return [c(0xff)];
    case 'pushState': return [store(op.storage), ...stateLit(op.value)];
    case 'branch': return [c(0x12), c(op.skip)];
    case 'jmp': return [c(0x13), c(op.skip)];
    case 'concat': return [c(0x16), c(op.n)];
    case 'idxStack': return [c(0x60 + op.path.length), ...op.path.flatMap(aligned), c(-1)];
    case 'concatCached': return [c(0x17), c(op.n)];
    default: throw new Error(`unknown ledger op ${op.kind}`);
  }
}

/** `Exec.blank`: an instruction as sent to the ledger, its `popeq` result not yet known. */
const blank = (op) => (op.kind === 'popeq' ? { ...op, result: [] } : op);

/** `Exec.request`: every operand of every instruction evaluated, in order, then blanked. */
const request = (ops, env) => ops.map((op) => blank(mapOp(op, (x) => evalExpr(x, env))));

/**
 * `ledgerGroups`: one group of public inputs per instruction. Every operand is
 * evaluated whether or not the statement is active; the values are zeroed if not.
 */
const ledgerGroups = (env, active, ops) =>
  ops.map((op) => {
    const vals = encodeOp(op, (x) => evalExpr(x, env));
    return { active, vals: active ? vals : vals.map(() => 0n) };
  });

// ---------------------------------------------------------------- Exec.step

/**
 * `Exec.step`. `st` is the part of `Exec.State` the interpreter keeps itself
 * (env, priv, pub, groups); the private state and the ledger state live in the
 * runtime context and change only through the oracles `io.witness` and
 * `io.ledger`. Each oracle returns the answer and a `commit` that installs the
 * new private / ledger state once the statement has succeeded (in Lean the
 * new state is part of the step's result).
 */
async function step(io, st, s, ev) {
  switch (s.kind) {
    // | .bind v _ e => do let x ← e.eval; pure { s with env := s.env.set v x }
    case 'bind':
      st.env.set(s.var, evalExpr(s.expr, st.env));
      return;

    // | .assert cond _ => do let c ← cond.eval; let c ← asBool c; if c then pure s else none
    case 'assert': {
      const c = evalExpr(s.cond, st.env);
      if (!asBool(c, `condition of assert "${s.msg}"`)) fail(`failed assert: ${s.msg}`);
      return;
    }

    // | .constrain e r => do let x ← e.eval; if r.holds x then pure s else none
    case 'constrain': {
      const x = evalExpr(s.expr, st.env);
      if (!rangeHolds(s.range, x)) fail(`value ${x} out of range ${showRange(s.range)}`);
      return;
    }

    // | .witness guard name args outs _ => do
    case 'witness': {
      //   let g ← guard.eval p s.env
      const g = evalExpr(s.guard, st.env);
      //   if outs.isEmpty then
      //     if g = 1 then (ask the witness; it must return nothing; keep the new private state)
      //     else pure s
      if (s.outs.length === 0) {
        if (g === 1n) {
          const argVals = evalList(s.args, st.env);
          const { vals, commit } = await io.witness(s, argVals, ev);
          if (vals.length !== 0) fail(`witness ${s.name} returned a value where none is declared`);
          commit();
        }
        return;
      }
      //   let active ← asBool g
      if (asBool(g, `guard of witness ${s.name}`)) {
        //   let argVals ← Expr.evalList p s.env args
        const argVals = evalList(s.args, st.env);
        //   let (vals, private_) ← O.witness name argVals s.private_
        const { vals, commit } = await io.witness(s, argVals, ev);
        //   let env ← assign s.env outs vals
        assign(st.env, s.outs, vals, `result of witness ${s.name}`);
        //   pure { s with env, private_, priv := s.priv ++ vals }
        st.priv.push(...vals);
        commit();
      } else {
        //   let env ← assign s.env outs (outs.map fun _ => 0); pure { s with env }
        assign(st.env, s.outs, s.outs.map(() => 0n), `zero result of witness ${s.name}, not asked`);
      }
      return;
    }

    // | .ledger guard reads ops => do
    case 'ledger': {
      //   let g ← guard.eval p s.env
      const g = evalExpr(s.guard, st.env);
      //   if reads.isEmpty && ops.isEmpty then pure s
      if (s.reads.length === 0 && s.ops.length === 0) return;
      const reads = s.reads.map((v) => ({ var: v, range: null }));
      //   let active ← asBool g
      if (asBool(g, 'guard of ledger statement')) {
        //   let req ← request p s.env ops
        const req = request(s.ops, st.env);
        //   let (vals, ledger) ← O.ledger req s.ledger
        const { vals, commit } = io.ledger(req, ev);
        //   let env ← assign s.env (reads.map fun v => (v, none)) vals
        assign(st.env, reads, vals, 'ledger reads');
        //   let groups ← ledgerGroups p env true ops
        const groups = ledgerGroups(st.env, true, s.ops);
        //   pure { s with env, ledger, pub := s.pub ++ vals, groups := s.groups ++ groups }
        st.pub.push(...vals);
        st.groups.push(...groups);
        commit();
      } else {
        //   let env ← assign s.env (reads.map fun v => (v, none)) (reads.map fun _ => 0)
        assign(st.env, reads, reads.map(() => 0n), 'zero reads of ledger statement, not run');
        //   let groups ← ledgerGroups p env false ops; pure { s with env, groups := s.groups ++ groups }
        st.groups.push(...ledgerGroups(st.env, false, s.ops));
      }
      return;
    }

    default: throw new Error(`unknown statement ${s.kind}`);
  }
}

// ---------------------------------------------------------------- the oracles, through the runtime

/** A runtime instruction from one whose operands are field elements (as `request` makes them). */
function runtimeOp(op) {
  const aligned = (v) => alignedOfFields(v.align, v.vals);
  if (SIMPLE_OPS.has(op.kind)) return op.kind;
  switch (op.kind) {
    case 'dup': return { dup: { n: op.n } };
    case 'swap': return { swap: { n: op.n } };
    case 'idx':
      return { idx: { cached: op.cached, pushPath: op.pushPath, path: op.path.map((k) => ({ tag: 'value', value: aligned(k) })) } };
    case 'popeq': return { popeq: { cached: op.cached, result: undefined } };
    case 'push': return { push: { storage: op.storage, value: rt.StateValue.newCell(aligned(op.value)).encode() } };
    case 'pushNull': return { push: { storage: op.storage, value: rt.StateValue.newNull().encode() } };
    case 'pushState': return { push: { storage: op.storage, value: stateValueOf(op.value, aligned).encode() } };
    case 'branch': return { branch: { skip: op.skip } };
    case 'jmp': return { jmp: { skip: op.skip } };
    case 'concat': return { concat: { cached: false, n: op.n } };
    case 'idxStack':
      return { idx: { cached: true, pushPath: false, path: [...op.path.map((k) => ({ tag: 'value', value: aligned(k) })), { tag: 'stack' }] } };
    case 'concatCached': return { concat: { cached: true, n: op.n } };
    case 'ins': return { ins: { cached: op.cached, n: op.n } };
    case 'rem': return { rem: { cached: op.cached } };
    case 'addi': return { addi: { immediate: Number(op.immediate) } };
    case 'subi': return { subi: { immediate: Number(op.immediate) } };
    default: throw new Error(`unknown ledger op ${op.kind}`);
  }
}

const SIMPLE_OPS = new Set(['lt', 'eq', 'type', 'size', 'and', 'or', 'neg', 'log', 'root', 'pop', 'add', 'sub', 'member', 'ckpt']);

/** A runtime StateValue from a literal state value. */
function stateValueOf(v, aligned) {
  switch (v.kind) {
    case 'null': return rt.StateValue.newNull();
    case 'cell': return rt.StateValue.newCell(aligned(v.value));
    case 'map': return rt.StateValue.newMap(new rt.StateMap());
    case 'array': return v.elems.reduce((arr, e) => arr.arrayPush(stateValueOf(e, aligned)), rt.StateValue.newArray());
    case 'merkleTree': return rt.StateValue.newBoundedMerkleTree(new rt.StateBoundedMerkleTree(v.depth));
    default: throw new Error(`unknown state value ${v.kind}`);
  }
}

/** Field elements read by the `popeq`s of the instructions just appended to the transcript. */
function readsOf(ops, recorded) {
  const out = [];
  ops.forEach((op, i) => {
    if (op.kind === 'popeq') out.push(...fieldsOfAligned(op.align, recorded[i].popeq.result.value));
  });
  return out;
}

const isFieldElement = (x) => typeof x === 'bigint' && x >= 0n && x < MODULUS;
const errorText = (e) => (e instanceof Error ? e.message : String(e));

/**
 * The two oracles of `Exec.Oracles`, implemented with the user's witnesses and
 * the runtime's ledger VM. An oracle that refuses (`none`) throws a Failure.
 */
function oracles(spec, witnesses, context, ppd) {
  const cc = context.callContext;
  return {
    // O.witness name argVals private_ : the field elements of the witness's
    // result. The JS value is converted at the boundary: it must be a value of
    // the witness's declared shape (the runtime's descriptors check it), else
    // the oracle refuses.
    witness(s, argVals, ev) {
      ev.witness = { name: s.name, args: argVals, answer: null };
      if (Object.hasOwn(BUILTIN_WITNESSES, s.name)) return builtinWitness(s, argVals, ev, context, ppd);
      if (isCallWitness(s.name)) return callWitness(spec, s, argVals, ev, context, ppd);
      const impl = witnesses[s.name];
      if (typeof impl !== 'function') fail(`no implementation for witness ${s.name}`);
      let next, aligned, vals;
      try {
        const wctx = rt.createWitnessContext(
          ledgerView(spec, cc.currentQueryContext.state), cc.currentPrivateState, cc.currentQueryContext.address);
        const out = impl(wctx, ...argVals);
        if (!Array.isArray(out) || out.length !== 2) throw new Error('a witness must return [nextPrivateState, value]');
        [next] = out;
        const leaves = flatten(s.shape, out[1]);
        aligned = alignedOfLeaves(leaves);
        vals = fieldsOfLeaves(leaves);
        if (!vals.every(isFieldElement)) throw new Error('result is not made of field elements');
      } catch (e) {
        ev.witness.error = errorText(e);
        return fail(`witness ${s.name} refused: ${errorText(e)}`);
      }
      ev.witness.answer = vals;
      return {
        vals,
        commit: () => {
          cc.currentPrivateState = next;
          ppd.privateTranscriptOutputs.push(aligned);
        },
      };
    },
    // O.ledger req ledger : run the instructions; the field elements their
    // `popeq`s read, in order. The runtime updates its state as it runs them;
    // the call works on a copy of the caller's context, so a failure later in
    // the statement leaves the caller's state as it was.
    ledger(req, ev) {
      ev.ledger = { request: req.flatMap((op) => encodeOp(op, (x) => x)), answer: null };
      let vals;
      try {
        const ops = req.map(runtimeOp);
        const from = ppd.publicTranscript.length;
        rt.queryLedgerState(context, ppd, ops);
        vals = readsOf(req, ppd.publicTranscript.slice(from));
      } catch (e) {
        ev.ledger.error = errorText(e);
        return fail(`ledger refused: ${errorText(e)}`);
      }
      ev.ledger.answer = vals;
      return { vals, commit: () => {} };
    },
  };
}

// ---------------------------------------------------------------- built-in witnesses
//
// Compact's `ownPublicKey`, `createZswapInput` and `createZswapOutput` are
// witnesses whose implementation is the runtime's, not the user's: they read
// and extend the call's Zswap local state (`context.callContext.
// currentZswapLocalState`), exactly as compactc's generated module calls them.
// To the definition (`Exec.step`) they are witnesses like any other. Their
// argument shapes are fixed by the standard library (Damp/Tokens.lean), so the
// field elements of their arguments are turned back into the JS values the
// runtime expects here.

const BYTES32 = { kind: 'bytes', length: 32 };
const U128 = { kind: 'uint', max: ((1n << 128n) - 1n).toString() };
const bytesStruct = (name) => ({ kind: 'struct', name, fieldNames: ['bytes'], fields: [BYTES32] });
const COIN_FIELDS = ['nonce', 'color', 'value'];
const COIN = { kind: 'struct', name: 'ShieldedCoinInfo', fieldNames: COIN_FIELDS, fields: [BYTES32, BYTES32, U128] };
const QUALIFIED_COIN = {
  kind: 'struct', name: 'QualifiedShieldedCoinInfo', fieldNames: [...COIN_FIELDS, 'mt_index'],
  fields: [BYTES32, BYTES32, U128, { kind: 'uint', max: ((1n << 64n) - 1n).toString() }],
};
const RECIPIENT = {
  kind: 'struct', name: 'Either', fieldNames: ['is_left', 'left', 'right'],
  fields: [{ kind: 'bool' }, bytesStruct('ZswapCoinPublicKey'), bytesStruct('ContractAddress')],
};

/** Each built-in: the shapes of its arguments, and what it does given them as JS values. */
const BUILTIN_WITNESSES = {
  ownPublicKey: { args: [], run: (context) => rt.ownPublicKey(context) },
  createZswapInput: { args: [QUALIFIED_COIN], run: (context, coin) => rt.createZswapInput(context, coin) },
  createZswapOutput: {
    args: [COIN, RECIPIENT],
    run: (context, coin, recipient) => rt.createZswapOutput(context, coin, recipient),
  },
};

/** The names a contract's own witnesses may not use. */
export const RESERVED_WITNESSES = Object.freeze(Object.keys(BUILTIN_WITNESSES));

/**
 * `O.witness` for a built-in: decode the arguments, run the runtime function on
 * the call's context when the statement commits (it updates the Zswap local
 * state), and answer with the field elements of its result.
 */
function builtinWitness(s, argVals, ev, context, ppd) {
  const b = BUILTIN_WITNESSES[s.name];
  let args, vals, aligned, result;
  try {
    let k = 0;
    const next = () => {
      if (k >= argVals.length) throw new Error('too few arguments');
      return argVals[k++];
    };
    args = b.args.map((shape) => build(shape, (ty) => fromFields(ty, next)));
    if (k !== argVals.length) throw new Error(`${argVals.length} argument field element(s) for ${k}`);
    // The arguments must convert back to exactly the field elements given.
    const back = fieldsOfLeaves(b.args.flatMap((shape, i) => flatten(shape, args[i])));
    if (back.some((x, i) => x !== argVals[i])) throw new Error('arguments are not values of their types');
    // Only `ownPublicKey` has a result, and it changes nothing; the others are
    // run at commit, when they change the Zswap local state.
    result = s.name === 'ownPublicKey' ? b.run(context) : [];
    const leaves = flatten(s.shape, result);
    aligned = alignedOfLeaves(leaves);
    vals = fieldsOfLeaves(leaves);
  } catch (e) {
    ev.witness.error = errorText(e);
    return fail(`built-in witness ${s.name} refused: ${errorText(e)}`);
  }
  ev.witness.answer = vals;
  return {
    vals,
    commit: () => {
      if (s.name !== 'ownPublicKey') b.run(context, ...args);
      ppd.privateTranscriptOutputs.push(aligned);
    },
  };
}

// ---------------------------------------------------------------- cross-contract calls
//
// A call of circuit `c` of a contract of type `I` (an `interface` in Lean;
// Compact's `contract I { … }`) is, in the IR, a witness named `call:I.c`
// whose arguments are the callee's address (2 field elements) and the call's
// arguments, and whose answer is the callee's results followed by the random
// opening of the communication commitment (Damp/Calls.lean). To the definition
// it is a witness like any other. The executor answers it by running the
// callee through the runtime's `crossContractCall`, exactly what compactc's
// module does at the call site: the runtime resolves the callee's module
// (`context.moduleProvider`) and deployed state (`context.stateProvider`),
// checks the module against the declared contract type and its verifier key
// fingerprints against the deployed keys, runs the callee's circuit on its own
// query context (its proof data goes onto `context.callProofDataTrace`), and
// samples the opening. The runtime also makes the kernel claim of the call on
// the caller's query context; in Damp that claim is an instruction sequence of
// the caller's circuit (the ledger statement after the witness), so the
// runtime's own claim is undone here and the circuit's runs instead: the same
// instructions with the same operands, so the same transcript and state.

export const CALL_PREFIX = 'call:';
const isCallWitness = (name) => typeof name === 'string' && name.startsWith(CALL_PREFIX);

/** The contract type and declared circuit a call witness names, from `spec.interfaces`. */
function calleeOf(spec, name) {
  const rest = name.slice(CALL_PREFIX.length);
  const dot = rest.lastIndexOf('.');
  const iface = (spec.interfaces ?? []).find((i) => i.name === rest.slice(0, dot));
  return { iface, circuit: iface?.circuits.find((c) => c.name === rest.slice(dot + 1)) };
}

const isInterface = (spec, shape) =>
  shape.kind === 'struct' && shape.fieldNames.length === 1 && shape.fieldNames[0] === 'bytes' &&
  (spec.interfaces ?? []).some((i) => i.name === shape.name);

/**
 * A shape as a signature type (the runtime's `SignatureType`, compactc's
 * `circuitSignatures` / `declaredInterfaces`). A struct shape named after one
 * of the contract's contract types is that contract type. Damp's enum shape
 * carries neither the enum's name nor its variants' names, so an enum is
 * written with placeholders: it conforms to a Damp contract's, not to
 * compactc's.
 */
function signatureType(spec, shape) {
  switch (shape.kind) {
    case 'field': return { tag: 'Field' };
    case 'bool': return { tag: 'Boolean' };
    case 'uint': return { tag: 'Uint', maxval: String(shape.max) };
    case 'bytes': return { tag: 'Bytes', length: Number(shape.length) };
    case 'enum':
      return { tag: 'Enum', name: 'enum', elements: Array.from({ length: Number(shape.max) + 1 }, (_, i) => String(i)) };
    case 'struct':
      if (isInterface(spec, shape)) {
        return { tag: 'Contract', name: shape.name, circuits: declarationOf(spec, spec.interfaces.find((i) => i.name === shape.name)) };
      }
      return { tag: 'Struct', name: shape.name, elements: shape.fields.map((f, i) => ({ name: shape.fieldNames[i], type: signatureType(spec, f) })) };
    case 'tuple': return { tag: 'Tuple', types: shape.elems.map((e) => signatureType(spec, e)) };
    case 'vector': return { tag: 'Vector', length: Number(shape.length), type: signatureType(spec, shape.elem) };
    default: throw new Error(`unknown shape ${shape.kind}`);
  }
}

/** A contract type as the runtime's `InterfaceDescriptor` (compactc's `declaredInterfaces[I]`). */
export function declarationOf(spec, iface) {
  return Object.fromEntries(iface.circuits.map((c) => [c.name, {
    argumentTypes: c.args.map((a) => signatureType(spec, a.shape)),
    resultType: signatureType(spec, c.result),
  }]));
}

/** compactc's `circuitSignatures` for a Damp contract: what a caller's runtime checks it against. */
export function circuitSignatures(spec) {
  return Object.fromEntries(spec.circuits.map((c) => [c.name, {
    pure: !c.proof && !c.body.some((s) => s.kind === 'witness'),
    provable: !!c.proof,
    argumentTypes: c.args.map((a) => signatureType(spec, a.shape)),
    resultType: signatureType(spec, c.result),
  }]));
}

/** compactc's `declaredInterfaces` for a Damp contract. */
export const declaredInterfaces = (spec) =>
  Object.fromEntries((spec.interfaces ?? []).map((i) => [i.name, declarationOf(spec, i)]));

const alignedKey = (a) =>
  JSON.stringify(a, (_k, v) =>
    (v instanceof Uint8Array ? Array.from(v, (b) => b.toString(16).padStart(2, '0')).join('') : typeof v === 'bigint' ? `${v}` : v));

/**
 * `O.witness` for a cross-contract call: decode the address and arguments, run
 * the callee, and answer with the field elements of its result and of the
 * commitment's opening. The callee runs when the witness is asked: its answer
 * is its result. If the statement then fails, so does the whole call, whose
 * context is a copy, so nothing the callee did survives. At commit, the two
 * aligned values compactc's module records are pushed onto the private
 * transcript: the callee's output, then the opening.
 */
async function callWitness(spec, s, argVals, ev, context, ppd) {
  let vals, outputs;
  try {
    const { iface, circuit } = calleeOf(spec, s.name);
    if (!circuit) throw new Error(`not a circuit of a contract type declared in contract.json`);
    let k = 0;
    const next = () => {
      if (k >= argVals.length) throw new Error('too few arguments');
      return argVals[k++];
    };
    const address = fromFields(BYTES32, next);
    const args = circuit.args.map((a) => build(a.shape, (ty) => fromFields(ty, next)));
    if (k !== argVals.length) throw new Error(`${argVals.length} argument field element(s) for ${k}`);
    const back = [...toFields(BYTES32, address), ...fieldsOfLeaves(circuit.args.flatMap((a, i) => flatten(a.shape, args[i])))];
    if (back.some((x, i) => x !== argVals[i])) throw new Error('arguments are not values of their types');

    // The runtime's own claim of the call is undone: the circuit claims it.
    const cc = context.callContext;
    const self = cc.contractAddress;
    const saved = { qc: cc.currentQueryContext, gas: cc.currentGasCost, cell: context.queryContexts?.[self], cost: context.gasCosts?.[self] };
    const scratch = emptyProofData();
    const result = await rt.crossContractCall({
      context,
      interfaceName: iface.name,
      declaration: declarationOf(spec, iface),
      calleeCircuitId: circuit.name,
      calleeAddress: rt.decodeContractAddress(address),
      partialProofData: scratch,
      args,
    });
    cc.currentQueryContext = saved.qc;
    cc.currentGasCost = saved.gas;
    if (context.queryContexts) context.queryContexts[self] = saved.cell;
    if (context.gasCosts) context.gasCosts[self] = saved.cost;

    outputs = scratch.privateTranscriptOutputs;
    if (outputs.length !== 2) throw new Error(`the runtime recorded ${outputs.length} private outputs, expected 2`);
    const leaves = flatten(circuit.result, result);
    if (alignedKey(alignedOfLeaves(leaves)) !== alignedKey(outputs[0])) {
      throw new Error('the callee\'s output is not its result as the contract type declares it');
    }
    vals = [...fieldsOfLeaves(leaves), rt.valueToBigInt(outputs[1].value)];
    if (!vals.every(isFieldElement)) throw new Error('result is not made of field elements');
  } catch (e) {
    ev.witness.error = errorText(e);
    return fail(`cross-contract call ${s.name.slice(CALL_PREFIX.length)} refused: ${errorText(e)}`);
  }
  ev.witness.answer = vals;
  return { vals, commit: () => { ppd.privateTranscriptOutputs.push(...outputs); } };
}

// ---------------------------------------------------------------- ledger view
//
// The public state as JS values, for witnesses and for applications reading a
// contract's state. Cells and counters are values; maps and sets are small
// objects. Other kinds are exposed as their raw StateValue.

const decodeAligned = (shape, aligned) => {
  const atoms = [...aligned.value];
  return build(shape, (ty) => descriptor(ty).fromValue(atoms));
};

/**
 * @param spec   the contract's `contract.json`
 * @param state  a ChargedState or StateValue holding the contract's ledger
 */
export function ledgerView(spec, state) {
  const root = state instanceof rt.StateValue ? state : state.state;
  const slots = root.asArray();
  const view = {};
  for (const f of spec.ledger) {
    const slot = () => slots[f.index];
    switch (f.type.kind) {
      case 'cell':
        Object.defineProperty(view, f.name, { enumerable: true, get: () => decodeAligned(f.type.shape, slot().asCell()) });
        break;
      case 'counter':
        Object.defineProperty(view, f.name, { enumerable: true, get: () => decodeAligned(U64, slot().asCell()) });
        break;
      case 'map': {
        const key = (k) => alignedOfShape(f.type.key, k);
        view[f.name] = {
          member: (k) => slot().asMap().get(key(k)) !== undefined,
          lookup: (k) => {
            const v = slot().asMap().get(key(k));
            if (v === undefined) throw new rt.CompactError(`${f.name}: key not present`);
            return decodeAligned(f.type.value, v.asCell());
          },
          size: () => BigInt(slot().asMap().keys().length),
          isEmpty: () => slot().asMap().keys().length === 0,
          *[Symbol.iterator]() {
            const m = slot().asMap();
            for (const k of m.keys()) yield [decodeAligned(f.type.key, k), decodeAligned(f.type.value, m.get(k).asCell())];
          },
        };
        break;
      }
      case 'set': {
        const key = (k) => alignedOfShape(f.type.elem, k);
        view[f.name] = {
          member: (k) => slot().asMap().get(key(k)) !== undefined,
          size: () => BigInt(slot().asMap().keys().length),
          isEmpty: () => slot().asMap().keys().length === 0,
          *[Symbol.iterator]() {
            for (const k of slot().asMap().keys()) yield decodeAligned(f.type.elem, k);
          },
        };
        break;
      }
      default:
        Object.defineProperty(view, f.name, { enumerable: true, get: slot });
    }
  }
  return view;
}

// ---------------------------------------------------------------- circuits
//
// The trace. `makeContract(spec, witnesses, { trace })` calls `trace(record)`
// once per circuit call (and once for the constructor), when the call has
// completed or failed. Off unless given. A record is
//
//   { circuit,                  the circuit's name ('constructor' for the constructor)
//     inputs,                   the circuit inputs as field elements (bigint[]), or null
//                               when the arguments could not be converted at all
//     steps: [{ index, kind,    each statement, as it starts
//               witness?: { name, args, answer, error? },   a witness asked: its
//                               arguments and its answer (field elements), or
//                               answer null and the error if it refused
//               ledger?:  { request, answer, error? } }],   the ledger asked: the
//                               instructions sent (their public-input encoding,
//                               popeq results blank) and the field elements read
//     groups,                   the public inputs declared, [{ active, vals }]
//     outputs,                  the output field elements, or null
//     failure,                  null, or { at, reason }: `at` is a statement index,
//                               'inputs' or 'outputs' (where the definition fails), or
//                               'arguments' / 'result' (the boundary conversions)
//     proofData }               the proof data recorded (partial if the call failed)

/** A call failed: where, and why. */
const failedAt = (circuit, at, reason) =>
  new rt.CompactError(`${circuit.name}: ${typeof at === 'number' ? `statement ${at} (${circuit.body[at].kind})` : at}: ${reason}`);

function newRecord(name, ppd) {
  return { circuit: name, inputs: null, steps: [], groups: [], outputs: null, failure: null, proofData: ppd };
}

/**
 * `Exec.run`, with the boundary conversions around it: the JS arguments to
 * circuit inputs before, the output field elements to a JS value after.
 * Records into `ppd` and `rec`; returns the result as a JS value.
 */
async function execBody(spec, circuit, witnesses, context, ppd, args, rec) {
  // ---- boundary: arguments to field elements
  if (args.length !== circuit.args.length) {
    rec.failure = { at: 'arguments', reason: `expected ${circuit.args.length} argument(s), received ${args.length}` };
    throw failedAt(circuit, 'arguments', rec.failure.reason);
  }
  const leaves = circuit.args.flatMap((a, k) => flatten(a.shape, args[k]));
  try {
    ppd.input = alignedOfLeaves(leaves);   // the runtime's descriptors check every value against its type
  } catch (e) {
    // Not a value of the argument types: rejected before the circuit runs. The
    // trace still gets the field elements where they can be formed, so that a
    // test can confirm the circuit would reject them too.
    try { rec.inputs = fieldsOfLeaves(leaves).map((x) => (isFieldElement(x) ? x : null)); } catch { /* none */ }
    rec.failure = { at: 'arguments', reason: errorText(e) };
    throw failedAt(circuit, 'arguments', rec.failure.reason);
  }
  const inputs = fieldsOfLeaves(leaves);
  rec.inputs = inputs;

  const io = oracles(spec, witnesses, context, ppd);
  let at = 'inputs';
  let outs;
  try {
    // let env ← bindInputs (fun _ => 0) c.inputs inputs
    const st = { env: bindInputs(circuit.inputs, inputs), priv: [], pub: [], groups: rec.groups };
    // let s ← steps p O c.body.toList { env, private_, ledger }     (Exec.steps: one step per statement, in order)
    for (const [i, s] of circuit.body.entries()) {
      at = i;
      const ev = { index: i, kind: s.kind };
      rec.steps.push(ev);
      await step(io, st, s, ev);
    }
    // let outputs ← Expr.evalList p s.env c.outputs
    at = 'outputs';
    outs = evalList(circuit.outputs, st.env);
    rec.outputs = outs;
  } catch (e) {
    if (!(e instanceof Failure)) throw e;
    rec.failure = { at, reason: e.message };
    throw failedAt(circuit, at, e.message);
  }

  // ---- boundary: output field elements to a JS value. It must convert back to
  // exactly the same field elements, or the proof data would claim other outputs.
  let k = 0;
  let result, back;
  try {
    result = build(circuit.result, (ty) => fromFields(ty, () => outs[k++]));
    back = fieldsOfLeaves(flatten(circuit.result, result));
  } catch { back = null; }
  if (back === null || k !== outs.length || back.length !== outs.length || back.some((x, i) => x !== outs[i])) {
    rec.failure = { at: 'result', reason: `outputs [${outs}] are not a value of the result type` };
    throw failedAt(circuit, 'result', rec.failure.reason);
  }
  return result;
}

const emptyProofData = () => ({ input: { value: [], alignment: [] }, output: undefined, publicTranscript: [], privateTranscriptOutputs: [] });

async function runCircuit(spec, circuit, witnesses, contextIn, args, trace) {
  const context = rt.copyCircuitContext(contextIn);
  const ppd = emptyProofData();
  const rec = newRecord(circuit.name, ppd);
  try {
    const result = await execBody(spec, circuit, witnesses, context, ppd, args, rec);
    try {
      ppd.output = alignedOfShape(circuit.result, result);
    } catch (e) {
      rec.failure = { at: 'result', reason: errorText(e) };
      throw failedAt(circuit, 'result', rec.failure.reason);
    }
    rt.finalizeCallProofData(context, ppd);
    return { result, context, gasCost: context.callContext.currentGasCost, proofData: ppd };
  } catch (e) {
    rec.failure ??= { at: 'runtime', reason: errorText(e) };
    throw e;
  } finally {
    trace?.(rec);
  }
}

// ---------------------------------------------------------------- contract

const U8 = { kind: 'uint', max: '255' };
const U64 = { kind: 'uint', max: ((1n << 64n) - 1n).toString() };

/** The state a ledger field starts in. */
const initialStateValue = (field) => {
  switch (field.type.kind) {
    case 'cell': return rt.StateValue.newCell(alignedOfShape(field.type.shape, build(field.type.shape, zeroLeaf)));
    case 'counter': return rt.StateValue.newCell(alignedOfLeaves([{ ty: U64, val: 0n }]));
    case 'map':
    case 'mapOf':
    case 'set': return rt.StateValue.newMap(new rt.StateMap());
    case 'list':
      return rt.StateValue.newArray().arrayPush(rt.StateValue.newNull()).arrayPush(rt.StateValue.newNull())
        .arrayPush(rt.StateValue.newCell(alignedOfLeaves([{ ty: U64, val: 0n }])));
    case 'merkleTree':
    case 'historicMerkleTree': {
      const arr = rt.StateValue.newArray()
        .arrayPush(rt.StateValue.newBoundedMerkleTree(new rt.StateBoundedMerkleTree(field.type.depth)))
        .arrayPush(rt.StateValue.newCell(alignedOfLeaves([{ ty: U64, val: 0n }])));
      return field.type.kind === 'merkleTree' ? arr : arr.arrayPush(rt.StateValue.newMap(new rt.StateMap()));
    }
    default: throw new Error(`unknown ledger type ${field.type.kind}`);
  }
};

const slotKey = (i) => rt.StateValue.newCell(alignedOfLeaves([{ ty: U8, val: BigInt(i) }])).encode();

/** The instructions that install a field's initial state, as compactc's `initialState` issues them. */
const initialOps = (field) => {
  const key = { push: { storage: false, value: slotKey(field.index) } };
  const value = { push: { storage: true, value: initialStateValue(field).encode() } };
  if (field.type.kind !== 'historicMerkleTree') return [key, value, { ins: { cached: false, n: 1 } }];
  // A historic tree starts with its (empty) root among the past roots.
  return [key, value,
    { idx: { cached: false, pushPath: true, path: [{ tag: 'value', value: alignedOfLeaves([{ ty: U8, val: 2n }]) }] } },
    { dup: { n: 2 } },
    { idx: { cached: false, pushPath: false, path: [{ tag: 'value', value: alignedOfLeaves([{ ty: U8, val: 0n }]) }] } },
    'root',
    { push: { storage: true, value: rt.StateValue.newNull().encode() } },
    { ins: { cached: true, n: 2 } },
    { ins: { cached: false, n: 1 } }];
};

/**
 * Build a contract object from the exported `contract.json` and witness
 * implementations. Witnesses have the Compact shape:
 * `(witnessContext, ...args) => [nextPrivateState, value]`.
 *
 * `options.trace`, if given, is called with a record of every call (see
 * "The trace" above and docs/executor.md). Off by default.
 */
export function makeContract(spec, witnesses = {}, options = {}) {
  if (spec.format !== FORMAT) throw new Error(`unsupported contract format ${spec.format} (this executor reads ${FORMAT})`);
  for (const name of RESERVED_WITNESSES) {
    if (Object.hasOwn(witnesses, name)) throw new Error(`witness ${name} is built in and cannot be supplied`);
  }
  for (const name of Object.keys(witnesses)) {
    if (isCallWitness(name)) throw new Error(`witness ${name}: names starting with "${CALL_PREFIX}" are cross-contract calls`);
  }
  const { trace } = options;
  // `circuits` holds every exported circuit. Only those that touch the ledger
  // are proved; the rest run locally and have no ZKIR or keys.
  const circuits = {};
  const provableCircuits = {};
  for (const c of spec.circuits) {
    circuits[c.name] = async (context, ...args) => runCircuit(spec, c, witnesses, context, args, trace);
    if (c.proof) provableCircuits[c.name] = circuits[c.name];
  }

  /** Initial contract state: every field at its default, then the constructor, given `args`. */
  async function initialState(constructorContext, ...args) {
    const state = new rt.ContractState();
    let slots = rt.StateValue.newArray();
    for (const _ of spec.ledger) slots = slots.arrayPush(rt.StateValue.newNull());
    state.data = new rt.ChargedState(slots);
    for (const c of spec.circuits) if (c.proof) state.setOperation(c.name, new rt.ContractOperation());
    const context = rt.createCircuitContext({
      circuitId: 'constructor',
      contractAddress: rt.dummyContractAddress(),
      coinPublicKeyOrZswapState: constructorContext.initialZswapLocalState.coinPublicKey,
      contractState: state.data,
      privateState: constructorContext.initialPrivateState,
    });
    const defaults = emptyProofData();
    for (const f of spec.ledger) rt.queryLedgerState(context, defaults, initialOps(f));
    if (spec.constructor) {
      // The constructor body is a circuit run like any other, recording its own proof data.
      const ppd = emptyProofData();
      const rec = newRecord('constructor', ppd);
      try {
        const result = await execBody(spec, spec.constructor, witnesses, context, ppd, args, rec);
        try {
          ppd.output = alignedOfShape(spec.constructor.result, result);
        } catch (e) {
          rec.failure = { at: 'result', reason: errorText(e) };
          throw failedAt(spec.constructor, 'result', rec.failure.reason);
        }
      } catch (e) {
        rec.failure ??= { at: 'runtime', reason: errorText(e) };
        throw e;
      } finally {
        trace?.(rec);
      }
    } else if (args.length !== 0) throw new rt.CompactError('this contract has no constructor arguments');
    state.data = new rt.ChargedState(context.callContext.currentQueryContext.state.state);
    return {
      currentContractState: state,
      currentPrivateState: context.callContext.currentPrivateState,
      currentZswapLocalState: context.callContext.currentZswapLocalState,
    };
  }

  return {
    spec, witnesses, circuits, impureCircuits: provableCircuits, provableCircuits, initialState,
    /** The public state as JS values. */
    ledger: (state) => ledgerView(spec, state),
  };
}

/**
 * The module a caller's runtime loads for a Damp contract deployed at some
 * address: what `crossContractCall` reads off compactc's generated
 * `contract/index.js` (`Contract`, `circuitSignatures`, `expectedVk`), plus
 * `ledger` and `declaredInterfaces`. `expectedVk` maps each provable circuit
 * to the SHA-256 (lowercase hex) of its verifier key, as compactc records it;
 * the runtime refuses the call unless it equals the fingerprint of the key
 * deployed on chain. `options.trace` is passed to `makeContract`.
 */
export function contractModule(spec, expectedVk = {}, options = {}) {
  class Contract {
    constructor(witnesses = {}) {
      return makeContract(spec, witnesses, options);
    }
  }
  return {
    Contract,
    circuitSignatures: circuitSignatures(spec),
    expectedVk,
    declaredInterfaces: declaredInterfaces(spec),
    ledger: (state) => ledgerView(spec, state),
  };
}
