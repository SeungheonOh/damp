# How compactc 0.36.1 lowers `Bytes<n>` and `persistentHash`

Everything below was **observed** by compiling small contracts with compactc 0.36.1 (`--skip-zk`) and reading the emitted `zkir/*.zkir`, or by running the JS runtime (compact-runtime 0.21.0, onchain-runtime-v4 4.0.2) and the real ZKIR 3.2.1 `check` through `executor/harness/check.mjs`. Statements marked *(inferred)* were not observed directly.

The test contracts, their compiled output and the JS scripts are in
a scratch directory that is not kept:

| contract | what it covers |
|---|---|
| `rep.compact` | inputs, witnesses, ledger write and read for n = 1, 8, 31, 32, 33, 62, 63, 64 |
| `eq.compact` | `==` and `!=` for n = 8, 32, 64, 93, plus equality against a ledger read |
| `lit.compact` | `pad`, string literals, `default<Bytes<n>>` |
| `ph.compact` | `persistentHash`, `persistentCommit`, `transientHash`, `transientCommit`, `degradeToTransient`, `upgradeFromTransient` |
| `conv.compact` | `as Field` / `as Bytes<n>`, `?:` on Bytes, and `Map<Bytes<32>,_>` keys |
| `misc.compact` | structs, `Maybe` and `Vector` holding Bytes, and a guarded read |

- To compile one: `./c.sh <name>`. The output goes to `out/<name>/`.
- To print a circuit's ZKIR one instruction per line: `./show.sh out/<name>/zkir/<c>.zkir`.
- `node repr.mjs` checks the limb formula against the runtime's `transientHash`.
- `node roundtrip.mjs` runs the compactc modules and checks their proof data with `checkProofData`. Its output is saved in `roundtrip.out`, and every case in it passes.

ZKIR immediates are **little-endian** hex (spec §3.4/§587). That matches Damp's `leHex`. So `"0x616263"` is the field element `0x63_62_61`: its in-memory byte order is the string "abc".

---

## R1. Limb layout

A `Bytes<n>` value is `L = ceil(n/31)` field elements, called limbs.

- Read the n bytes `b[0..n)` as one **little-endian** integer `X = Σ b[i]·256^i`.
- Cut `X` into 248-bit chunks and list them **most significant first**: `limb[j] = (X >> 248·(L−1−j)) mod 2^248` for `j = 0..L−1`.

In bytes:

- **The last limb** holds `b[0..31)`.
- **The limb before it** holds `b[31..62)`.
- **`limb[0]`** holds the top `r = n − 31·(L−1)` bytes, `b[31(L−1)..n)`. Here `r = n mod 31`, or 31 when 31 divides n.
- **Within a limb** the bytes are little-endian: the byte with the lowest index is the least significant.

| n | L | limb 0 | limb 1 | limb 2 |
|---|---|---|---|---|
| 1, 8, 31 | 1 | b[0..n) | | |
| 32 | 2 | b[31] | b[0..31) | |
| 33 | 2 | b[31..33) | b[0..31) | |
| 62 | 2 | b[31..62) | b[0..31) | |
| 63 | 3 | b[62] | b[31..62) | b[0..31) |
| 64 | 3 | b[62..64) | b[31..62) | b[0..31) |
| 93 | 3 | b[62..93) | b[31..62) | b[0..31) |

This order is the same everywhere the value appears:

- circuit inputs;
- `private_input` sequences (witness results);
- `public_input` sequences (ledger reads);
- `output`;
- `impact` push/popeq value lists;
- `persistent_hash` inputs;
- `transient_hash` inputs;
- `cond_select` and `test_eq`.

Evidence. The constants pin down the layout, because the IR compares an input against known bytes (`lit.compact`):

```compact
export circuit pad32(a: Bytes<32>): [] { assert(disclose(a) == pad(32, "abcdefghijklmnopqrstuvwxyz012345"), "x"); cnt.increment(1); }
export circuit pad64(a: Bytes<64>): [] { assert(disclose(a) == pad(64, "abcdefghijklmnopqrstuvwxyz0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ!@"), "x"); cnt.increment(1); }
```
```
pad32: {"op":"test_eq","output":"%t.2","a":"%a.0","b":"0x35"}                       <- "5" = b[31]
       {"op":"test_eq","output":"%t.3","a":"%a.1","b":"0x6162636465666768696a6b6c6d6e6f707172737475767778797a3031323334"}  <- b[0..31) "abc…01234"
pad64: {"op":"test_eq","output":"%t.3","a":"%a.0","b":"0x2140"}                     <- "!@" = b[62..64)
       {"op":"test_eq","output":"%t.4","a":"%a.1","b":"0x35363738394142434445464748494a4b4c4d4e4f505152535455565758595a"}  <- b[31..62) "56789A…Z"
       {"op":"test_eq","output":"%t.6","a":"%a.2","b":"0x6162636465666768696a6b6c6d6e6f707172737475767778797a3031323334"}  <- b[0..31)
```
`lit3` (`Bytes<3>` compared with `"abc"`) gives `test_eq a.0 0x616263`.

The ZKIR VM's own in-circuit decoder (`fab_decode_to_bytes_atom` in `ir_vm.rs`) uses the same layout. It reads the stray limb first and puts its bytes at the end. It then reads the full limbs from last to first, filling the bytes from the front.

## R2. Range constraints

Each limb gets a `constrain_bits`:

- `limb[0]` gets `8·r` bits, where r is the byte count of limb 0 from R1.
- Every other limb gets 248 bits.

The constraints are emitted **in limb order**:

- **Circuit inputs:** for all inputs, in order, right after the input declarations, before any other instruction. They sit in the same place as the existing Uint/Boolean checks, and the inputs interleave with them (see `hq` in R6).
- **Witness results:** each `private_input` is followed immediately by its own `constrain_bits`.

`Bytes<32>` and `Bytes<64>` as inputs (`rep.compact`, `export circuit in32(x: Bytes<32>): [] { cnt.increment(1); }`):
```
in32 inputs [%x.0, %x.1]   (both "Scalar<BLS12-381>")
  {"op":"constrain_bits","val":"%x.0","bits":8}
  {"op":"constrain_bits","val":"%x.1","bits":248}
in64 inputs [%x.0,%x.1,%x.2]: bits 16, 248, 248
```

Observed widths for each n:

| n | widths |
|---|---|
| 1 | 8 |
| 8 | 64 |
| 31 | 248 |
| 32 | 8, 248 |
| 33 | 16, 248 |
| 62 | 248, 248 |
| 63 | 8, 248, 248 |
| 64 | 16, 248, 248 |
| 93 | 248 ×3 |
| 5 | 40 |

A witness `Bytes<32>` result (`witness wit32(): Bytes<32>; export circuit w32(): [] { b32 = disclose(wit32()); }`):
```
{"op":"private_input","type":"Scalar<BLS12-381>","output":"%tmp.0","guard":null}
{"op":"constrain_bits","val":"%tmp.0","bits":8}
{"op":"private_input","type":"Scalar<BLS12-381>","output":"%tmp.1","guard":null}
{"op":"constrain_bits","val":"%tmp.1","bits":248}
```
Ledger reads (`public_input`) and circuit outputs get **no** range constraint (see R5).

## R3. ZKIR types

- **No ZKIR byte types at the interface.** Every circuit `input`, every `private_input` and `public_input`, and every entry in `outputs` is `Scalar<BLS12-381>`, one per limb. A tally over all 100+ compiled circuits found 158 `"type"` fields, all `Scalar<BLS12-381>`.
- **Only two places hold a bytes value.** A bytes-typed register (`Bytes32`) exists only as the output of `persistent_hash`, and it is consumed at once by `bytes_into_natives`.
- **Ops that never appear:** `bytes_from_natives`, `bytes32_into_low_high`, `bytes32_from_low_high`, `into_bytes32`, `from_bytes32` and `encode`. Ops that did appear: `assert`, `bytes_into_natives`, `cond_select`, `constrain_bits`, `constrain_to_boolean`, `copy`, `div_mod_power_of_two`, `impact`, `output`, `persistent_hash`, `private_input`, `public_input`, `reconstitute_field`, `test_eq` and `transient_hash`.
- **`persistent_hash` takes limbs.** Its inputs are native limbs in the R1 order. A Bytes value goes in as its limbs; nothing is converted to a ZKIR Bytes value first (see R6).

## R4. Equality

The comparison is a left fold over limbs, starting at limb 0. Each step does `test_eq` on limb i, then `cond_select(bit = acc, a = eq_i, b = 0x00)`. The `test_eq` for limb i+1 is emitted just before the `cond_select` that uses it.

The operands of `test_eq` keep the source order: `a == b` gives `a: a_i, b: b_i`, and `ledger == arg` gives `a: ledger limb`.

When L = 1 there is only a `test_eq`. `!=` adds `cond_select(bit = eq, a = 0x00, b = 0x01)`.

```compact
export circuit eq32(a: Bytes<32>, b: Bytes<32>): [] { assert(disclose(a == b), "x"); cnt.increment(1); }
```
```
eq8 : {"op":"test_eq","output":"%t.2","a":"%a.0","b":"%b.1"}  {"op":"assert","cond":"%t.2"}
eq32: {"op":"test_eq","output":"%t.4","a":"%a.0","b":"%b.2"}
      {"op":"test_eq","output":"%t.5","a":"%a.1","b":"%b.3"}
      {"op":"cond_select","output":"%t.6","bit":"%t.4","a":"%t.5","b":"0x00"}
      {"op":"assert","cond":"%t.6"}
ne32: … same … then {"op":"cond_select","output":"%t.7","bit":"%t.6","a":"0x00","b":"0x01"}
eq64 (and eq93, same shape):
      test_eq t.6 = a.0 b.3 ; test_eq t.7 = a.1 b.4 ; cond_select t.8 = t.6 ? t.7 : 0
      test_eq t.9 = a.2 b.5 ; cond_select t.10 = t.8 ? t.9 : 0 ; assert t.10
eql  (assert(disclose(a) == b32)): test_eq a=%a.0 b=%t.2 ; test_eq a=%a.1 b=%t.3 ; cond_select …
eql2 (assert(b32 == disclose(a))): test_eq a=%t.2 b=%a.0 ; test_eq a=%t.3 b=%a.1 ; cond_select …
```

When a comparison sits in a guarded branch (`if (c) assert(h == x)`), the fold result r is wrapped as `cond_select(bit = c, a = r, b = 0x01)` before the `assert` (`misc.guarded`).

The ternary `c ? x : y` is one `cond_select(bit = c, a = x_i, b = y_i)` per limb, in limb order (`conv.sel`).

`eqb` returns `a == b` after a ledger op. There the `test_eq`/`cond_select` instructions are emitted **after** the impacts, at the point of use. This is compactc's usual lazy placement, not something specific to Bytes.

## R5. Ledger Cell of `Bytes<n>`

In the Impact encoding, an AlignedValue is written as `[#atoms, atom codes…, values…]`. A bytes atom has code `n`; field is `-2` and compress is `-1`, as `Damp.Impact.atomCode` already has it. A Bytes<n> value is a **single** atom `bytes n` followed by its L limbs in R1 order.

This applies to:

- `push` (storage=true) for writes;
- `popeq` for reads;
- `push` (storage=false) when Bytes is a Map key;
- `idx` path entries when Bytes is a Map key.

Write (`b32` is ledger field 4 in `rep.compact`):
```
set32 : {"op":"impact","guard":"0x01","inputs":["0x10","0x01","0x01","0x01","0x04"]}
        {"op":"impact","guard":"0x01","inputs":["0x11","0x01","0x01","0x20","%x.0","%x.1"]}
        {"op":"impact","guard":"0x01","inputs":["0x91"]}
set64 : … ["0x11","0x01","0x01","0x40","%x.0","%x.1","%x.2"] …
set31 : … ["0x11","0x01","0x01","0x1f","%x.0"] …
```
Read: L `public_input`s in limb order, unguarded or with the branch guard, all emitted **before** the `dup`. The `popeq` lists them in the same order. The circuit output is the same limbs.
```
get32 : {"op":"public_input","type":"Scalar<BLS12-381>","output":"%t.0","guard":null}
        {"op":"public_input","type":"Scalar<BLS12-381>","output":"%t.1","guard":null}
        {"op":"impact","guard":"0x01","inputs":["0x30"]}
        {"op":"impact","guard":"0x01","inputs":["0x50","0x01","0x01","0x04"]}
        {"op":"impact","guard":"0x01","inputs":["0x0c","0x01","0x20","%t.0","%t.1"]}
        {"op":"output","vals":["%t.0","%t.1"]}
get64 : 3 public_inputs t.0..t.2; popeq ["0x0c","0x01","0x40","%t.0","%t.1","%t.2"]; output [t.0,t.1,t.2]
guarded read (misc.guarded): public_input … "guard":"%c.0" (×2), impacts with guard %c.0
```
Constants are written as their limb immediates (`lit.compact`):
```
setlit  (b32 = pad(32,"abc"))        : ["0x11","0x01","0x01","0x20","0x00","0x616263"]
setdef  (b32 = default<Bytes<32>>)   : ["0x11","0x01","0x01","0x20","0x00","0x00"]
setdef3 (b3 = default<Bytes<3>>)     : ["0x11","0x01","0x01","0x03","0x00"]
setlit64                             : ["0x11","0x01","0x01","0x40","0x2140","0x3536…5a","0x6162…34"]
```

A composite value lists its atoms in order: `struct S { a: Uint<16>, b: Bytes<32> }` gives `["0x11","0x01","0x02","0x02","0x20","%x.0","%x.1","%x.2"]`. Here `x.0` is a, and `x.1, x.2` are b's limbs.

`Map<Bytes<32>, Field>`:

- insert key: `["0x10","0x01","0x01","0x20","%k.0","%k.1"]`;
- lookup path: `["0x50","0x01","0x20","%k.0","%k.1"]`;
- member: push key then `0x18`.

The `transientHash` of a Bytes<n> is `transient_hash` over its limbs in R1 order: `th` gives `transient_hash inputs [%x.0, %x.1]`.

## R6. `persistentHash` and `bytes_into_natives`

`persistentHash<T>(v)` becomes one `persistent_hash` instruction:

- **`alignment`:** `T`'s alignment as JSON atoms.
- **`inputs`:** `v`'s limbs, flattened in field order, with each Bytes in R1 order.
- **Output:** a single `Bytes32` register, named `%bytes.N`, which is **immediately** followed by `bytes_into_natives` with 2 outputs.

The type-to-alignment mapping:

| T | alignment |
|---|---|
| Field | `{field}` |
| Bytes<n> | `{bytes, length n}` |
| Uint<64> | `{bytes, length 8}` |
| Boolean | `{bytes, length 1}` |
| struct, tuple or Vector | the concatenation of its members |

In the alignment JSON, a bytes atom is written `{"length": n, "tag": "bytes"}`. The ZKIR file serializes keys in that order; JSON key order should not matter to `jsonIrToBinary`, but the VK test cares only about the binary.

**The order swap.** `bytes_into_natives` returns its limbs in the *opposite* order to R1. Its `outputs[0]` is `b[0..31)` and `outputs[1]` is `b[31]`, which is the ZKIR VM's `encode_offcircuit`: 31-byte chunks from the front, each little-endian. compactc therefore uses the outputs **reversed** as the Compact `Bytes<32>` value: `[outputs[1], outputs[0]]`.

```
hf  (h = persistentHash<Field>(x)):
  {"op":"persistent_hash","output":"%bytes.1","alignment":[{"tag":"atom","value":{"tag":"field"}}],"inputs":["%x.0"]}
  {"op":"bytes_into_natives","outputs":["%tmp.2","%tmp.3"],"bytes":"%bytes.1"}
  {"op":"impact","guard":"0x01","inputs":["0x11","0x01","0x01","0x20","%tmp.3","%tmp.2"]}     <- swapped
hb  (Bytes<32>): alignment [{bytes 32}], inputs ["%x.0","%x.1"] (R1 order, high byte first)
hb64 (Bytes<64>): alignment [{bytes 64}], inputs ["%x.0","%x.1","%x.2"]
hb5 (Bytes<5>): [{bytes 5}], ["%x.0"];   hu (Uint<64>): [{bytes 8}], ["%x.0"];   hbool: [{bytes 1}], ["%x.0"]
hs  (struct P {a: Field, b: Field}) and hv (Vector<2, Field>): [{field},{field}], ["%x.0","%x.1"]
ht  ([Field, Bytes<32>] tuple): [{field},{bytes 32}], ["%x.0","%y.1","%y.2"]
hq  (struct {a: Uint<64>, b: Bytes<32>, c: Boolean}): [{bytes 8},{bytes 32},{bytes 1}], ["%x.0","%x.1","%x.2","%x.3"]
hvec (Vector<2, Bytes<32>>): [{bytes 32},{bytes 32}], ["%x.0","%x.1","%x.2","%x.3"]
hcmp (assert(persistentHash<Field>(x) == y), y: Bytes<32>):
  {"op":"bytes_into_natives","outputs":["%t.4","%t.5"],"bytes":"%bytes.3"}
  {"op":"test_eq","output":"%t.6","a":"%t.5","b":"%y.1"}      <- out[1] vs limb 0 (b[31])
  {"op":"test_eq","output":"%t.7","a":"%t.4","b":"%y.2"}      <- out[0] vs limb 1 (b[0..31))
hh  (persistentHash<Bytes<32>>(persistentHash<Field>(x))):
  bytes_into_natives outputs [%t.2,%t.3]; next persistent_hash inputs ["%t.3","%t.2"]
```
`checkProofData` accepts `hcmp` called with `y = rt.persistentHash(CompactTypeField, x)` (`roundtrip.out`). The JS hash bytes therefore line up with the swapped limbs.

Rule: for a hash result, Compact limbs = `[bin[1], bin[0]]`. In general, Compact limbs = `reverse(bytes_into_natives outputs)`. The general form is *(inferred)*: compactc only ever applies `bytes_into_natives` to the 32-byte hash output.

Each `bytes_into_natives` output gets **no** `constrain_bits`.

**Register names.** The output register is named `%bytes.N`. The `bytes_into_natives` outputs are named `%tmp.N` when the value is used directly as a result, and `%t.N` when it feeds a comparison or a second hash. These are only names, and they should not affect the verifier key *(inferred)*.

The commitments and conversions (`ph.compact`):
```
pc  persistentCommit<Field>(x, r: Bytes<32>):
    persistent_hash alignment [{bytes 32},{field}], inputs ["%r.1","%r.2","%x.0"]   <- opening first, then value
    bytes_into_natives [%tmp.4,%tmp.5]; result limbs [%tmp.5,%tmp.4]
tc  transientCommit<Field>(x, r: Field): {"op":"transient_hash","inputs":["%r.1","%x.0"]}   <- opening first
dt  degradeToTransient(x: Bytes<32>): {"op":"copy","output":"%tmp.2","val":"%x.1"}   <- the low limb b[0..31); b[31] dropped
ut  upgradeFromTransient(x: Field):
    {"op":"copy","output":"%tmp.1","val":"0x00"}
    {"op":"div_mod_power_of_two","outputs":["%tmp.2","%tmp.3"],"val":"%x.0","bits":248}
    result limbs [%tmp.1, %tmp.3] = [0, x mod 2^248]     <- the quotient %tmp.2 is unused
```
The JS runtime agrees on `ut`:

- `upgradeFromTransient(maxField)` gives 31 bytes, with the top byte 0x73 dropped. So the result is x mod 2^248, padded with zeros to 32.
- `degradeToTransient(b)` equals limb 1.

`roundtrip.mjs` checks both.

## R7. Conversions (`conv.compact`)

```
b8f   Bytes<8>  as Field : no instruction; the limb is the field value
b31f  Bytes<31> as Field : no instruction
b32f  Bytes<32> as Field : {"op":"reconstitute_field","output":"%tmp.2","divisor":"%x.0","modulus":"%x.1","bits":248}
                            (= x.0·2^248 + x.1, asserting no overflow past |Fr|)
fb8   Field as Bytes<8>  : {"op":"copy","output":"%tmp.1","val":"%x.0"} ; {"op":"constrain_bits","val":"%tmp.1","bits":64}
fb31  Field as Bytes<31> : copy ; constrain_bits 248
fb32  Field as Bytes<32> : {"op":"div_mod_power_of_two","outputs":["%tmp.1","%tmp.2"],"val":"%x.0","bits":248}
                            limbs = [%tmp.1 (quotient), %tmp.2 (remainder)]   (no extra constrain_bits)
```
`Field as Bytes<n>` for n < 32 uses a `copy` and then a `constrain_bits` of `8n` bits on the copy. Damp would need a `copy` instruction to reproduce this byte for byte; `Damp.Zkir.Instr.copy` exists.

`Maybe<Bytes<32>>` is flattened to `[is_some, limb0, limb1]`. Each part gets its own range check (`constrain_to_boolean`, then 8 bits, then 248 bits). `m.is_some ? m.value : default` becomes two `cond_select`s with `b: 0x00` (`misc.wmc`).

## R8. JS side: AlignedValue and the limbs ↔ Uint8Array formula

- **`CompactTypeBytes(n)`.** It has `alignment() = [{tag:'atom', value:{tag:'bytes', length:n}}]`. `toValue(u8)` is **one** atom: the n bytes in their natural order, with **trailing zero bytes stripped**. All zeros gives `Uint8Array(0)`, and `pad(32,"abc")` gives `616263`.
  - Circuit arguments, witness results (`privateTranscriptOutputs`), pushed cells and `popeq` results all use this same form. For example, the `set32` cell is `{value:[<32-byte hex>], alignment:[bytes 32]}`, and the `setlit` cell is `value ['616263'], alignment [bytes 32]`.
- **The prover's field representation of a `bytes n` atom is exactly R1.** Pad the atom back to n bytes, then apply the formula. Two independent observations show this:
  1. `onchain-runtime.transientHash([bytes n], [atom])` equals `transientHash([field]*L, limbs)` with the limbs from R1. This held for n = 1, 8, 31, 32, 33, 62, 63, 64, 93 and 100, and the reversed limb order fails for every n ≥ 32 (`repr.mjs`).
  2. `checkProofData` accepts proof data whose input atom is rebuilt **from the IR's constant limbs** with `limbsToBytes`, for `lit.pad32` and `lit.pad64`. It rejects the byte-reversed input. Tampering `set32` with the reversed bytes gives `Public transcript input mismatch for input 9; expected: Some(0c), computed: Some(07)`. Input 9 is the first limb after `0x11,0x01,0x01,0x20`, and 0x0c is the original b[31]: the first limb really is the last byte.
- **The formula for a generic executor.** It is used by `roundtrip.mjs`, and every `rep`, `lit` and `ph` circuit passes `check` with it:

```js
// bytes (length n) -> limbs (length L = ceil(n/31)), limb 0 = most significant 248-bit chunk
const bytesToLimbs = (b) => {
  const n = b.length, L = Math.ceil(n / 31); let X = 0n;
  for (let i = n - 1; i >= 0; i--) X = (X << 8n) | BigInt(b[i]);          // X = Σ b[i]·256^i
  return Array.from({ length: L }, (_, j) => (X >> BigInt(248 * (L - 1 - j))) & ((1n << 248n) - 1n));
};
const limbsToBytes = (limbs, n) => {
  const L = limbs.length; let X = 0n;
  for (let j = 0; j < L; j++) X |= limbs[j] << BigInt(248 * (L - 1 - j));
  const b = new Uint8Array(n); for (let i = 0; i < n; i++) { b[i] = Number(X & 255n); X >>= 8n; }
  return b;
};
// AlignedValue for the transcript: new CompactTypeBytes(n).toValue(limbsToBytes(limbs, n)), alignment [bytes n]
```

`rt.persistentHash(desc, v)` returns the 32 digest bytes `d`. These map to Compact limbs `[d[31], LE(d[0..31))]`, and that equals `bytesToLimbs(d)`.

## Could not determine / not tested

- **`bytes_into_natives` on anything other than the 32-byte hash.** compactc never emits it any other way, so the general rule "reverse its outputs" for other lengths is *(inferred)*. Neither `bytes_from_natives` nor the `bytes32_*` ops ever appeared.
- **`Bytes<n> as Field` for n > 32, and `Field as Bytes<n>` for n > 32.** Not tried; they are probably type errors. `Bytes<0>` was not tried either.
- **Keccak, `ecMul` and similar.** Byte-producing builtins other than `persistentHash`/`persistentCommit` were not explored.
- **`upgradeFromTransient` dropping the quotient.** It ignores the `div_mod_power_of_two` quotient (the result's high byte is always 0). That was observed, and the JS runtime agrees. Whether this is intended was not investigated.
- **The `"length"`-before-`"tag"` key order in the `persistent_hash` alignment JSON.** This is just how compactc prints it. That it does not affect the binary IR or the VK is *(inferred)*: no VK comparison was run (`--skip-zk`).
- **Generated register names (`%tmp` vs `%t` vs `%bytes`).** Assumed irrelevant to the VK *(inferred)*.
