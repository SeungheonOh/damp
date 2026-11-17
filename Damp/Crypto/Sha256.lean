/-
SHA-256 (FIPS 180-4), on a list of bytes.

The round constants and initial hash value are not typed in: they are computed
from their definition in FIPS 180-4 §4.2.2 and §5.3.3 (the first 32 bits of the
fractional parts of the cube roots of the first 64 primes, and of the square
roots of the first 8 primes). `test/semantics.sh` checks the result against
Node's SHA-256 and against Midnight's `persistentHash`.

Core Lean only; every function is total and executable.
-/
namespace Damp.Crypto.Sha256

/-! ## Constants, from their definition -/

/-- Largest `r < 2^bits` with `r^k ≤ n`, found one bit at a time from the top. -/
def iroot (k n : Nat) : (bits : Nat) → Nat → Nat
  | 0, r => r
  | b + 1, r =>
      let r' := r + 2 ^ b
      iroot k n b (if r' ^ k ≤ n then r' else r)

def isPrime (n : Nat) : Bool :=
  2 ≤ n && (List.range n).all fun d => d < 2 || d * d > n || n % d != 0

/-- The first 64 primes (all below 312). -/
def primes : List Nat := ((List.range 312).filter isPrime).take 64

/-- First 32 bits of the fractional part of `p^(1/k)`: `⌊(p·2^(32k))^(1/k)⌋ mod 2^32`. -/
def fracBits (k p : Nat) : UInt32 :=
  UInt32.ofNat (iroot k (p * 2 ^ (32 * k)) (32 + 9) 0 % 2 ^ 32)

/-- `K`: cube roots of the first 64 primes (§4.2.2). -/
def K : Array UInt32 := (primes.map (fracBits 3)).toArray

/-- `H(0)`: square roots of the first 8 primes (§5.3.3). -/
def H0 : List UInt32 := (primes.take 8).map (fracBits 2)

/-! ## The compression function (§6.2.2) -/

def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

def bsig0 (x : UInt32) : UInt32 := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22
def bsig1 (x : UInt32) : UInt32 := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25
def ssig0 (x : UInt32) : UInt32 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
def ssig1 (x : UInt32) : UInt32 := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)
def ch (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (~~~x &&& z)
def maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- Big-endian word from four bytes. -/
def word (a b c d : UInt8) : UInt32 :=
  (a.toUInt32 <<< 24) ||| (b.toUInt32 <<< 16) ||| (c.toUInt32 <<< 8) ||| d.toUInt32

/-- The message schedule of the block starting at byte `off`. -/
def schedule (msg : Array UInt8) (off : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := #[]
  for t in [0:16] do
    let i := off + 4 * t
    w := w.push (word msg[i]! msg[i+1]! msg[i+2]! msg[i+3]!)
  for t in [16:64] do
    w := w.push (ssig1 w[t-2]! + w[t-7]! + ssig0 w[t-15]! + w[t-16]!)
  return w

/-- Process one 64-byte block. -/
def compress (h : Array UInt32) (msg : Array UInt8) (off : Nat) : Array UInt32 := Id.run do
  let w := schedule msg off
  let mut a := h[0]!; let mut b := h[1]!; let mut c := h[2]!; let mut d := h[3]!
  let mut e := h[4]!; let mut f := h[5]!; let mut g := h[6]!; let mut hh := h[7]!
  for t in [0:64] do
    let t1 := hh + bsig1 e + ch e f g + K[t]! + w[t]!
    let t2 := bsig0 a + maj a b c
    hh := g; g := f; f := e; e := d + t1
    d := c; c := b; b := a; a := t1 + t2
  return #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d, h[4]! + e, h[5]! + f, h[6]! + g, h[7]! + hh]

/-- Padding (§5.1.1): `0x80`, zeros, and the length in bits as a 64-bit big-endian integer. -/
def pad (msg : List UInt8) : List UInt8 :=
  let len := msg.length
  let zeros := (64 + 56 - (len + 1) % 64) % 64
  let bits := 8 * len
  msg ++ [0x80] ++ List.replicate zeros 0 ++
    (List.range 8).reverse.map fun i => UInt8.ofNat (bits / 2 ^ (8 * i) % 256)

/-- SHA-256 of a byte string: 32 bytes. -/
def hash (msg : List UInt8) : List UInt8 :=
  let m := (pad msg).toArray
  let h := (List.range (m.size / 64)).foldl (fun h i => compress h m (64 * i)) H0.toArray
  h.toList.flatMap fun (x : UInt32) => [(x >>> 24).toUInt8, (x >>> 16).toUInt8, (x >>> 8).toUInt8, x.toUInt8]

/-- SHA-256 on bytes given as naturals (each taken mod 256). -/
def hashNat (msg : List Nat) : List Nat :=
  (hash (msg.map UInt8.ofNat)).map (·.toNat)

end Damp.Crypto.Sha256
