/-
`Bytes n` beyond limb equality.

A `Bytes n` value is `L = byteLimbs n` limbs, most significant first, each a
248-bit chunk of the little-endian number `X = Σ b[i]·256^i` of its bytes
(docs/bytes-lowering.md, R1). `Bytes.toNat` reassembles `X` from the limbs and
`Bytes.bytesOf n` reads its `n` bytes back, first byte first.

* Given the limb range checks every `Bytes n` input and witness result carries
  (R2: the first limb `8·(n − 31·(L−1))` bits, the others 248), `==.` on
  `Bytes n` is byte-wise equality (`Bytes.eq_bytes`).
* `Bytes.ofBytes n bs` (and so `Bytes.pad`) means the bytes `bs`, cut or padded
  with zeros to `n` (`Bytes.ofBytes_bytes`).
-/
import Damp.Proofs.Interface.Values

namespace Damp
open IR

/-! ## Numbers in base `2 ^ 248`, most significant digit first -/

/-- The limb base. -/
abbrev limbBase : Nat := 2 ^ 248

/-- The number a list of limbs spells, most significant first. -/
def Bytes.toNat (xs : List Fr) : Nat := xs.foldl (fun acc x => acc * limbBase + x.val) 0

/-- The `n` bytes of the number the limbs spell, first (least significant) byte first. -/
def Bytes.bytesOf (n : Nat) (xs : List Fr) : List Nat := (List.range n).map fun i => Bytes.toNat xs / 256 ^ i % 256

theorem foldl_digits_acc (B : Nat) : ∀ (ds : List Nat) (a : Nat),
    ds.foldl (fun acc d => acc * B + d) a = a * B ^ ds.length + ds.foldl (fun acc d => acc * B + d) 0
  | [], a => by simp
  | d :: ds, a => by
    simp only [List.foldl_cons, List.length_cons]
    rw [foldl_digits_acc B ds (a * B + d), foldl_digits_acc B ds (0 * B + d)]
    simp only [Nat.zero_mul, Nat.zero_add, Nat.pow_succ, Nat.add_mul, Nat.add_assoc]
    rw [Nat.mul_assoc, Nat.mul_comm B]

theorem toNat_eq_digits (xs : List Fr) :
    Bytes.toNat xs = (xs.map Fr.val).foldl (fun acc d => acc * limbBase + d) 0 := by
  unfold Bytes.toNat; rw [List.foldl_map]

/-- The number spelled by digits below the base is below the base to the number of digits. -/
theorem foldl_digits_lt (B : Nat) : ∀ (ds : List Nat), (∀ d ∈ ds, d < B) →
    ds.foldl (fun acc d => acc * B + d) 0 < B ^ ds.length
  | [], _ => by simp
  | d :: ds, h => by
    rw [List.foldl_cons, foldl_digits_acc, List.length_cons]
    have ih := foldl_digits_lt B ds fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hd := h d (List.mem_cons_self ..)
    simp only [Nat.zero_mul, Nat.zero_add]
    rw [Nat.pow_succ, Nat.mul_comm (B ^ ds.length) B]
    have : d * B ^ ds.length + B ^ ds.length ≤ B * B ^ ds.length := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hd
    omega

/-- Digits below the base are determined by the number they spell (for a fixed number of digits). -/
theorem foldl_digits_inj (B : Nat) : ∀ (ds es : List Nat), ds.length = es.length →
    (∀ d ∈ ds, d < B) → (∀ e ∈ es, e < B) →
    ds.foldl (fun acc d => acc * B + d) 0 = es.foldl (fun acc d => acc * B + d) 0 → ds = es
  | [], [], _, _, _, _ => rfl
  | d :: ds, e :: es, hl, hd, he, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    rw [List.foldl_cons, List.foldl_cons, foldl_digits_acc, foldl_digits_acc (a := 0 * B + e)] at h
    simp only [Nat.zero_mul, Nat.zero_add] at h
    have r1 := foldl_digits_lt B ds fun x hx => hd x (List.mem_cons_of_mem _ hx)
    have r2 := foldl_digits_lt B es fun x hx => he x (List.mem_cons_of_mem _ hx)
    rw [hl] at r1 h
    have hpos : 0 < B ^ es.length := Nat.lt_of_le_of_lt (Nat.zero_le _) r2
    -- divide and take the remainder by `B ^ length`
    have hq := congrArg (· / B ^ es.length) h
    have hr := congrArg (· % B ^ es.length) h
    rw [Nat.mul_comm d, Nat.mul_comm e, Nat.mul_add_div hpos, Nat.mul_add_div hpos,
      Nat.div_eq_of_lt r1, Nat.div_eq_of_lt r2] at hq
    rw [Nat.mul_comm d, Nat.mul_comm e, Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt r1,
      Nat.mod_eq_of_lt r2] at hr
    simp only [Nat.add_zero] at hq
    rw [hq, foldl_digits_inj B ds es hl (fun x hx => hd x (List.mem_cons_of_mem _ hx))
      (fun x hx => he x (List.mem_cons_of_mem _ hx)) hr]
  | [], _ :: _, hl, _, _, _ => by simp at hl
  | _ :: _, [], hl, _, _, _ => by simp at hl

/-- Limbs below `2 ^ 248` are determined by the number they spell. -/
theorem Bytes.toNat_inj {xs ys : List Fr} (hl : xs.length = ys.length)
    (hx : ∀ x ∈ xs, x.val < limbBase) (hy : ∀ y ∈ ys, y.val < limbBase)
    (h : Bytes.toNat xs = Bytes.toNat ys) : xs = ys := by
  rw [toNat_eq_digits, toNat_eq_digits] at h
  have := foldl_digits_inj limbBase _ _ (by simp [hl]) (by simpa using hx) (by simpa using hy) h
  clear h hl hx hy
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at this
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at this
      rw [Fr.ext this.1, ih this.2]

/-! ## Bytes of a number -/

/-- The first `c` base-256 digits of a number. -/
theorem bytes_succ (x c : Nat) :
    (List.range (c + 1)).map (fun i => x / 256 ^ i % 256) =
      x % 256 :: (List.range c).map (fun i => x / 256 / 256 ^ i % 256) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Nat.pow_zero, Nat.div_one, List.cons.injEq, true_and]
  apply List.map_congr_left; intro i _
  simp only [Function.comp, Nat.pow_succ, Nat.div_div_eq_div_mul]
  rw [Nat.mul_comm 256]

/-- A number below `256 ^ c` is determined by its first `c` bytes. -/
theorem bytes_inj : ∀ (c x y : Nat), x < 256 ^ c → y < 256 ^ c →
    (List.range c).map (fun i => x / 256 ^ i % 256) = (List.range c).map (fun i => y / 256 ^ i % 256) → x = y
  | 0, x, y, hx, hy, _ => by simp at hx hy; omega
  | c + 1, x, y, hx, hy, h => by
    rw [bytes_succ, bytes_succ, List.cons.injEq] at h
    have := bytes_inj c (x / 256) (y / 256) (by rw [Nat.pow_succ] at hx; omega)
      (by rw [Nat.pow_succ] at hy; omega) h.2
    omega

/-! ## The limb ranges -/

/-- The bytes held by limb `j` of a `Bytes n` value. -/
def Bytes.limbCount (n j : Nat) : Nat := if j = 0 then n - 31 * (byteLimbs n - 1) else 31

theorem Bytes.ranges_eq (n : Nat) :
    Value.ranges (Bytes n) = (List.range (byteLimbs n)).map fun j => some (.bits (8 * Bytes.limbCount n j)) := by
  simp only [Value.ranges, Value.shape, Shape.ranges_prim, Ty.ranges, Bytes.limbCount]
  apply List.map_congr_left; intro j _; split <;> rfl

theorem Bytes.limbCount_le (n j : Nat) : Bytes.limbCount n j ≤ 31 := by
  unfold Bytes.limbCount byteLimbs; split <;> omega

/-- Limbs that pass the `Bytes n` range checks are each below `2 ^ (8 · count)`. -/
theorem Bytes.limbs_lt {n : Nat} {xs : List Fr} (hl : xs.length = byteLimbs n)
    (h : rangesHold (Value.ranges (Bytes n)) xs = true) :
    ∀ j (hj : j < xs.length), xs[j].val < 2 ^ (8 * Bytes.limbCount n j) := by
  rw [Bytes.ranges_eq] at h
  intro j hj
  unfold rangesHold at h
  rw [List.all_eq_true] at h
  have hmem : (some (Range.bits (8 * Bytes.limbCount n j)), xs[j]) ∈
      ((List.range (byteLimbs n)).map fun j => some (Range.bits (8 * Bytes.limbCount n j))).zip xs := by
    rw [List.mem_iff_getElem]
    exact ⟨j, by simp [hl] at hj ⊢; omega, by simp⟩
  have := h _ hmem
  simp only [Option.all, Range.holds, Zkir.fitsBits, Zkir.frBits, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.2

/-- Hence below the limb base. -/
theorem Bytes.limbs_lt_base {n : Nat} {xs : List Fr} (hl : xs.length = byteLimbs n)
    (h : rangesHold (Value.ranges (Bytes n)) xs = true) : ∀ x ∈ xs, x.val < limbBase := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hx
  exact Nat.lt_of_lt_of_le (Bytes.limbs_lt hl h j hj)
    (Nat.pow_le_pow_right (by decide) (by have := Bytes.limbCount_le n j; omega))

/-- The number spelled by limbs in range is below `256 ^ n`: they hold exactly `n` bytes. -/
theorem Bytes.toNat_lt {n : Nat} {xs : List Fr} (hl : xs.length = byteLimbs n)
    (h : rangesHold (Value.ranges (Bytes n)) xs = true) : Bytes.toNat xs < 256 ^ n := by
  have hlt := Bytes.limbs_lt hl h
  match xs, hl with
  | [], hl =>
    have : n = 0 := by unfold byteLimbs at hl; simp at hl; omega
    subst this; simp [Bytes.toNat]
  | x :: rest, hl =>
    rw [toNat_eq_digits, List.map_cons, List.foldl_cons, foldl_digits_acc]
    simp only [Nat.zero_mul, Nat.zero_add, List.length_map]
    have h0 : x.val < 2 ^ (8 * Bytes.limbCount n 0) := hlt 0 (by simp)
    have hr : (rest.map Fr.val).foldl (fun acc d => acc * limbBase + d) 0 < limbBase ^ rest.length := by
      have := foldl_digits_lt limbBase (rest.map Fr.val) (by
        intro d hd; obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hd
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hy
        have := hlt (j + 1) (by simp; omega)
        simp only [List.getElem_cons_succ, Bytes.limbCount, Nat.add_one_ne_zero, ↓reduceIte] at this
        exact this)
      simpa using this
    simp only [List.length_cons] at hl
    have hn : 8 * Bytes.limbCount n 0 + 248 * rest.length = 8 * n := by
      simp only [Bytes.limbCount, ↓reduceIte]; unfold byteLimbs at hl ⊢; omega
    have hB : limbBase ^ rest.length = 2 ^ (248 * rest.length) := by rw [limbBase, ← Nat.pow_mul]
    rw [hB] at hr ⊢
    have h256 : (256 : Nat) ^ n = 2 ^ (8 * Bytes.limbCount n 0) * 2 ^ (248 * rest.length) := by
      rw [← Nat.pow_add, hn, Nat.pow_mul]
    rw [h256]
    have : (x.val + 1) * 2 ^ (248 * rest.length) ≤ 2 ^ (8 * Bytes.limbCount n 0) * 2 ^ (248 * rest.length) :=
      Nat.mul_le_mul_right _ h0
    rw [Nat.add_mul, Nat.one_mul] at this
    omega

/-! ## Equality of `Bytes` is byte-wise -/

/-- **`==.` on `Bytes n` is byte-wise equality**, for values whose limbs pass the `Bytes n`
    range checks (as every argument and witness result of that type does). -/
theorem Bytes.eq_bytes {p : Zkir.Prims} {env : Env} {n : Nat} {a b : Bytes n} {xs ys : List Fr}
    (ha : Bytes.Is p env a xs) (hb : Bytes.Is p env b ys)
    (hlx : xs.length = byteLimbs n) (hly : ys.length = byteLimbs n)
    (hx : rangesHold (Value.ranges (Bytes n)) xs = true) (hy : rangesHold (Value.ranges (Bytes n)) ys = true) :
    Boolean.Is p env (a.eq b) (decide (Bytes.bytesOf n xs = Bytes.bytesOf n ys)) := by
  have h := Bytes.eq_is ha hb (hlx.trans hly.symm)
  have e : decide (xs = ys) = decide (Bytes.bytesOf n xs = Bytes.bytesOf n ys) := by
    apply decide_eq_decide.mpr
    constructor
    · intro h; rw [h]
    · intro h
      exact Bytes.toNat_inj (hlx.trans hly.symm) (Bytes.limbs_lt_base hlx hx) (Bytes.limbs_lt_base hly hy)
        (bytes_inj n _ _ (Bytes.toNat_lt hlx hx) (Bytes.toNat_lt hly hy) h)
  rw [e] at h; exact h

/-! ## Constants: `ofBytes` and `pad` -/

/-- The number `ofBytes` makes of a byte list: little-endian. -/
def Bytes.numOf (bs : List UInt8) : Nat := bs.foldr (fun b acc => acc * 256 + b.toNat) 0

/-- The `i`-th base-256 digit of that number is the `i`-th byte, or 0 past the end. -/
theorem Bytes.numOf_digit : ∀ (bs : List UInt8) (i : Nat),
    Bytes.numOf bs / 256 ^ i % 256 = (bs.map UInt8.toNat).getD i 0
  | [], i => by simp [Bytes.numOf]
  | b :: bs, 0 => by
    simp only [Bytes.numOf, List.foldr_cons, Nat.pow_zero, Nat.div_one, List.map_cons, List.getD_cons_zero]
    have := b.toNat_lt; omega
  | b :: bs, i + 1 => by
    have ih := Bytes.numOf_digit bs i
    simp only [Bytes.numOf, List.foldr_cons, List.map_cons, List.getD_cons_succ] at ih ⊢
    rw [Nat.pow_succ, Nat.mul_comm (256 ^ i) 256, ← Nat.div_div_eq_div_mul]
    have := b.toNat_lt
    rw [show (bs.foldr (fun b acc => acc * 256 + b.toNat) 0 * 256 + b.toNat) / 256 =
      bs.foldr (fun b acc => acc * 256 + b.toNat) 0 by omega]
    exact ih

theorem Bytes.numOf_lt : ∀ bs : List UInt8, Bytes.numOf bs < 256 ^ bs.length
  | [] => by simp [Bytes.numOf]
  | b :: bs => by
    have ih := Bytes.numOf_lt bs
    simp only [Bytes.numOf, List.foldr_cons, List.length_cons, Nat.pow_succ] at ih ⊢
    have := b.toNat_lt
    have : (bs.foldr (fun b acc => acc * 256 + b.toNat) 0 + 1) * 256 ≤ 256 ^ bs.length * 256 :=
      Nat.mul_le_mul_right _ ih
    rw [Nat.add_mul] at this; omega

/-- The limb values of `limbsOf`, as field elements. -/
def Bytes.limbVals (L X : Nat) : List Fr :=
  (List.range L).map fun j => Fr.ofNat ((X >>> (248 * (L - 1 - j))) % 2 ^ 248)

/-- Recomposing the limbs gives the number back, modulo `2 ^ (248·L)`. -/
theorem Bytes.toNat_limbVals (X : Nat) : ∀ L, Bytes.toNat (Bytes.limbVals L X) = X % 2 ^ (248 * L)
  | 0 => by simp [Bytes.limbVals, Bytes.toNat, Nat.mod_one]
  | L + 1 => by
    have hval : ∀ y : Nat, (Fr.ofNat (y % 2 ^ 248)).val = y % 2 ^ 248 := fun y =>
      Fr.val_ofNat_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))
    have hmap : Bytes.limbVals (L + 1) X =
        Fr.ofNat ((X >>> (248 * L)) % 2 ^ 248) :: Bytes.limbVals L X := by
      unfold Bytes.limbVals
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      refine List.cons_eq_cons.2 ⟨by simp, List.map_congr_left fun j hj => ?_⟩
      simp only [Function.comp, List.mem_range] at hj ⊢
      rw [show L + 1 - 1 - (j + 1) = L - 1 - j by omega]
    rw [hmap, toNat_eq_digits, List.map_cons, List.foldl_cons, foldl_digits_acc, ← toNat_eq_digits,
      Bytes.toNat_limbVals X L]
    simp only [Nat.zero_mul, Nat.zero_add, List.length_map, Bytes.limbVals, List.length_range, hval,
      Nat.shiftRight_eq_div_pow]
    rw [show limbBase ^ L = 2 ^ (248 * L) by rw [limbBase, ← Nat.pow_mul],
      show 248 * (L + 1) = 248 * L + 248 by omega, Nat.pow_add, Nat.mod_mul]
    rw [Nat.mul_comm (2 ^ (248 * L)), Nat.add_comm]

/-- The limbs of a constant are what the IR evaluates. -/
theorem Bytes.ofBytes_is {p : Zkir.Prims} {env : Env} (n : Nat) (bs : List UInt8) :
    Bytes.Is p env (Bytes.ofBytes n bs) (Bytes.limbVals (byteLimbs n) (Bytes.numOf (bs.take n))) := by
  unfold Bytes.Is Bytes.ofBytes Bytes.limbsOf Bytes.limbVals Bytes.numOf
  simp only
  induction (List.range (byteLimbs n)) with
  | nil => rfl
  | cons j js ih => simp only [List.map_cons, Expr.evalList, Expr.eval, ih]; rfl

/-- **`ofBytes n bs` means the bytes `bs`, cut or zero-padded to `n`**, and its limbs pass the
    `Bytes n` range checks (so `Bytes.eq_bytes` applies to it). -/
theorem Bytes.ofBytes_bytes (n : Nat) (bs : List UInt8) :
    let vs := Bytes.limbVals (byteLimbs n) (Bytes.numOf (bs.take n))
    vs.length = byteLimbs n ∧
    Bytes.bytesOf n vs = (List.range n).map (fun i => ((bs.take n).map UInt8.toNat).getD i 0) ∧
    rangesHold (Value.ranges (Bytes n)) vs = true := by
  intro vs
  have hX : Bytes.numOf (bs.take n) < 256 ^ n :=
    Nat.lt_of_lt_of_le (Bytes.numOf_lt _) (Nat.pow_le_pow_right (by decide) (by rw [List.length_take]; exact Nat.min_le_left _ _))
  have hnL : n ≤ 31 * byteLimbs n := by unfold byteLimbs; omega
  have hXL : Bytes.numOf (bs.take n) < 2 ^ (248 * byteLimbs n) := by
    refine Nat.lt_of_lt_of_le hX ?_
    rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  refine ⟨by simp [vs, Bytes.limbVals], ?_, ?_⟩
  · unfold Bytes.bytesOf
    rw [Bytes.toNat_limbVals, Nat.mod_eq_of_lt hXL]
    exact List.map_congr_left fun i _ => Bytes.numOf_digit _ i
  · rw [Bytes.ranges_eq]
    unfold rangesHold
    rw [List.all_eq_true]
    intro ⟨r, x⟩ hmem
    obtain ⟨k, hk, hk'⟩ := List.mem_iff_getElem.1 hmem
    simp only [List.getElem_zip, List.getElem_map, List.getElem_range, Prod.mk.injEq, vs, Bytes.limbVals] at hk'
    obtain ⟨rfl, rfl⟩ := hk'
    simp only [List.length_zip, List.length_map, List.length_range] at hk
    simp only [Option.all, Range.holds, Zkir.fitsBits, Zkir.frBits, Bool.and_eq_true, decide_eq_true_eq]
    have hc := Bytes.limbCount_le n k
    refine ⟨decide_eq_true (by omega), ?_⟩
    have hvl : vs.length = byteLimbs n := by simp [vs, Bytes.limbVals]
    rw [hvl, Nat.min_self] at hk
    rw [Fr.val_ofNat_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)), Nat.shiftRight_eq_div_pow]
    by_cases hk0 : k = 0
    · subst hk0
      simp only [Bytes.limbCount, ↓reduceIte]
      refine Nat.lt_of_le_of_lt (Nat.mod_le _ _) ?_
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
      refine Nat.lt_of_lt_of_le hX ?_
      rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]
      exact Nat.pow_le_pow_right (by decide) (by unfold byteLimbs at hk ⊢; omega)
    · simp only [Bytes.limbCount, hk0, ↓reduceIte]
      exact Nat.mod_lt _ (by decide)

/-- `pad n s` means the UTF-8 bytes of `s`, cut or zero-padded to `n` bytes. -/
theorem Bytes.pad_is {p : Zkir.Prims} {env : Env} (n : Nat) (s : String) :
    Bytes.Is p env (Bytes.pad n s) (Bytes.limbVals (byteLimbs n) (Bytes.numOf (s.toUTF8.toList.take n))) ∧
    Bytes.bytesOf n (Bytes.limbVals (byteLimbs n) (Bytes.numOf (s.toUTF8.toList.take n))) =
      (List.range n).map (fun i => ((s.toUTF8.toList.take n).map UInt8.toNat).getD i 0) :=
  ⟨Bytes.ofBytes_is n _, (Bytes.ofBytes_bytes n _).2.1⟩

end Damp
