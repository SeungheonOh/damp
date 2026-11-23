/-
Soundness of `Circuit.shareSelects` and `Circuit.shareGuarded`
(`Damp/Optimize/ShareHashes.lean`).

What holds, exactly:

* For the transient hash, `select c (hash as) (hash bs)` and
  `hash (zipSel c as bs)` evaluate to the same thing, failures included, for
  every choice of hash functions, when `as` and `bs` have the same length and
  differ somewhere (`shareSel_hash_eval`).
* For the persistent hash the two differ for some hash functions (the first
  fails when the hash of the arm not taken fails). They agree for
  `Damp.Crypto.prims` when, wherever `as` and `bs` differ, both are constants
  that fit the bytes their place is read as (`phashMergeable`), because there
  a hash succeeds or fails on its input's shape and on whether each byte slot
  fits (`binaryRepr_isSome_transfer`), and its digest is always 32 bytes, two
  field elements (`Crypto.prims_natives`). So `Circuit.shareSelects` is sound
  for `Crypto.prims` (`Circuit.shareSelects_soundFor`), not for every `p`.
* A ledger statement evaluates its operands whatever its guard and uses
  their values only when the guard is 1. So an operand may be replaced by one
  equal to it when the guard is 1 and failing exactly when it does when the
  guard is 0 (`ledger_exec_congr`, `ledger_step_congr`); a verified
  replacement (`Repl.ok`) is such a pair for `Crypto.prims`
  (`Repl.ok_spec`). `Circuit.shareGuarded` is sound for `Crypto.prims`
  (`Circuit.shareGuarded_soundFor`). It keeps every ledger statement's guard,
  reads and instructions, and their order; only how operands are computed
  changes, and only where `ledgerProblem` still accepts the statement.
-/
import Damp.Optimize.ShareHashes
import Damp.Proofs.Optimize.MergeChecks
import Damp.Crypto.Prims

namespace Damp.IR
open Damp.Zkir (Prims AlignAtom bytesToNatives)
open Damp.Emit (Agree eval_congr evalList_congr)
open Damp.Exec

/-! ## The digest of Damp's persistent hash -/

theorem sha_compress_size (h : Array UInt32) (m : Array UInt8) (off : Nat) :
    (Crypto.Sha256.compress h m off).size = 8 := by
  simp [Crypto.Sha256.compress]

theorem sha_hash_length (msg : List UInt8) : (Crypto.Sha256.hash msg).length = 32 := by
  have fold : ∀ (l : List Nat) (h : Array UInt32), h.size = 8 →
      (l.foldl (fun h i => Crypto.Sha256.compress h (Crypto.Sha256.pad msg).toArray (64 * i)) h).size = 8 := by
    intro l; induction l with
    | nil => intro h hh; simpa using hh
    | cons a l ih => intro h _; simp only [List.foldl_cons]; exact ih _ (sha_compress_size _ _ _)
  simp only [Crypto.Sha256.hash]
  rw [List.length_flatMap]
  simp only [List.length_cons, List.length_nil]
  have hs := fold (List.range ((Crypto.Sha256.pad msg).toArray.size / 64)) Crypto.Sha256.H0.toArray (by decide)
  generalize (List.foldl (fun h i => Crypto.Sha256.compress h (Crypto.Sha256.pad msg).toArray (64 * i))
    Crypto.Sha256.H0.toArray (List.range ((Crypto.Sha256.pad msg).toArray.size / 64))) = a at hs ⊢
  have key : ∀ l : List UInt32, (List.map (fun _ => 0 + 1 + 1 + 1 + 1) l).sum = 4 * l.length := by
    intro l; induction l with
    | nil => rfl
    | cons x l ih => simp [List.sum_cons, ih]; omega
  rw [key, Array.length_toList, hs]

theorem bytesToNatives_32 (bs : List Nat) (h : bs.length = 32) : ∃ lo hi, bytesToNatives bs = [lo, hi] := by
  rw [bytesToNatives, dif_neg (by omega), bytesToNatives, dif_pos (by simp [h])]
  exact ⟨_, _, rfl⟩

/-- Damp's persistent hash always yields two field elements. -/
theorem Crypto.prims_natives {al : List AlignAtom} {vs : List Fr} {d : List Nat}
    (h : Crypto.prims.persistentHash al vs = some d) : ∃ lo hi, bytesToNatives d = [lo, hi] := by
  simp only [Crypto.prims, Crypto.persistentHash, Option.map_eq_some_iff] at h
  obtain ⟨bs, _, rfl⟩ := h
  apply bytesToNatives_32
  simp [Crypto.Sha256.hashNat, sha_hash_length]

/-! ## Which inputs the persistent hash accepts -/

theorem alignSlots_map {α β : Type} (g : α → β) : ∀ (al : List AlignAtom) (l : List α),
    alignSlots al (l.map g) = (alignSlots al l).map (fun y => (g y.1, y.2))
  | [], _ => by simp [alignSlots]
  | .compress :: _, _ => by simp [alignSlots]
  | .field :: _, [] => by simp [alignSlots]
  | .field :: al, x :: xs => by simp only [List.map_cons, alignSlots]; exact alignSlots_map g al xs
  | .bytes n :: al, xs => by
      simp only [alignSlots, List.length_map]
      by_cases hlen : xs.length < n / 31 + (if n % 31 ≠ 0 then 1 else 0)
      · rw [if_pos hlen, if_pos hlen]; rfl
      rw [if_neg hlen, if_neg hlen]
      by_cases hz : n % 31 = 0
      · rw [if_pos hz, if_pos hz, ← List.map_drop, alignSlots_map g al]
        simp [List.map_take, Function.comp_def]
      · rw [if_neg hz, if_neg hz]
        cases xs with
        | nil => rfl
        | cons x r =>
            simp only [List.map_cons]
            rw [← List.map_drop, alignSlots_map g al]
            simp [List.map_take, Function.comp_def]

theorem alignSlots_mem {α : Type} : ∀ (al : List AlignAtom) (l : List α) (y : α × Nat),
    y ∈ alignSlots al l → y.1 ∈ l
  | [], _, _, h => by simp [alignSlots] at h
  | .compress :: _, _, _, h => by simp [alignSlots] at h
  | .field :: _, [], _, h => by simp [alignSlots] at h
  | .field :: al, x :: xs, y, h => by
      simp only [alignSlots] at h
      exact List.mem_cons_of_mem _ (alignSlots_mem al xs y h)
  | .bytes n :: al, xs, y, h => by
      simp only [alignSlots] at h
      by_cases hlen : xs.length < n / 31 + (if n % 31 ≠ 0 then 1 else 0)
      · rw [if_pos hlen] at h; simp at h
      rw [if_neg hlen] at h
      by_cases hz : n % 31 = 0
      · rw [if_pos hz] at h
        rcases List.mem_append.mp h with h | h
        · simp only [List.mem_map] at h
          obtain ⟨x, hx, rfl⟩ := h
          exact List.mem_of_mem_take hx
        · exact List.mem_of_mem_drop (alignSlots_mem al _ y h)
      · rw [if_neg hz] at h
        cases xs with
        | nil => simp at h
        | cons x r =>
            simp only [List.mem_cons, List.mem_append, List.mem_map] at h
            rcases h with rfl | ⟨z, hz, rfl⟩ | h
            · simp
            · exact List.mem_cons_of_mem _ (List.mem_of_mem_take hz)
            · exact List.mem_cons_of_mem _ (List.mem_of_mem_drop (alignSlots_mem al _ y h))

/-- A `Bytes<n>` atom parses when there are enough elements and each fits. -/
theorem parseBytesAtom_of_fits {n : Nat} {ys : List Fr}
    (hlen : ¬ ys.length < n / 31 + (if n % 31 ≠ 0 then 1 else 0))
    (h0 : n % 31 = 0 → ∀ y ∈ ys.take (n / 31), y.val < 2 ^ 248)
    (h1 : n % 31 ≠ 0 → ∀ y r, ys = y :: r → y.val < 2 ^ (8 * (n % 31)) ∧ ∀ z ∈ r.take (n / 31), z.val < 2 ^ 248) :
    ∃ bs, Crypto.parseBytesAtom n ys = some (bs, if n % 31 = 0 then ys.drop (n / 31) else ys.tail.drop (n / 31)) := by
  by_cases hz : n % 31 = 0
  · have hall := h0 hz
    simp only [Crypto.parseBytesAtom, hz, ite_true]
    rw [if_neg (by simpa [hz] using hlen)]
    have : (ys.take (n / 31)).all (·.val < 2 ^ 248) = true := List.all_eq_true.mpr (fun y hy => by simpa using hall y hy)
    simp [this]
  · cases ys with
    | nil => simp [hz] at hlen
    | cons y r =>
        obtain ⟨hy, hr⟩ := h1 hz y r rfl
        simp only [Crypto.parseBytesAtom, hz, ite_false]
        rw [if_neg (by simpa [hz] using hlen)]
        have : (r.take (n / 31)).all (·.val < 2 ^ 248) = true := List.all_eq_true.mpr (fun z hz' => by simpa using hr z hz')
        simp [hy, this]

/-- The persistent hash's parse succeeds on inputs of the length of some it
    succeeds on, whose byte slots all fit. -/
theorem binaryRepr_some_of_slots : ∀ (al : List AlignAtom) (xs ys : List Fr),
    (Crypto.binaryRepr al xs).isSome → ys.length = xs.length →
      (∀ y ∈ alignSlots al ys, y.1.val < 2 ^ y.2) → (Crypto.binaryRepr al ys).isSome
  | [], _, _, _, _, _ => by simp [Crypto.binaryRepr]
  | .compress :: _, _, _, h, _, _ => by simp [Crypto.binaryRepr, Crypto.parseAtom] at h
  | .field :: _, [], _, h, _, _ => by simp [Crypto.binaryRepr, Crypto.parseAtom] at h
  | .field :: _, _ :: _, [], _, hl, _ => by simp at hl
  | .field :: al, x :: xs, y :: ys, h, hl, hf => by
      simp only [Crypto.binaryRepr, Crypto.parseAtom, Option.bind_eq_bind, Option.bind_some,
        Option.isSome_bind] at h ⊢
      simp only [alignSlots] at hf
      have := binaryRepr_some_of_slots al xs ys (by
        cases hb : Crypto.binaryRepr al xs <;> simp_all) (by simpa using hl) hf
      cases hb : Crypto.binaryRepr al ys <;> simp_all
  | .bytes n :: al, xs, ys, h, hl, hf => by
      simp only [Crypto.binaryRepr, Crypto.parseAtom, Option.bind_eq_bind, Option.isSome_iff_exists,
        Option.bind_eq_some_iff] at h
      obtain ⟨_, ⟨⟨bs, rest⟩, hp, more, hm, _⟩⟩ := h
      obtain ⟨hlen, hx0, hx1⟩ := hr_parseBytesAtom_spec hp
      have hlen' : ¬ ys.length < n / 31 + (if n % 31 ≠ 0 then 1 else 0) := by rw [hl]; exact hlen
      simp only [alignSlots, hlen', ite_false] at hf
      have hrest : ∀ y ∈ alignSlots al (if n % 31 = 0 then ys.drop (n / 31) else ys.tail.drop (n / 31)),
          y.1.val < 2 ^ y.2 := by
        intro y hy
        by_cases hz : n % 31 = 0
        · simp only [hz, ite_true] at hy hf
          exact hf y (List.mem_append_right _ hy)
        · simp only [hz, ite_false] at hy hf
          cases ys with
          | nil => simp [hz] at hlen'
          | cons y0 r =>
              simp only [List.tail_cons] at hy
              exact hf y (List.mem_cons_of_mem _ (List.mem_append_right _ hy))
      obtain ⟨bs', hp'⟩ := parseBytesAtom_of_fits hlen'
        (fun hz y hy => by
          simp only [hz, ite_true] at hf
          exact hf (y, 248) (List.mem_append_left _ (List.mem_map.mpr ⟨y, hy, rfl⟩)))
        (fun hz y r he => by
          subst he
          simp only [hz, ite_false] at hf
          refine ⟨hf (y, 8 * (n % 31)) (List.mem_cons_self ..), fun z hz' => ?_⟩
          exact hf (z, 248) (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.mpr ⟨z, hz', rfl⟩))))
      have hrest_len : (if n % 31 = 0 then ys.drop (n / 31) else ys.tail.drop (n / 31)).length = rest.length := by
        by_cases hz : n % 31 = 0
        · obtain ⟨_, hr⟩ := hx0 hz
          simp [hz, hr, hl]
        · obtain ⟨x, r, rfl, _, _, hr⟩ := hx1 hz
          simp only [hz, ite_false, hr, List.length_drop, List.length_tail]
          simp at hl; omega
      have := binaryRepr_some_of_slots al rest _ (by simp [hm]) hrest_len hrest
      simp only [Crypto.binaryRepr, Crypto.parseAtom, hp', Option.bind_eq_bind, Option.bind_some, Option.isSome_bind]
      cases hb : Crypto.binaryRepr al (if n % 31 = 0 then ys.drop (n / 31) else ys.tail.drop (n / 31)) <;> simp_all

/-- The half of the persistent hash `phash h al` computes from input values. -/
def phashOf (p : Prims) (h : Bool) (al : List AlignAtom) (vs : List Fr) : Option Fr :=
  (p.persistentHash al vs).bind fun d => match bytesToNatives d with
    | [lo, hi] => some (if h then hi else lo)
    | _ => none

theorem eval_phash (p : Prims) (env : Env) (h : Bool) (al : List AlignAtom) (xs : List Expr) :
    (Expr.phash h al xs).eval p env = (Expr.evalList p env xs).bind (phashOf p h al) := rfl

theorem phashOf_isSome (h : Bool) (al : List AlignAtom) (vs : List Fr) :
    (phashOf Crypto.prims h al vs).isSome = (Crypto.binaryRepr al vs).isSome := by
  unfold phashOf
  cases hb : Crypto.binaryRepr al vs with
  | none => simp [Crypto.prims, Crypto.persistentHash, hb]
  | some bs =>
      have hd : Crypto.prims.persistentHash al vs = some (Crypto.Sha256.hashNat bs) := by
        simp [Crypto.prims, Crypto.persistentHash, hb]
      obtain ⟨lo, hi, hn⟩ := Crypto.prims_natives hd
      simp [hd, hn]

theorem binaryRepr_transfer1 {al : List AlignAtom} {xs ys : List Fr} (hl : xs.length = ys.length)
    (hq : ∀ q ∈ alignSlots al (xs.zip ys), q.1.1 = q.1.2 ∨ q.1.2.val < 2 ^ q.2)
    (hx : (Crypto.binaryRepr al xs).isSome) : (Crypto.binaryRepr al ys).isSome := by
  have ex : alignSlots al xs = (alignSlots al (xs.zip ys)).map (fun q => (q.1.1, q.2)) := by
    rw [← alignSlots_map, List.map_fst_zip (by omega)]
  have ey : alignSlots al ys = (alignSlots al (xs.zip ys)).map (fun q => (q.1.2, q.2)) := by
    rw [← alignSlots_map, List.map_snd_zip (by omega)]
  obtain ⟨bs, hb⟩ := Option.isSome_iff_exists.mp hx
  have fx := hr_binaryRepr_slots al xs bs hb
  refine binaryRepr_some_of_slots al xs ys hx hl.symm fun y hy => ?_
  rw [ey, List.mem_map] at hy
  obtain ⟨q, hq', rfl⟩ := hy
  rcases hq q hq' with he | hf
  · have := fx (q.1.1, q.2) (by rw [ex]; exact List.mem_map.mpr ⟨q, hq', rfl⟩)
    simpa [he] using this
  · exact hf

theorem zip_map_swap {α β : Type} : ∀ (xs : List α) (ys : List β), (xs.zip ys).map Prod.swap = ys.zip xs
  | [], ys => by cases ys <;> rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by simp [zip_map_swap xs ys]

/-- Two lists of input values of the same length that, in every byte slot of
    the alignment, agree or both fit. -/
def SlotsAgree (al : List AlignAtom) (xs ys : List Fr) : Prop :=
  xs.length = ys.length ∧
    ∀ q ∈ alignSlots al (xs.zip ys), q.1.1 = q.1.2 ∨ (q.1.1.val < 2 ^ q.2 ∧ q.1.2.val < 2 ^ q.2)

/-- On such lists, Damp's persistent hash succeeds on both or on neither. -/
theorem binaryRepr_isSome_transfer {al : List AlignAtom} {xs ys : List Fr} (h : SlotsAgree al xs ys) :
    (Crypto.binaryRepr al xs).isSome = (Crypto.binaryRepr al ys).isSome := by
  obtain ⟨hl, hq⟩ := h
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact binaryRepr_transfer1 hl (fun q hq' => (hq q hq').imp id (·.2))
  · refine binaryRepr_transfer1 hl.symm (fun q hq' => ?_)
    have hs : ys.zip xs = (xs.zip ys).map Prod.swap := (zip_map_swap xs ys).symm
    rw [hs, alignSlots_map, List.mem_map] at hq'
    obtain ⟨q0, hq0, rfl⟩ := hq'
    rcases hq q0 hq0 with he | hf
    · exact Or.inl he.symm
    · exact Or.inr hf.1

theorem phashOf_isSome_transfer {al : List AlignAtom} {xs ys : List Fr} (h : SlotsAgree al xs ys) (hh : Bool) :
    (phashOf Crypto.prims hh al xs).isSome = (phashOf Crypto.prims hh al ys).isSome := by
  rw [phashOf_isSome, phashOf_isSome, binaryRepr_isSome_transfer h]

/-! ## Selected inputs -/

/-- A conditional on lists of values. -/
def selL (C : Option Fr) (X Y : Option (List Fr)) : Option (List Fr) :=
  C.bind fun cv => X.bind fun xs => Y.bind fun ys => (asBool cv).bind fun cb => some (if cb then xs else ys)

theorem evalList_cons (p : Prims) (env : Env) (x : Expr) (xs : List Expr) :
    Expr.evalList p env (x :: xs) =
      (x.eval p env).bind fun y => (Expr.evalList p env xs).bind fun ys => some (y :: ys) := rfl

theorem beq_expr (a b : Expr) : (a == b) = a.same b := rfl

/-- `zipSel c as bs` evaluates to the selected list, when `as` and `bs`
    differ somewhere; to `as` when they are the same. -/
theorem evalList_zipSel (p : Prims) (env : Env) (c : Expr) : ∀ (as bs : List Expr), as.length = bs.length →
    Expr.evalList p env (zipSel c as bs) =
      if Expr.sameList as bs then Expr.evalList p env as
      else selL (c.eval p env) (Expr.evalList p env as) (Expr.evalList p env bs)
  | [], [], _ => by simp [zipSel, Expr.sameList, Expr.evalList]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: as, b :: bs, h => by
      have ih := evalList_zipSel p env c as bs (by simpa using h)
      simp only [zipSel, Expr.sameList, beq_expr]
      by_cases hab : a.same b = true
      · have := Expr.same_eq _ _ hab; subst this
        simp only [hab, ite_true, Bool.true_and]
        rw [evalList_cons, ih]
        by_cases hs : Expr.sameList as bs = true
        · have := Expr.sameList_eq _ _ hs; subst this
          simp only [hs, ite_true]; rfl
        · simp only [hs, Bool.false_eq_true, ite_false, evalList_cons, selL]
          generalize c.eval p env = C
          generalize a.eval p env = A
          generalize Expr.evalList p env as = X
          generalize Expr.evalList p env bs = Y
          cases C with
          | none => cases A <;> simp
          | some cv =>
              cases hb : asBool cv with
              | none => cases A <;> cases X <;> cases Y <;> simp [hb]
              | some cb => cases cb <;> cases A <;> cases X <;> cases Y <;> simp [hb]
      · simp only [hab, Bool.false_eq_true, ite_false, Bool.false_and]
        rw [evalList_cons, ih, eval_select]
        by_cases hs : Expr.sameList as bs = true
        · have := Expr.sameList_eq _ _ hs; subst this
          simp only [hs, ite_true, evalList_cons, selL, selv]
          generalize c.eval p env = C
          generalize a.eval p env = A
          generalize b.eval p env = B
          generalize Expr.evalList p env as = X
          cases C with
          | none => simp
          | some cv =>
              cases hb : asBool cv with
              | none => cases A <;> cases B <;> cases X <;> simp [hb]
              | some cb => cases cb <;> cases A <;> cases B <;> cases X <;> simp [hb]
        · simp only [hs, Bool.false_eq_true, ite_false, evalList_cons, selL, selv]
          generalize c.eval p env = C
          generalize a.eval p env = A
          generalize b.eval p env = B
          generalize Expr.evalList p env as = X
          generalize Expr.evalList p env bs = Y
          cases C with
          | none => simp
          | some cv =>
              cases hb : asBool cv with
              | none => cases A <;> cases B <;> cases X <;> cases Y <;> simp [hb]
              | some cb => cases cb <;> cases A <;> cases B <;> cases X <;> cases Y <;> simp [hb]

/-- Lists that agree or hold constants place by place evaluate together. -/
theorem evalList_isSome_agree (p : Prims) (env : Env) : ∀ (as bs : List Expr), as.length = bs.length →
    (as.zip bs).all agreeOrConst = true →
    (Expr.evalList p env as).isSome = (Expr.evalList p env bs).isSome
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: as, b :: bs, h, ha => by
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at ha
      have ih := evalList_isSome_agree p env as bs (by simpa using h) ha.2
      have hab : (a.eval p env).isSome = (b.eval p env).isSome := by
        have h1 := ha.1
        simp only [agreeOrConst, Bool.or_eq_true, beq_expr] at h1
        rcases h1 with h1 | h1
        · rw [Expr.same_eq _ _ h1]
        · split at h1
          · rfl
          · simp at h1
      rw [evalList_cons, evalList_cons]
      cases hxs : Expr.evalList p env as <;> cases hys : Expr.evalList p env bs <;>
        cases ha' : a.eval p env <;> cases hb' : b.eval p env <;> simp_all

theorem evalList_zip_rel (p : Prims) (env : Env) : ∀ (as bs : List Expr) (xs ys : List Fr),
    Expr.evalList p env as = some xs → Expr.evalList p env bs = some ys →
    ∀ e ∈ (as.zip bs).zip (xs.zip ys), e.1.1.eval p env = some e.2.1 ∧ e.1.2.eval p env = some e.2.2
  | a :: as, b :: bs, xs, ys, hx, hy => by
      rw [evalList_cons] at hx hy
      simp only [Option.bind_eq_some_iff, Option.some.injEq] at hx hy
      obtain ⟨x, hx1, xs', hx2, rfl⟩ := hx
      obtain ⟨y, hy1, ys', hy2, rfl⟩ := hy
      intro e he
      simp only [List.zip_cons_cons, List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨hx1, hy1⟩
      · exact evalList_zip_rel p env as bs xs' ys' hx2 hy2 e he
  | [], _, _, _, _, _ => by simp
  | _ :: _, [], _, _, _, _ => by simp

/-- The byte slots of the values of two input lists agree or fit, when those
    of the expressions do (`slotOk`). -/
theorem slotsAgree_of (p : Prims) (env : Env) (al : List AlignAtom) (as bs : List Expr) (xs ys : List Fr)
    (hl : as.length = bs.length) (hs : (alignSlots al (as.zip bs)).all slotOk = true)
    (hx : Expr.evalList p env as = some xs) (hy : Expr.evalList p env bs = some ys) : SlotsAgree al xs ys := by
  have lx := hr_evalList_length hx
  have ly := hr_evalList_length hy
  refine ⟨by omega, fun q hq => ?_⟩
  let L := (as.zip bs).zip (xs.zip ys)
  have h1 : L.map Prod.fst = as.zip bs := List.map_fst_zip (by simp; omega)
  have h2 : L.map Prod.snd = xs.zip ys := List.map_snd_zip (by simp; omega)
  rw [← h2, alignSlots_map, List.mem_map] at hq
  obtain ⟨q0, hq0, rfl⟩ := hq
  have hok : slotOk (q0.1.1, q0.2) = true := List.all_eq_true.mp hs _ (by
    rw [← h1, alignSlots_map]; exact List.mem_map.mpr ⟨q0, hq0, rfl⟩)
  obtain ⟨ea, eb⟩ := evalList_zip_rel p env as bs xs ys hx hy q0.1 (alignSlots_mem al L q0 hq0)
  simp only [slotOk, Bool.or_eq_true, beq_expr] at hok
  rcases hok with he | hk
  · left
    rw [Expr.same_eq _ _ he] at ea
    rw [ea] at eb; exact Option.some.inj eb
  · right
    split at hk
    · rename_i k k' hka hkb
      rw [hka] at ea; rw [hkb] at eb
      simp only [Expr.eval, Option.some.injEq] at ea eb
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
      rw [← ea, ← eb]; exact hk
    · simp at hk

/-! ## The conditional of two hashes -/

theorem eval_hash (p : Prims) (env : Env) (xs : List Expr) :
    (Expr.hash xs).eval p env = (Expr.evalList p env xs).bind fun vs => some (p.transientHash vs) := rfl

/-- The transient hash: exact for every choice of hash functions. -/
theorem shareSel_hash_eval (p : Prims) (env : Env) (c : Expr) (as bs : List Expr)
    (hl : as.length = bs.length) (hd : Expr.sameList as bs = false) :
    (Expr.hash (zipSel c as bs)).eval p env = (Expr.select c (.hash as) (.hash bs)).eval p env := by
  rw [eval_hash, evalList_zipSel p env c as bs hl, hd, eval_select, eval_hash, eval_hash]
  simp only [Bool.false_eq_true, ite_false, selL, selv]
  generalize c.eval p env = C
  generalize Expr.evalList p env as = X
  generalize Expr.evalList p env bs = Y
  cases C with
  | none => simp
  | some cv =>
      cases hb : asBool cv with
      | none => cases X <;> cases Y <;> simp [hb]
      | some cb => cases cb <;> cases X <;> cases Y <;> simp [hb]

/-- The persistent hash: exact for `Crypto.prims` when the inputs differ only
    in constants that fit their byte slots. -/
theorem shareSel_phash_eval (env : Env) (c : Expr) (h : Bool) (al : List AlignAtom) (as bs : List Expr)
    (hm : phashMergeable al as bs = true) :
    (Expr.phash h al (zipSel c as bs)).eval Crypto.prims env =
      (Expr.select c (.phash h al as) (.phash h al bs)).eval Crypto.prims env := by
  simp only [phashMergeable, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hm
  obtain ⟨⟨⟨hl, hd⟩, _⟩, hs⟩ := hm
  rw [eval_phash, evalList_zipSel _ env c as bs hl, hd, eval_select, eval_phash, eval_phash]
  simp only [Bool.false_eq_true, ite_false, selL, selv]
  cases hX : Expr.evalList Crypto.prims env as with
  | none => cases c.eval Crypto.prims env <;> simp
  | some xs =>
  cases hY : Expr.evalList Crypto.prims env bs with
  | none => cases c.eval Crypto.prims env <;> simp
  | some ys =>
  have ht := phashOf_isSome_transfer (slotsAgree_of _ env al as bs xs ys hl hs hX hY) h
  cases C : c.eval Crypto.prims env with
  | none => simp
  | some cv =>
      cases hb : asBool cv with
      | none =>
          cases hpx : phashOf Crypto.prims h al xs <;> cases hpy : phashOf Crypto.prims h al ys <;> simp [hb]
      | some cb =>
          cases cb <;> cases hpx : phashOf Crypto.prims h al xs <;> cases hpy : phashOf Crypto.prims h al ys <;>
            simp_all

theorem shareSelRoot_eval (env : Env) (e : Expr) :
    (shareSelRoot e).eval Crypto.prims env = e.eval Crypto.prims env := by
  unfold shareSelRoot
  split
  · rename_i c as bs
    split
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_true_eq] at hc
      exact shareSel_hash_eval _ env c as bs hc.1.1 hc.1.2
    · rfl
  · rename_i c h al as h' al' bs
    split
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨rfl, rfl⟩, hm⟩ := hc
      exact shareSel_phash_eval env c h al as bs hm
    · rfl
  · rfl

mutual
theorem Expr.shareSel_eval (env : Env) : ∀ e : Expr, e.shareSel.eval Crypto.prims env = e.eval Crypto.prims env
  | .add a b => by simp only [Expr.shareSel, Expr.eval, Expr.shareSel_eval env a, Expr.shareSel_eval env b]
  | .mul a b => by simp only [Expr.shareSel, Expr.eval, Expr.shareSel_eval env a, Expr.shareSel_eval env b]
  | .neg a => by simp only [Expr.shareSel, Expr.eval, Expr.shareSel_eval env a]
  | .lt n a b => by simp only [Expr.shareSel, Expr.eval, Expr.shareSel_eval env a, Expr.shareSel_eval env b]
  | .eq a b => by simp only [Expr.shareSel, Expr.eval, Expr.shareSel_eval env a, Expr.shareSel_eval env b]
  | .select c a b => by
      simp only [Expr.shareSel]
      rw [shareSelRoot_eval]
      simp only [Expr.eval, Expr.shareSel_eval env c, Expr.shareSel_eval env a, Expr.shareSel_eval env b]
  | .hash xs => by simp only [Expr.shareSel, Expr.eval, Expr.shareSelList_eval env xs]
  | .phash h al xs => by simp only [Expr.shareSel, Expr.eval, Expr.shareSelList_eval env xs]
  | .divmod q n a => by simp only [Expr.shareSel, Expr.eval, Expr.shareSel_eval env a]
  | .disclose a => by simp only [Expr.shareSel, Expr.eval, Expr.shareSel_eval env a]
  | .var _ | .const _ | .invalid _ => rfl
theorem Expr.shareSelList_eval (env : Env) :
    ∀ xs : List Expr, Expr.evalList Crypto.prims env (Expr.shareSelList xs) = Expr.evalList Crypto.prims env xs
  | [] => rfl
  | x :: xs => by
      simp only [Expr.shareSelList, Expr.evalList, Expr.shareSel_eval env x, Expr.shareSelList_eval env xs]
end

/-- `Circuit.shareSelects` is sound for Damp's hash functions. -/
theorem Circuit.shareSelects_soundFor : Pass.SoundFor Crypto.prims Circuit.shareSelects :=
  Circuit.mapExprs_soundFor (fun env e => Expr.shareSel_eval env e)

theorem Circuit.shareSelects_checkLedger (c : Circuit) (h : c.checkLedger = .ok ()) :
    c.shareSelects.checkLedger = .ok () :=
  Circuit.mapExprs_checkLedger _ c h

/-! ## Replacements in ledger operands -/

/-- The selection of two lists that evaluate together is the list selected. -/
theorem selL_some {cv : Fr} {cb : Bool} (hcb : asBool cv = some cb) {X Y : Option (List Fr)}
    (hXY : X.isSome = Y.isSome) : selL (some cv) X Y = if cb then X else Y := by
  cases X <;> cases Y <;> simp_all [selL] <;> cases cb <;> simp

theorem bind_isSome_transfer {X Y : Option (List Fr)} {PH : List Fr → Option Fr} (hXY : X.isSome = Y.isSome)
    (htr : ∀ xs ys, X = some xs → Y = some ys → (PH xs).isSome = (PH ys).isSome) :
    (X.bind PH).isSome = (Y.bind PH).isSome := by
  cases hx : X <;> cases hy : Y <;> simp_all

theorem asBool_notv {C : Option Fr} {gv : Fr} {b : Bool} (h : notv C = some gv) (hb : asBool gv = some b) :
    ∃ cv, C = some cv ∧ asBool cv = some (!b) := by
  cases C with
  | none => simp [notv, selv] at h
  | some cv =>
      refine ⟨cv, rfl, ?_⟩
      simp only [notv, selv, Option.bind_some] at h
      rcases asBool_cases cv with hc | ⟨hc, rfl⟩ | ⟨hc, rfl⟩ <;> simp [hc] at h
      · subst h; rw [asBool_zero] at hb; cases hb; exact asBool_one
      · subst h; rw [asBool_one] at hb; cases hb; exact asBool_zero

/-- A verified replacement, in a statement whose guard is `b`: equal to the
    operand it replaces when `b` holds, and failing exactly when it does
    otherwise, in any environment that differs from the statement's only in
    the variables it reads. -/
theorem Repl.ok_spec {D : Defs} {env : Env} (hD : D.Valid Crypto.prims env) {g : Expr} {reads : List Var}
    {r : Repl} (hok : r.ok D g reads = true) {gv : Fr} {b : Bool} (hg : g.eval Crypto.prims env = some gv)
    (hb : asBool gv = some b) (env' : Env) (hag : ∀ u, u ∉ reads → env' u = env u) :
    (b = true → r.new.eval Crypto.prims env' = r.old.eval Crypto.prims env') ∧
      (b = false → (r.new.eval Crypto.prims env').isSome = (r.old.eval Crypto.prims env').isSome) := by
  simp only [Repl.ok, Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨⟨hm, hpol⟩, hvars⟩ := hok
  have hm' := hm
  simp only [phashMergeable, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hm'
  obtain ⟨⟨⟨hl, hd⟩, hagr⟩, hs⟩ := hm'
  have agree : ∀ vs : List Var, (∀ v ∈ vs, v ∈ r.c.vars ++ Expr.varsList r.as ++ Expr.varsList r.bs) →
      Agree vs env' env := fun vs hvs v hv => hag v (by simpa using hvars v (hvs v hv))
  have hc : r.c.eval Crypto.prims env' = r.c.eval Crypto.prims env :=
    eval_congr _ _ (agree _ (fun v hv => by simp [hv]))
  -- The condition's value and the arm it picks.
  obtain ⟨cv, hcv, cb, hcb, hcbb⟩ : ∃ cv, r.c.eval Crypto.prims env = some cv ∧ ∃ cb, asBool cv = some cb ∧
      cb = (if r.pos then b else !b) := by
    by_cases hp : r.pos = true
    · simp only [hp, ite_true, beq_iff_eq] at hpol
      have : r.c.eval Crypto.prims env = g.eval Crypto.prims env := by rw [← hpol, Defs.resolve_eval hD]
      exact ⟨gv, this.trans hg, b, hb, by simp [hp]⟩
    · simp only [hp, Bool.false_eq_true, ite_false] at hpol
      have hn := isNot_eval hD hpol
      rw [hg, eval_not] at hn
      obtain ⟨cv, hcv, hcb⟩ := asBool_notv hn.symm hb
      exact ⟨cv, hcv, !b, hcb, by simp [hp]⟩
  have hXY := evalList_isSome_agree Crypto.prims env' r.as r.bs hl hagr
  have hnew : r.new.eval Crypto.prims env' =
      (if cb then Expr.evalList Crypto.prims env' r.as else Expr.evalList Crypto.prims env' r.bs).bind
        (phashOf Crypto.prims r.h r.al) := by
    simp only [Repl.new]
    rw [eval_phash, evalList_zipSel _ env' r.c r.as r.bs hl, hd, hc, hcv]
    simp only [Bool.false_eq_true, ite_false]
    rw [selL_some hcb hXY]
  have htr := bind_isSome_transfer (PH := phashOf Crypto.prims r.h r.al) hXY (fun xs ys hx hy =>
    phashOf_isSome_transfer (slotsAgree_of _ env' r.al r.as r.bs xs ys hl hs hx hy) r.h)
  simp only [Repl.old, eval_phash, hnew]
  subst hcbb
  constructor
  · intro hbt; subst hbt
    cases r.pos <;> simp
  · intro hbf; subst hbf
    cases r.pos <;> simp [htr]

theorem replaceWith_const (rs : List Repl) (k : Int) : replaceWith rs (.const k) = .const k := by
  unfold replaceWith
  have : rs.find? (fun r => r.old == Expr.const k) = none := by
    rw [List.find?_eq_none]
    intro r _
    simp [Repl.old, beq_expr, Expr.same]
  rw [this]

theorem replaceWith_cases (rs : List Repl) (e : Expr) :
    replaceWith rs e = e ∨ ∃ r ∈ rs, r.old = e ∧ replaceWith rs e = r.new := by
  unfold replaceWith
  cases h : rs.find? (fun r => r.old == e) with
  | none => exact Or.inl rfl
  | some r =>
      right
      refine ⟨r, List.mem_of_find?_eq_some h, ?_, rfl⟩
      have := List.find?_some h
      exact eq_of_beq this

/-- The replacements made in a statement, as one rewrite of its operands. -/
theorem replaceWith_spec {D : Defs} {env : Env} (hD : D.Valid Crypto.prims env) {g : Expr} {reads : List Var}
    (rs : List Repl) {gv : Fr} {b : Bool} (hg : g.eval Crypto.prims env = some gv) (hb : asBool gv = some b)
    (env' : Env) (hag : ∀ u, u ∉ reads → env' u = env u) (e : Expr) :
    (b = true → (replaceWith (rs.filter (Repl.ok D g reads)) e).eval Crypto.prims env' = e.eval Crypto.prims env') ∧
      (b = false → ((replaceWith (rs.filter (Repl.ok D g reads)) e).eval Crypto.prims env').isSome =
        (e.eval Crypto.prims env').isSome) := by
  rcases replaceWith_cases (rs.filter (Repl.ok D g reads)) e with h | ⟨r, hr, hold, h⟩
  · rw [h]; exact ⟨fun _ => rfl, fun _ => rfl⟩
  · rw [h, ← hold]
    exact Repl.ok_spec hD (List.mem_filter.mp hr).2 hg hb env' hag

/-! ## Ledger statements whose operands are rewritten -/

section Congr
variable {p : Prims} (f : Expr → Expr) (hc : ∀ k, f (.const k) = .const k)

theorem evalList_map_eq {env : Env} (hf : ∀ e, (f e).eval p env = e.eval p env) :
    ∀ xs : List Expr, Expr.evalList p env (xs.map f) = Expr.evalList p env xs
  | [] => rfl
  | x :: xs => by simp only [List.map_cons, Expr.evalList, hf x, evalList_map_eq hf xs]

theorem evalList_map_zero {env : Env} (hf : ∀ e, ((f e).eval p env).isSome = (e.eval p env).isSome) :
    ∀ xs : List Expr, (Expr.evalList p env (xs.map f)).map (·.map fun _ => (0 : Fr)) =
      (Expr.evalList p env xs).map (·.map fun _ => (0 : Fr))
  | [] => rfl
  | x :: xs => by
      have ih := evalList_map_zero hf xs
      have hx := hf x
      simp only [List.map_cons, evalList_cons]
      cases h1 : (f x).eval p env <;> cases h2 : x.eval p env <;> simp_all <;>
        cases h3 : Expr.evalList p env (xs.map f) <;> cases h4 : Expr.evalList p env xs <;> simp_all

include hc in
theorem ledgerGroups_congr {env : Env} {active : Bool}
    (hact : active = true → ∀ e, (f e).eval p env = e.eval p env)
    (hin : active = false → ∀ e, ((f e).eval p env).isSome = (e.eval p env).isSome) :
    ∀ ops : List (Impact.Op Expr), ledgerGroups p env active (ops.map (·.map f)) = ledgerGroups p env active ops
  | [] => rfl
  | op :: ops => by
      have ih := ledgerGroups_congr hact hin ops
      simp only [List.map_cons, ledgerGroups, Op.encode_map f hc, ih]
      cases active with
      | true => rw [evalList_map_eq f (hact rfl)]
      | false =>
          have hz := evalList_map_zero f (hin rfl) (op.encode Expr.const)
          cases h1 : Expr.evalList p env ((op.encode Expr.const).map f) <;>
            cases h2 : Expr.evalList p env (op.encode Expr.const) <;> simp_all

theorem request_congr {env : Env} (hf : ∀ e, (f e).eval p env = e.eval p env) :
    ∀ ops : List (Impact.Op Expr), Exec.request p env (ops.map (·.map f)) = Exec.request p env ops
  | [] => rfl
  | op :: ops => by
      simp only [List.map_cons, Exec.request]
      rw [Exec.Op.mapM_map f (Expr.eval p env) (Expr.eval p env) hf op, request_congr hf ops]

end Congr

theorem map_ops_isEmpty (f : Expr → Expr) (ops : List (Impact.Op Expr)) :
    (ops.map (·.map f)).isEmpty = ops.isEmpty := by cases ops <;> rfl

/-- A statement with its verified replacements made runs exactly as before. -/
theorem shareStmt_exec {D : Defs} (rs : List Repl) (st : RunState) (hD : D.Valid Crypto.prims st.env) :
    ∀ s : Stmt, (shareStmt D rs s).exec Crypto.prims st = s.exec Crypto.prims st
  | .ledger g reads ops => by
      simp only [shareStmt]
      split
      · rfl
      split
      · rename_i _ _
        generalize hok : rs.filter (Repl.ok D g reads) = ok
        simp only [Stmt.exec, Option.bind_eq_bind]
        cases hg : g.eval Crypto.prims st.env with
        | none => rfl
        | some gv =>
            simp only [Option.bind_some, map_ops_isEmpty]
            split
            · rfl
            cases hb : asBool gv with
            | none => rfl
            | some b =>
                simp only [Option.bind_some]
                cases hr : readAll b st.env (reads.map fun v => (v, none)) st.pub with
                | none => rfl
                | some ep =>
                    obtain ⟨env', pub'⟩ := ep
                    have hkeep : ∀ u, u ∉ reads → env' u = st.env u := fun u hu =>
                      hr_readAll_keeps _ _ _ _ _ hr u (by simpa [List.map_map, Function.comp_def] using hu)
                    simp only [Option.bind_some]
                    rw [← hok, ledgerGroups_congr _ (replaceWith_const _)
                      (fun hbt e => (replaceWith_spec hD rs hg hb env' hkeep e).1 hbt)
                      (fun hbf e => (replaceWith_spec hD rs hg hb env' hkeep e).2 hbf)]
      · rfl
  | .bind .. | .assert .. | .constrain .. | .witness .. => rfl

/-- ... and so does the executor's step. -/
theorem shareStmt_step {ω σ : Type} {D : Defs} (rs : List Repl) (O : Exec.Oracles ω σ) (st : Exec.State ω σ)
    (hD : D.Valid Crypto.prims st.env) :
    ∀ s : Stmt, Exec.step Crypto.prims O st (shareStmt D rs s) = Exec.step Crypto.prims O st s
  | .ledger g reads ops => by
      simp only [shareStmt]
      split
      · rfl
      split
      · rename_i _ _
        generalize hok : rs.filter (Repl.ok D g reads) = ok
        simp only [Exec.step, Option.bind_eq_bind]
        cases hg : g.eval Crypto.prims st.env with
        | none => rfl
        | some gv =>
            simp only [Option.bind_some, map_ops_isEmpty]
            split
            · rfl
            cases hb : asBool gv with
            | none => rfl
            | some b =>
                simp only [Option.bind_some]
                cases b with
                | true =>
                    simp only [ite_true]
                    rw [← hok, request_congr _ (fun e => (replaceWith_spec hD rs hg hb st.env (fun _ _ => rfl) e).1 rfl)]
                    cases Exec.request Crypto.prims st.env ops with
                    | none => rfl
                    | some req =>
                        simp only [Option.bind_some]
                        cases O.ledger req st.ledger with
                        | none => rfl
                        | some vl =>
                            obtain ⟨vals, l⟩ := vl
                            simp only [Option.bind_some]
                            cases ha : Exec.assign st.env (reads.map fun v => (v, none)) vals with
                            | none => rfl
                            | some env' =>
                                have hkeep : ∀ u, u ∉ reads → env' u = st.env u := fun u hu =>
                                  hr_assign_keeps _ _ _ _ ha u (by simpa [List.map_map, Function.comp_def] using hu)
                                simp only [Option.bind_some]
                                rw [ledgerGroups_congr _ (replaceWith_const _)
                                  (fun hbt e => (replaceWith_spec hD rs hg hb env' hkeep e).1 hbt)
                                  (fun hbf e => (replaceWith_spec hD rs hg hb env' hkeep e).2 hbf)]
                | false =>
                    simp only [Bool.false_eq_true, ite_false]
                    cases ha : Exec.assign st.env (reads.map fun v => (v, none)) (reads.map fun _ => 0) with
                    | none => rfl
                    | some env' =>
                        have hkeep : ∀ u, u ∉ reads → env' u = st.env u := fun u hu =>
                          hr_assign_keeps _ _ _ _ ha u (by simpa [List.map_map, Function.comp_def] using hu)
                        simp only [Option.bind_some]
                        rw [← hok, ledgerGroups_congr _ (replaceWith_const _)
                          (fun hbt e => (replaceWith_spec hD rs hg hb env' hkeep e).1 hbt)
                          (fun hbf e => (replaceWith_spec hD rs hg hb env' hkeep e).2 hbf)]
      · rfl
  | .bind .. | .assert .. | .constrain .. | .witness .. => rfl

/-! ## The pass -/

section Runner
variable {S : Type} {envOf : S → Env} {step : S → Stmt → Option S}

theorem runL_shareGo (hs : StepOK Crypto.prims envOf step)
    (hstmt : ∀ (D : Defs) (rs : List Repl) (st : S) (s : Stmt), D.Valid Crypto.prims (envOf st) →
      step st (shareStmt D rs s) = step st s) (plan : Nat → List Repl) :
    ∀ (D : Defs) (i : Nat) (L : List Stmt) (st : S), D.Valid Crypto.prims (envOf st) →
      runL step (shareGo plan D i L) st = runL step L st
  | _, _, [], _, _ => rfl
  | D, i, s :: rest, st, hD => by
      simp only [shareGo, runL, hstmt D (plan i) st s hD]
      cases h : step st s with
      | none => rfl
      | some st' => exact runL_shareGo hs hstmt plan _ (i + 1) rest st' (Defs.valid_after hs hD h)

end Runner

/-- `Circuit.shareGuarded` does not change a run with Damp's hash functions. -/
theorem Circuit.shareGuarded_run (c : Circuit) (inputs priv pub : List Fr) :
    c.shareGuarded.run Crypto.prims inputs priv pub = c.run Crypto.prims inputs priv pub := by
  simp only [Circuit.run, Circuit.shareGuarded, List.toList_toArray]
  congr 1; funext env; congr 1
  rw [execAll_eq_runL, execAll_eq_runL,
    runL_shareGo (exec_stepOK _) (fun D rs st s hD => shareStmt_exec rs st hD s) _ _ _ _ _ (Defs.valid_nil _ _)]

/-- ... nor what the executor does. -/
theorem Circuit.shareGuarded_exec {ω σ : Type} (O : Exec.Oracles ω σ) (c : Circuit)
    (inputs : List Fr) (private_ : ω) (ledger : σ) :
    Exec.run Crypto.prims O c.shareGuarded inputs private_ ledger = Exec.run Crypto.prims O c inputs private_ ledger := by
  simp only [Exec.run, Circuit.shareGuarded, List.toList_toArray]
  congr 1; funext env; congr 1
  rw [steps_eq_runL, steps_eq_runL,
    runL_shareGo (step_stepOK _ O) (fun D rs st s hD => shareStmt_step rs O st hD s) _ _ _ _ _ (Defs.valid_nil _ _)]

/-- `Circuit.shareGuarded` is sound for Damp's hash functions. -/
theorem Circuit.shareGuarded_soundFor : Pass.SoundFor Crypto.prims Circuit.shareGuarded :=
  ⟨fun c i pr pu => by rw [Circuit.shareGuarded_run], fun O c i w l => by rw [Circuit.shareGuarded_exec]⟩

/-- A statement with its replacements made has no ledger problem if it had none. -/
theorem shareStmt_ledgerProblem (D : Defs) (rs : List Repl) :
    ∀ s : Stmt, s.ledgerProblem = none → (shareStmt D rs s).ledgerProblem = none
  | .ledger g reads ops, h => by
      simp only [shareStmt]
      split
      · exact h
      split
      · rename_i _ hp
        simp only [Stmt.ledgerProblem]
        exact Option.isNone_iff_eq_none.mp hp
      · exact h
  | .bind .., h | .assert .., h | .constrain .., h | .witness .., h => h

theorem shareGo_ledgerProblem (plan : Nat → List Repl) : ∀ (D : Defs) (i : Nat) (L : List Stmt),
    (∀ s ∈ L, s.ledgerProblem = none) → ∀ s ∈ shareGo plan D i L, s.ledgerProblem = none
  | _, _, [], _ => by simp [shareGo]
  | D, i, s :: rest, h => by
      intro x hx
      simp only [shareGo, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact shareStmt_ledgerProblem D _ s (h s (by simp))
      · exact shareGo_ledgerProblem plan _ _ rest (fun y hy => h y (by simp [hy])) x hx

end Damp.IR
