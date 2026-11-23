/-
The values the token library computes, as field elements, for the end-to-end
theorems of `TokensRuns.lean`.

**Nothing is assumed about the hash functions.** A commitment, a nullifier, a
token type or a derived nonce is whatever the executor's `p : Prims` gives on
the field elements the circuit hashes: `phashFs p align xs` (the persistent
hash's two limbs, high first, exactly as the IR evaluates `persistentHash`),
`p.transientHash xs`. The lemmas here say which field elements are hashed; the
theorems that use them take the hash results as given.

Also: `Value.RoundTrip` for the standard-library structures the token library
uses, and `Value.Shaped` (a value read off a list of expressions of the type's
width, as every `val`, ledger read and witness result is), from which the
parts of a structure can be read.
-/
import Damp.Proofs.Interface.TokenLogic
import Damp.Proofs.Interface.Bytes
import Damp.Lang.Tokens

namespace Damp
open IR

set_option linter.unusedSimpArgs false

variable {p : Zkir.Prims} {env : Env}

/-! ## Widths and round trips -/

theorem Value.width_contractAddress : Value.width ContractAddress = 2 := rfl
theorem Value.width_zswapKey : Value.width ZswapCoinPublicKey = 2 := rfl
theorem Value.width_userAddress : Value.width UserAddress = 2 := rfl
theorem Value.width_coin : Value.width ShieldedCoinInfo = 5 := by
  simp [Value.width, Value.ranges, Value.shape, Shape.ranges_struct, Shape.ranges_prim, Ty.ranges, ranges_uint,
    byteLimbs]
  split <;> rfl
theorem Value.width_qcoin : Value.width QualifiedShieldedCoinInfo = 6 := by
  simp [Value.width, Value.ranges, Value.shape, Shape.ranges_struct, Shape.ranges_prim, Ty.ranges, ranges_uint,
    byteLimbs]
  split <;> split <;> rfl
theorem Value.width_either {α β : Type} [Value α] [Value β] :
    Value.width (Either α β) = 1 + Value.width α + Value.width β := by
  simp [Value.width, Value.ranges, Value.shape, Shape.ranges_struct, Shape.ranges_prim, Ty.ranges]; omega

theorem roundTrip_contractAddress : Value.RoundTrip ContractAddress := fun es h => by
  show ExprsEquiv (es.take (byteLimbs 32)) es
  rw [show byteLimbs 32 = es.length from h.symm, List.take_length]; exact ExprsEquiv.refl _

theorem roundTrip_zswapKey : Value.RoundTrip ZswapCoinPublicKey := fun es h => by
  match es, h with
  | [a, b], _ => exact ExprsEquiv.refl _

theorem roundTrip_userAddress : Value.RoundTrip UserAddress := fun es h => by
  show ExprsEquiv (es.take (byteLimbs 32)) es
  rw [show byteLimbs 32 = es.length from h.symm, List.take_length]; exact ExprsEquiv.refl _

theorem roundTrip_either {α β : Type} [Value α] [Value β] (ha : Value.RoundTrip α) (hb : Value.RoundTrip β) :
    Value.RoundTrip (Either α β) := fun es h => by
  rw [Value.width_either] at h
  match es, h with
  | [], h => simp at h; omega
  | e :: es, h =>
    show ExprsEquiv ([e] ++ (Value.toExprs (Value.ofExprs (es.take (Value.width α)) : α) ++
      Value.toExprs (Value.ofExprs (es.drop (Value.width α)) : β))) ([e] ++ es)
    refine (ExprsEquiv.refl _).append ?_
    conv => rhs; rw [← List.take_append_drop (Value.width α) es]
    exact (ha _ (by simp at h ⊢; omega)).append (hb _ (by simp at h ⊢; omega))

theorem uint128_bound : (340282366920938463463374607431768211455 : Nat) ≤ Uint.maxBound := by decide
theorem uint64_bound : (18446744073709551615 : Nat) ≤ Uint.maxBound := by decide

theorem roundTrip_coin : Value.RoundTrip ShieldedCoinInfo := fun es h => by
  rw [Value.width_coin] at h
  match es, h with
  | [a, b, c, d, f], _ =>
    have e : (Value.toExprs (Value.ofExprs [a, b, c, d, f] : ShieldedCoinInfo)) =
        [a, b, c, d] ++ (Value.toExprs (Value.ofExprs [f] : Uint128) ++ []) := by
      simp only [Value.ofExprs, Value.toExprs, Value.take_eq, Value.width_uint, Value.width_bytes,
        show byteLimbs 32 = 2 from rfl, List.take, List.drop, List.headD, List.cons_append, List.nil_append]
    rw [e, List.append_nil]
    exact (ExprsEquiv.refl _).append (roundTrip_uint uint128_bound [f] (by rw [Value.width_uint]; rfl))

theorem roundTrip_qcoin : Value.RoundTrip QualifiedShieldedCoinInfo := fun es h => by
  rw [Value.width_qcoin] at h
  match es, h with
  | [a, b, c, d, f, g], _ =>
    have e : (Value.toExprs (Value.ofExprs [a, b, c, d, f, g] : QualifiedShieldedCoinInfo)) =
        [a, b, c, d] ++ (Value.toExprs (Value.ofExprs [f] : Uint128) ++
          (Value.toExprs (Value.ofExprs [g] : Uint64) ++ [])) := by
      simp only [Value.ofExprs, Value.toExprs, Value.take_eq, Value.width_uint, Value.width_bytes,
        show byteLimbs 32 = 2 from rfl, List.take, List.drop, List.headD, List.cons_append, List.nil_append]
    rw [e, List.append_nil, show [a, b, c, d, f, g] = [a, b, c, d] ++ ([f] ++ [g]) from rfl]
    exact (ExprsEquiv.refl _).append ((roundTrip_uint uint128_bound [f] (by rw [Value.width_uint]; rfl)).append
      (roundTrip_uint uint64_bound [g] (by rw [Value.width_uint]; rfl)))

theorem Value.width_sendResult : Value.width ShieldedSendResult =
    Value.width (Maybe ShieldedCoinInfo) + Value.width ShieldedCoinInfo := by
  show (Shape.struct "ShieldedSendResult" ["change", "sent"]
    [Value.shape (Maybe ShieldedCoinInfo), Value.shape ShieldedCoinInfo]).ranges.length = _
  rw [Shape.ranges_struct]
  simp [Value.width, Value.ranges]

theorem roundTrip_sendResult : Value.RoundTrip ShieldedSendResult := fun es h => by
  rw [Value.width_sendResult] at h
  show ExprsEquiv (Value.toExprs (Value.ofExprs (es.take (Value.width (Maybe ShieldedCoinInfo))) : Maybe ShieldedCoinInfo) ++
    (Value.toExprs (Value.ofExprs ((es.drop (Value.width (Maybe ShieldedCoinInfo))).take (Value.width ShieldedCoinInfo)) :
      ShieldedCoinInfo) ++ [])) es
  conv => rhs; rw [← List.take_append_drop (Value.width (Maybe ShieldedCoinInfo)) es]
  refine ((roundTrip_maybe roundTrip_coin) _ (by simp; omega)).append ?_
  rw [List.append_nil]
  have : (es.drop (Value.width (Maybe ShieldedCoinInfo))).length = Value.width ShieldedCoinInfo := by simp; omega
  rw [List.take_of_length_le (Nat.le_of_eq this)]
  exact roundTrip_coin _ this

/-! ## Values read off a list of expressions -/

/-- The parts of a shaped `Either` of two 32-byte wrappers. -/
theorem Either.shaped_parts {r : Either ZswapCoinPublicKey ContractAddress} (h : Value.Shaped r) :
    (Value.toExprs r.left).length = 2 ∧ (Value.toExprs r.right).length = 2 := by
  obtain ⟨es, hl, rfl⟩ := h
  rw [Value.width_either] at hl
  match es, hl with
  | [a, b, c, d, f], _ => exact ⟨rfl, rfl⟩

theorem EitherU.shaped_parts {r : Either ContractAddress UserAddress} (h : Value.Shaped r) :
    (Value.toExprs r.left).length = 2 ∧ (Value.toExprs r.right).length = 2 := by
  obtain ⟨es, hl, rfl⟩ := h
  rw [Value.width_either] at hl
  match es, hl with
  | [a, b, c, d, f], _ => exact ⟨rfl, rfl⟩

theorem ContractAddress.shaped_len {a : ContractAddress} (h : Value.Shaped a) : a.bytes.limbs.length = 2 := by
  obtain ⟨es, hl, rfl⟩ := h
  match es, hl with
  | [x, y], _ => rfl

/-- An `Either`'s meaning, split into its parts. -/
theorem either_is {α β : Type} [Value α] [Value β] {r : Either α β} {b : Fr} {ls rs : List Fr}
    (hl : (Value.toExprs r.left).length = ls.length) (h : Value.Is p env r (b :: ls ++ rs)) :
    r.isLeft.expr.eval p env = some b ∧ Value.Is p env r.left ls ∧ Value.Is p env r.right rs := by
  unfold Value.Is at h ⊢
  have e : Value.toExprs r = r.isLeft.expr :: (Value.toExprs r.left ++ Value.toExprs r.right) := rfl
  have h' : Expr.evalList p env (r.isLeft.expr :: (Value.toExprs r.left ++ Value.toExprs r.right)) =
      some (b :: (ls ++ rs)) := by rw [← e, h]; rfl
  obtain ⟨x, xs, hx, hxs, he⟩ := evalList_cons.1 h'
  simp only [List.cons.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨us, vs, huv, hu, hv⟩ := evalList_append_inv hxs
  have hlu : us.length = ls.length := by rw [evalList_length hu, hl]
  have h1 := List.append_inj huv.symm hlu
  rw [h1.1] at hu; rw [h1.2] at hv
  exact ⟨hx, hu, hv⟩

theorem either_mk_is {α β : Type} [Value α] [Value β] {r : Either α β} {b : Fr} {ls rs : List Fr}
    (hb : r.isLeft.expr.eval p env = some b) (hl : Value.Is p env r.left ls) (hr : Value.Is p env r.right rs) :
    Value.Is p env r (b :: ls ++ rs) := by
  unfold Value.Is at *
  show Expr.evalList p env (r.isLeft.expr :: (Value.toExprs r.left ++ Value.toExprs r.right)) = _
  simp [Expr.evalList, hb, evalList_append_some hl hr]

/-! ## Hashes, as functions of the field elements hashed -/

/-- The persistent hash's two limbs (high first), as the IR evaluates
    `persistentHash`: whatever `p.persistentHash` gives. -/
def phashFs (p : Zkir.Prims) (align : List Zkir.AlignAtom) (xs : List Fr) : Option (List Fr) := do
  let d ← p.persistentHash align xs
  match Zkir.bytesToNatives d with
  | [lo, hi] => some [hi, lo]
  | _ => none

theorem phashFs_length {align : List Zkir.AlignAtom} {xs hs : List Fr} (h : phashFs p align xs = some hs) :
    hs.length = 2 := by
  unfold phashFs at h
  cases hd : p.persistentHash align xs with
  | none => simp [hd] at h
  | some d =>
    simp only [hd, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; rfl
    · simp at h

theorem phash_pair_is {align : List Zkir.AlignAtom} {es : List Expr} {xs hs : List Fr}
    (hx : Expr.evalList p env es = some xs) (hh : phashFs p align xs = some hs) (f : Expr → Expr)
    (hf : ∀ e, (f e).eval p env = e.eval p env) :
    Expr.evalList p env [f (.phash true align es), f (.phash false align es)] = some hs := by
  unfold phashFs at hh
  cases hd : p.persistentHash align xs with
  | none => simp [hd] at hh
  | some d =>
    simp only [hd, Option.bind_eq_bind, Option.bind_some] at hh
    split at hh
    · rename_i lo hi heq
      simp only [Option.some.injEq] at hh
      subst hh
      simp [Expr.evalList, hf, Expr.eval, hx, hd, heq]
    · simp at hh

/-- `persistentHash x` means `phashFs` of what `x` means. -/
theorem persistentHash_is {α : Type} [Value α] {x : α} {xs hs : List Fr} (hx : Value.Is p env x xs)
    (hh : phashFs p ((Value.tys α).map Ty.align) xs = some hs) : Value.Is p env (persistentHash x) hs :=
  phash_pair_is hx hh id (fun _ => rfl)

/-- `persistentCommit x r` means `phashFs` of `r` then `x`, aligned `bytes 32` first. -/
theorem persistentCommit_is {α : Type} [Value α] {x : α} {r : Bytes 32} {xs rs hs : List Fr}
    (hx : Value.Is p env x xs) (hr : Value.Is p env r rs)
    (hh : phashFs p (.bytes 32 :: (Value.tys α).map Ty.align) (rs ++ xs) = some hs) :
    Value.Is p env (persistentCommit x r) hs :=
  phash_pair_is (evalList_append_some hr hx) hh .disclose (fun _ => rfl)

/-! ### Coin commitments and nullifiers -/

/-- The field elements of a 21-byte domain separator. -/
def dsep21 (s : String) : List Fr := Bytes.limbVals (byteLimbs 21) (Bytes.numOf (s.toUTF8.toList.take 21))

/-- The alignment of a `CoinPreimage`, what commitments and nullifiers hash. -/
def coinPreimageAlign : List Zkir.AlignAtom := (Value.tys CoinPreimage).map Ty.align

/-- The field elements a commitment of the coin meaning `coinFs`, sent to a
    recipient meaning `Fr.ofBool u :: ls ++ rs`, hashes: the domain separator,
    the coin, the flag, and the chosen side. -/
def ccPre (coinFs : List Fr) (u : Bool) (ls rs : List Fr) : List Fr :=
  dsep21 "midnight:zswap-cc[v1]" ++ (coinFs ++ ([Fr.ofBool u] ++ ((if u then ls else rs) ++ [])))

/-- The field elements a nullifier of the coin meaning `coinFs` held by the
    contract whose address means `as` hashes. -/
def cnPre (coinFs as : List Fr) : List Fr :=
  dsep21 "midnight:zswap-cn[v1]" ++ (coinFs ++ ([Fr.ofBool false] ++ (as ++ [])))

/-- **`coinCommitment coin r`** means the persistent hash of `ccPre`, whatever
    the hash function. -/
theorem coinCommitment_is {coin : ShieldedCoinInfo} {r : Either ZswapCoinPublicKey ContractAddress}
    {coinFs ls rs cm : List Fr} {u : Bool} (hc : Value.Is p env coin coinFs)
    (hsh : (Value.toExprs r.left).length = 2 ∧ (Value.toExprs r.right).length = 2) (hls : ls.length = 2)
    (hr : Value.Is p env r (Fr.ofBool u :: ls ++ rs))
    (hh : phashFs p coinPreimageAlign (ccPre coinFs u ls rs) = some cm) :
    Value.Is p env (coinCommitment coin r) cm := by
  obtain ⟨hb, hl, hrr⟩ := either_is (by rw [hsh.1, hls]) hr
  have hbool : Boolean.Is p env r.isLeft u := hb
  have e1 : Value.toExprs r.left = Value.toExprs r.left.bytes ++ [] := rfl
  have e2 : Value.toExprs r.right = Value.toExprs r.right.bytes := rfl
  unfold Value.Is at hl hrr
  rw [e1, List.append_nil] at hsh hl
  rw [e2] at hsh hrr
  have hsel : Value.Is p env (select r.isLeft r.left.bytes r.right.bytes) (if u then ls else rs) :=
    select_is roundTrip_bytes hbool hsh.1 hsh.2 hl hrr
  refine persistentHash_is ?_ hh
  have hd := (Bytes.pad_is (p := p) (env := env) 21 "midnight:zswap-cc[v1]").1
  unfold Value.Is
  show Expr.evalList p env ((Bytes.pad 21 "midnight:zswap-cc[v1]").limbs ++ (Value.toExprs coin ++
    ([r.isLeft.expr] ++ (Value.toExprs (select r.isLeft r.left.bytes r.right.bytes) ++ [])))) = _
  unfold ccPre dsep21
  refine evalList_append_some hd (evalList_append_some hc (evalList_append_some ?_
    (evalList_append_some hsel rfl)))
  simp [Expr.evalList, hb]

/-- **`coinNullifier coin addr`** means the persistent hash of `cnPre`. -/
theorem coinNullifier_is {coin : ShieldedCoinInfo} {addr : ContractAddress} {coinFs as nf : List Fr}
    (hc : Value.Is p env coin coinFs) (ha : Value.Is p env addr as)
    (hh : phashFs p coinPreimageAlign (cnPre coinFs as) = some nf) :
    Value.Is p env (coinNullifier coin addr) nf := by
  refine persistentHash_is ?_ hh
  have hd := (Bytes.pad_is (p := p) (env := env) 21 "midnight:zswap-cn[v1]").1
  unfold Value.Is
  show Expr.evalList p env ((Bytes.pad 21 "midnight:zswap-cn[v1]").limbs ++ (Value.toExprs coin ++
    ([Expr.const 0] ++ (addr.bytes.limbs ++ [])))) = _
  unfold cnPre dsep21
  exact evalList_append_some hd (evalList_append_some hc (evalList_append_some rfl
    (evalList_append_some ha rfl)))

/-! ### Token types -/

/-- The field elements of a 32-byte constant string. -/
def dsep32 (s : String) : List Fr := Bytes.limbVals (byteLimbs 32) (Bytes.numOf (s.toUTF8.toList.take 32))

/-- What `tokenType ds addr` commits to, with opening `"midnight:derive_token"`. -/
def tokenTypePre (dsFs addrFs : List Fr) : List Fr := dsep32 "midnight:derive_token" ++ (dsFs ++ (addrFs ++ []))

def tokenTypeAlign : List Zkir.AlignAtom := .bytes 32 :: (Value.tys (Vector (Bytes 32) 2)).map Ty.align

/-- **`tokenType ds addr`** means the persistent commitment `phashFs` of
    `tokenTypePre`, whatever the hash function. -/
theorem tokenType_is {ds : Bytes 32} {addr : ContractAddress} {dsFs as ts : List Fr}
    (hd : Value.Is p env ds dsFs) (ha : Value.Is p env addr as)
    (hh : phashFs p tokenTypeAlign (tokenTypePre dsFs as) = some ts) : Value.Is p env (tokenType ds addr) ts := by
  refine persistentCommit_is (x := (#v[ds, addr.bytes] : Vector (Bytes 32) 2)) (xs := dsFs ++ (as ++ []))
    ?_ (Bytes.pad_is (p := p) (env := env) 32 "midnight:derive_token").1 hh
  unfold Value.Is
  show Expr.evalList p env (ds.limbs ++ (addr.bytes.limbs ++ [])) = _
  exact evalList_append_some hd (evalList_append_some ha rfl)

/-! ### Derived nonces -/

/-- The field element `Field.ofString s`. -/
def fieldConst (s : String) : Fr :=
  Fr.ofInt ((s.toUTF8.toList.foldr (fun b acc => acc * 256 + b.toNat) 0 % Fr.modulus : Nat) : Int)

/-- The 32 bytes of a nonce derived under `domain` from a nonce whose limbs are
    `nonceFs` (the token library's `derivedNonce`, `evolveNonce` without the
    counter): the transient hash of the domain and the nonce's low limb, cut to
    31 bytes, under a zero top byte. -/
def derivedNonceFs (p : Zkir.Prims) (domain : String) (nonceFs : List Fr) : List Fr :=
  [Fr.ofInt 0, Fr.ofNat ((p.transientHash [fieldConst domain, nonceFs.getD 1 0]).val % 2 ^ 248)]

/-- **A derived nonce** means `derivedNonceFs`, whatever the hash function. -/
theorem derivedNonce_is {nonce : Bytes 32} {nonceFs : List Fr} (domain : String) (hl : nonce.limbs.length = 2)
    (hn : Value.Is p env nonce nonceFs) :
    Value.Is p env (upgradeFromTransient (transientHash (#v[Field.ofString domain, degradeToTransient nonce] :
      Vector Field 2))) (derivedNonceFs p domain nonceFs) := by
  match h : nonce.limbs, hl with
  | [a, b], _ =>
    unfold Value.Is at hn
    have hn' : Expr.evalList p env [a, b] = some nonceFs := by rw [← h]; exact hn
    obtain ⟨x, xs, hx, hxs, rfl⟩ := evalList_cons.1 hn'
    obtain ⟨y, ys, hy, hys, rfl⟩ := evalList_cons.1 hxs
    simp [Expr.evalList] at hys; subst hys
    unfold Value.Is
    show Expr.evalList p env [.const 0, .divmod false 248 (.hash ([Expr.const _] ++
      ([(nonce.limbs.getD 1 (.const 0))] ++ [])))] = _
    rw [h]
    simp [Expr.evalList, Expr.eval, hy, derivedNonceFs, fieldConst]

end Damp

