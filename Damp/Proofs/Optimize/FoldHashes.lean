/-
Soundness of `Circuit.foldDivmod` and `Circuit.foldHashes p`
(`Damp/Optimize/FoldHashes.lean`).

`Expr.foldK q hashes` preserves `Expr.eval p` exactly whenever it folds no
hash or folds them with `q = p` (`Expr.foldK_eval`). Hence:

* `Circuit.foldDivmod_sound : Pass.Sound Circuit.foldDivmod` (it folds no
  hash, so it preserves evaluation at every `p`);
* `Circuit.foldHashes_soundFor (p) : Pass.SoundFor p (Circuit.foldHashes p)`:
  sound when the hash functions the circuit is run with are the ones the pass
  computed with. It is *not* `Pass.Sound`: run with other hash functions, a
  folded constant is not what the hash would give.

Both keep `checkLedger` (any `Circuit.mapExprs` does).
-/
import Damp.Optimize.FoldHashes
import Damp.Proofs.Optimize.SoundFor

namespace Damp.IR
open Damp.Zkir (Prims bytesToNatives)

theorem constsOf_eq : ∀ {xs : List Expr} {ks : List Int}, constsOf xs = some ks → xs = ks.map .const
  | [], ks, h => by simp [constsOf] at h; subst h; rfl
  | .const k :: xs, ks, h => by
      simp only [constsOf, Option.map_eq_some_iff] at h
      obtain ⟨ks', h', rfl⟩ := h
      simp [constsOf_eq h']
  | .var _ :: _, _, h | .add .. :: _, _, h | .mul .. :: _, _, h | .neg _ :: _, _, h
  | .lt .. :: _, _, h | .eq .. :: _, _, h | .select .. :: _, _, h | .hash _ :: _, _, h
  | .phash .. :: _, _, h | .divmod .. :: _, _, h | .invalid _ :: _, _, h
  | .disclose _ :: _, _, h => by simp [constsOf] at h

theorem evalList_consts (p : Prims) (env : Env) :
    ∀ ks : List Int, Expr.evalList p env (ks.map .const) = some (ks.map Fr.ofInt)
  | [] => rfl
  | k :: ks => by simp [Expr.evalList, Expr.eval, evalList_consts p env ks]

section
variable (p : Prims) (env : Env)

theorem foldDivmodConst_eval (quot : Bool) (bits : Nat) (a : Expr) :
    (foldDivmodConst quot bits a).eval p env = (Expr.divmod quot bits a).eval p env := by
  unfold foldDivmodConst
  split
  · split
    · rename_i k h
      rw [canon_eval]
      simp [Expr.eval, h]
    · rfl
  · rfl

theorem foldHashConst_eval (xs : List Expr) :
    (foldHashConst p xs).eval p env = (Expr.hash xs).eval p env := by
  unfold foldHashConst
  split
  · rename_i ks h
    rw [canon_eval, constsOf_eq h]
    simp [Expr.eval, evalList_consts]
  · rfl

theorem foldPHashConst_eval (high : Bool) (align : List Zkir.AlignAtom) (xs : List Expr) :
    (foldPHashConst p high align xs).eval p env = (Expr.phash high align xs).eval p env := by
  unfold foldPHashConst
  split
  · rename_i ks h
    split
    · rename_i d hd
      split
      · rename_i lo hi hb
        rw [canon_eval, constsOf_eq h]
        simp [Expr.eval, evalList_consts, hd, hb]
      · rfl
    · rfl
  · rfl

end

mutual
/-- Folding preserves evaluation at `p` exactly, when it folds no hash or
    folds them with `p` itself. -/
theorem Expr.foldK_eval (q : Prims) (hashes : Bool) (p : Prims) (hp : hashes = true → q = p) (env : Env) :
    ∀ e : Expr, (e.foldK q hashes).eval p env = e.eval p env
  | .add a b => by
      simp only [Expr.foldK, Expr.eval, Expr.foldK_eval q hashes p hp env a, Expr.foldK_eval q hashes p hp env b]
  | .mul a b => by
      simp only [Expr.foldK, Expr.eval, Expr.foldK_eval q hashes p hp env a, Expr.foldK_eval q hashes p hp env b]
  | .neg a => by
      simp only [Expr.foldK, Expr.eval, Expr.foldK_eval q hashes p hp env a]
  | .lt bits a b => by
      simp only [Expr.foldK, Expr.eval, Expr.foldK_eval q hashes p hp env a, Expr.foldK_eval q hashes p hp env b]
  | .eq a b => by
      simp only [Expr.foldK, Expr.eval, Expr.foldK_eval q hashes p hp env a, Expr.foldK_eval q hashes p hp env b]
  | .select c a b => by
      simp only [Expr.foldK, Expr.eval, Expr.foldK_eval q hashes p hp env c,
        Expr.foldK_eval q hashes p hp env a, Expr.foldK_eval q hashes p hp env b]
  | .divmod quot bits a => by
      simp only [Expr.foldK, foldDivmodConst_eval, Expr.eval, Expr.foldK_eval q hashes p hp env a]
  | .hash xs => by
      simp only [Expr.foldK]
      cases hashes with
      | true =>
          cases hp rfl
          simp only [ite_true, foldHashConst_eval, Expr.eval, Expr.foldKList_eval q true q hp env xs]
      | false => simp only [Bool.false_eq_true, ite_false, Expr.eval, Expr.foldKList_eval q false p hp env xs]
  | .phash high align xs => by
      simp only [Expr.foldK]
      cases hashes with
      | true =>
          cases hp rfl
          simp only [ite_true, foldPHashConst_eval, Expr.eval, Expr.foldKList_eval q true q hp env xs]
      | false => simp only [Bool.false_eq_true, ite_false, Expr.eval, Expr.foldKList_eval q false p hp env xs]
  | .var _ => rfl
  | .const _ => rfl
  | .invalid _ => rfl
  | .disclose e => by
      simp only [Expr.foldK, Expr.eval, Expr.foldK_eval q hashes p hp env e]
theorem Expr.foldKList_eval (q : Prims) (hashes : Bool) (p : Prims) (hp : hashes = true → q = p) (env : Env) :
    ∀ xs : List Expr, Expr.evalList p env (Expr.foldKList q hashes xs) = Expr.evalList p env xs
  | [] => rfl
  | x :: xs => by
      simp only [Expr.foldKList, Expr.evalList, Expr.foldK_eval q hashes p hp env x,
        Expr.foldKList_eval q hashes p hp env xs]
end

/-- Folding `divmod` of constants is a sound pass. -/
theorem Circuit.foldDivmod_sound : Pass.Sound Circuit.foldDivmod :=
  Circuit.mapExprs_sound fun p env e => Expr.foldK_eval noPrims false p (fun h => nomatch h) env e

/-- Folding hashes of constants with `p` is sound when the hash functions are `p`. -/
theorem Circuit.foldHashes_soundFor (p : Prims) : Pass.SoundFor p (Circuit.foldHashes p) :=
  Circuit.mapExprs_soundFor fun env e => Expr.foldK_eval p true p (fun _ => rfl) env e

theorem Circuit.foldDivmod_checkLedger (c : Circuit) (h : c.checkLedger = .ok ()) :
    (Circuit.foldDivmod c).checkLedger = .ok () :=
  Circuit.mapExprs_checkLedger _ c h

theorem Circuit.foldHashes_checkLedger (p : Prims) (c : Circuit) (h : c.checkLedger = .ok ()) :
    (Circuit.foldHashes p c).checkLedger = .ok () :=
  Circuit.mapExprs_checkLedger _ c h

end Damp.IR
