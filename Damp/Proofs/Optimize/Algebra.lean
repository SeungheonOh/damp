/-
Soundness of `Circuit.algebra` (`Damp/Optimize/Algebra.lean`).

* The generic vehicle: rewriting every expression of a circuit with a function
  that preserves `Expr.eval` exactly leaves `Circuit.run` and `Exec.run`
  unchanged, not just their observable parts (`Circuit.mapExprs_run`,
  `Circuit.mapExprs_exec`), so it is a sound pass (`Circuit.mapExprs_sound`);
  and it keeps `checkLedger` (`Circuit.mapExprs_checkLedger`), whatever the
  function.
* The rewrite `Expr.algebra` preserves `Expr.eval` exactly (`Expr.algebra_eval`).
  Linear normalization is proved through a denotation of linear forms
  (`Algebra.D`): each operation on linear forms preserves it, and the rebuilt
  expression evaluates to it.

The field identities needed (commutativity, associativity, distributivity,
negation) are proved here from the definition of `Fr`, without `ring`.
-/
import Damp.Optimize.Algebra
import Damp.Proofs.Optimize.Sound

namespace Damp.IR.Algebra
open Damp.Zkir (Prims)

/-! ## Field identities -/

theorem fr_add_comm (a b : Fr) : a + b = b + a := by
  apply Fr.ext
  show (a.val + b.val) % Fr.modulus = (b.val + a.val) % Fr.modulus
  rw [Nat.add_comm]

theorem fr_mul_comm (a b : Fr) : a * b = b * a := by
  apply Fr.ext
  show (a.val * b.val) % Fr.modulus = (b.val * a.val) % Fr.modulus
  rw [Nat.mul_comm]

theorem fr_add_assoc (a b c : Fr) : a + b + c = a + (b + c) := by
  apply Fr.ext
  show ((a.val + b.val) % Fr.modulus + c.val) % Fr.modulus =
    (a.val + (b.val + c.val) % Fr.modulus) % Fr.modulus
  rw [Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]

theorem fr_mul_assoc (a b c : Fr) : a * b * c = a * (b * c) := by
  apply Fr.ext
  show ((a.val * b.val) % Fr.modulus * c.val) % Fr.modulus =
    (a.val * ((b.val * c.val) % Fr.modulus)) % Fr.modulus
  rw [Nat.mod_mul_mod, Nat.mul_mod_mod, Nat.mul_assoc]

theorem fr_mul_add (a b c : Fr) : a * (b + c) = a * b + a * c := by
  apply Fr.ext
  show (a.val * ((b.val + c.val) % Fr.modulus)) % Fr.modulus =
    ((a.val * b.val) % Fr.modulus + (a.val * c.val) % Fr.modulus) % Fr.modulus
  rw [Nat.mul_mod_mod, ← Nat.add_mod, Nat.mul_add]

theorem fr_add_mul (a b c : Fr) : (a + b) * c = a * c + b * c := by
  rw [fr_mul_comm, fr_mul_add, fr_mul_comm c a, fr_mul_comm c b]

theorem fr_add_left_comm (a b c : Fr) : a + (b + c) = b + (a + c) := by
  rw [← fr_add_assoc, fr_add_comm a b, fr_add_assoc]

theorem fr_add_neg (a : Fr) : a + -a = 0 := by
  apply Fr.ext
  show (a.val + (Fr.modulus - a.val) % Fr.modulus) % Fr.modulus = (0 : Fr).val
  rw [Nat.add_mod_mod, Fr.val_zero]
  have h := a.isLt
  rw [show a.val + (Fr.modulus - a.val) = Fr.modulus by omega, Nat.mod_self]

theorem fr_neg_add (a : Fr) : -a + a = 0 := by rw [fr_add_comm, fr_add_neg]

/-- An additive inverse is the negation. -/
theorem fr_eq_neg_of_add {b x : Fr} (h : b + x = 0) : b = -x := by
  calc b = b + (x + -x) := by rw [fr_add_neg, Fr.add_zero]
    _ = (b + x) + -x := by rw [fr_add_assoc]
    _ = -x := by rw [h, Fr.zero_add]

theorem fr_neg_one_add_one : (-1 : Fr) + 1 = 0 := by decide

theorem fr_neg_one_mul (x : Fr) : (-1 : Fr) * x = -x := by
  apply fr_eq_neg_of_add
  calc (-1 : Fr) * x + x = (-1) * x + 1 * x := by rw [Fr.one_mul]
    _ = ((-1) + 1) * x := by rw [fr_add_mul]
    _ = 0 := by rw [fr_neg_one_add_one, Fr.zero_mul]

theorem fr_neg_inj {x y : Fr} (h : -x = -y) : x = y := by
  rw [← Fr.neg_neg x, h, Fr.neg_neg]

/-- `x + a = b` exactly when `x = b - a`. -/
theorem fr_add_eq_iff (x a b : Fr) : x + a = b ↔ x = b - a := by
  show x + a = b ↔ x = b + -a
  constructor
  · intro h
    rw [← h, fr_add_assoc, fr_add_neg, Fr.add_zero]
  · intro h
    rw [h, fr_add_assoc, fr_neg_add, Fr.add_zero]

/-- With `k · i = 1`, `k · x = c` exactly when `x = i · c`. -/
theorem fr_mul_eq_iff {k i : Fr} (hk : k * i = 1) (x c : Fr) : k * x = c ↔ x = i * c := by
  constructor
  · intro h
    rw [← h, ← fr_mul_assoc, fr_mul_comm i k, hk, Fr.one_mul]
  · intro h
    rw [h, ← fr_mul_assoc, hk, Fr.one_mul]

/-! ## Option plumbing -/

theorem obind_some {α β : Type} (x : α) (f : α → Option β) : (some x).bind f = f x := rfl

/-! ## Linear forms: the denotation -/

section Lin
variable (p : Prims) (env : Env)

/-- `k + Σ c·a`: fails exactly when one of the atoms does. -/
def D (k : Fr) : List (Fr × Expr) → Option Fr
  | [] => some k
  | t :: ts => do
      let x ← t.2.eval p env
      let y ← D k ts
      pure (t.1 * x + y)

theorem D_nil (k : Fr) : D p env k [] = some k := rfl

theorem D_cons (k : Fr) (c : Fr) (a : Expr) (ts : List (Fr × Expr)) :
    D p env k ((c, a) :: ts) = (a.eval p env).bind fun x => (D p env k ts).bind fun y => some (c * x + y) := rfl

theorem D_shift (k k' : Fr) : ∀ ts : List (Fr × Expr), D p env (k + k') ts = (D p env k' ts).map (k + ·)
  | [] => rfl
  | (c, a) :: ts => by
      rw [D_cons, D_cons, D_shift k k' ts]
      cases a.eval p env <;> cases D p env k' ts <;> simp [fr_add_left_comm]

theorem D_append (k1 k2 : Fr) : ∀ ts1 ts2 : List (Fr × Expr),
    D p env (k1 + k2) (ts1 ++ ts2) =
      (D p env k1 ts1).bind fun y1 => (D p env k2 ts2).bind fun y2 => some (y1 + y2)
  | [], ts2 => by
      rw [List.nil_append, D_shift, D_nil]
      cases D p env k2 ts2 <;> rfl
  | (c, a) :: ts1, ts2 => by
      rw [List.cons_append, D_cons, D_cons, D_append k1 k2 ts1 ts2]
      cases a.eval p env <;> cases D p env k1 ts1 <;> cases D p env k2 ts2 <;> simp [fr_add_assoc]

/-- Terms with the same denotation can be swapped in front of others. -/
theorem D_prefix (k : Fr) {xs ys : List (Fr × Expr)} (h : ∀ k', D p env k' xs = D p env k' ys)
    (zs : List (Fr × Expr)) : D p env k (xs ++ zs) = D p env k (ys ++ zs) := by
  have h1 := D_append p env 0 k xs zs
  have h2 := D_append p env 0 k ys zs
  rw [Fr.zero_add] at h1 h2
  rw [h1, h2, h 0]

theorem D_scale (c k : Fr) : ∀ ts : List (Fr × Expr),
    D p env (c * k) (ts.map fun t => (c * t.1, t.2)) = (D p env k ts).map (c * ·)
  | [] => rfl
  | (d, a) :: ts => by
      rw [List.map_cons, D_cons, D_cons, D_scale c k ts]
      cases a.eval p env <;> cases D p env k ts <;> simp [fr_mul_add, fr_mul_assoc]

theorem D_snoc (k : Fr) (c : Fr) (a : Expr) : ∀ ts : List (Fr × Expr),
    D p env k (ts ++ [(c, a)]) = (a.eval p env).bind fun z => (D p env k ts).bind fun y => some (c * z + y)
  | [] => rfl
  | (c', a') :: ts => by
      rw [List.cons_append, D_cons, D_cons, D_snoc k c a ts]
      cases a.eval p env <;> cases a'.eval p env <;> cases D p env k ts <;> simp [fr_add_left_comm]

theorem D_insert (t : Fr × Expr) : ∀ (acc : List (Fr × Expr)) (k : Fr),
    D p env k (insertTerm t acc) = D p env k (acc ++ [t])
  | [], _ => rfl
  | (c', a') :: rest, k => by
      obtain ⟨c, a⟩ := t
      simp only [insertTerm]
      split
      · rename_i h
        have h' : a' = a := eq_of_beq h
        subst h'
        rw [List.cons_append, D_cons, D_cons, D_snoc]
        cases a'.eval p env <;> cases D p env k rest <;> simp [fr_add_mul, fr_add_assoc]
      · rw [List.cons_append, D_cons, D_cons, D_insert (c, a) rest k]

theorem D_combine (k : Fr) : ∀ (ts acc : List (Fr × Expr)),
    D p env k (combine acc ts) = D p env k (acc ++ ts)
  | [], acc => by simp [combine]
  | t :: ts, acc => by
      rw [combine, D_combine k ts, D_prefix p env k (D_insert p env t acc), List.append_assoc,
        List.singleton_append]

theorem D_filter (k : Fr) : ∀ ts : List (Fr × Expr), D p env k (ts.filter keepTerm) = D p env k ts
  | [] => rfl
  | (c, a) :: ts => by
      rw [List.filter_cons]
      split
      · rw [D_cons, D_cons, D_filter k ts]
      · rename_i h
        have h' : c = 0 ∧ a.total [] = true := by simpa [keepTerm] using h
        obtain ⟨hc, ht⟩ := h'
        obtain ⟨x, hx⟩ := Expr.total_eval p env [] (boolsHold_nil env) a ht
        rw [D_cons, D_filter k ts, hx, hc]
        cases D p env k ts <;> simp [Fr.zero_mul, Fr.zero_add]

theorem term_eval (t : Fr × Expr) : (term t).eval p env = (t.2.eval p env).map (t.1 * ·) := by
  obtain ⟨c, a⟩ := t
  simp only [term]
  split
  · rename_i h; subst h
    cases a.eval p env <;> simp [Fr.one_mul]
  · split
    · rename_i _ h; subst h
      simp only [Expr.eval]
      cases a.eval p env <;> simp [fr_neg_one_mul]
    · simp only [Expr.eval, canon_eval]
      cases a.eval p env <;> simp

theorem sumTerms_eval : ∀ ts : List (Fr × Expr), (sumTerms ts).eval p env = D p env 0 ts
  | [] => rfl
  | [t] => by
      rw [sumTerms, term_eval]
      obtain ⟨c, a⟩ := t
      rw [D_cons, D_nil]
      cases a.eval p env <;> simp [Fr.add_zero]
  | t :: t' :: ts => by
      show Expr.eval p env (.add (term t) (sumTerms (t' :: ts))) = _
      rw [Expr.eval, term_eval, sumTerms_eval (t' :: ts)]
      obtain ⟨c, a⟩ := t
      rw [D_cons p env 0 c a (t' :: ts)]
      cases a.eval p env <;> cases D p env 0 (t' :: ts) <;> simp

theorem mkSum_eval (ts : List (Fr × Expr)) (k : Fr) : (mkSum ts k).eval p env = D p env k ts := by
  simp only [mkSum]
  split
  · rename_i h
    rw [List.isEmpty_iff] at h
    subst h
    exact canon_eval p env k
  · split
    · rename_i _ h; subst h; exact sumTerms_eval p env ts
    · have h := D_shift p env k 0 ts
      rw [Fr.add_zero] at h
      rw [h, Expr.eval, sumTerms_eval, canon_eval]
      cases D p env 0 ts <;> simp [fr_add_comm]

theorem Lin.rebuild_eval (L : Lin) : L.rebuild.eval p env = D p env L.k L.ts := by
  rw [Lin.rebuild, mkSum_eval, D_filter, D_combine, List.nil_append]

/-- A linear form and a rewritten expression, both meaning `e`. -/
structure Good (q : Lin × Expr) (e : Expr) : Prop where
  den : D p env q.1.k q.1.ts = e.eval p env
  eval : q.2.eval p env = e.eval p env

variable {p env}

theorem fin_eval {q : Lin × Expr} {e : Expr} (h : Good p env q e) : (fin q).eval p env = e.eval p env := by
  simp only [fin]
  split
  · rw [Lin.rebuild_eval, h.den]
  · exact h.eval

theorem atomOf_good {e' e : Expr} (h : e'.eval p env = e.eval p env) : Good p env (atomOf e') e where
  den := by
    show D p env 0 [(1, e')] = _
    rw [D_cons, D_nil, ← h]
    cases e'.eval p env <;> simp [Fr.one_mul, Fr.add_zero]
  eval := h

theorem linAdd_good {qa qb : Lin × Expr} {a b : Expr} (ha : Good p env qa a) (hb : Good p env qb b) :
    Good p env (linAdd qa qb) (.add a b) where
  den := by
    show D p env (qa.1.k + qb.1.k) (qa.1.ts ++ qb.1.ts) = _
    rw [D_append, ha.den, hb.den]; rfl
  eval := by
    show Expr.eval p env (.add qa.2 qb.2) = _
    simp only [Expr.eval, ha.eval, hb.eval]

theorem linNeg_good {qa : Lin × Expr} {a : Expr} (ha : Good p env qa a) :
    Good p env (linNeg qa) (.neg a) where
  den := by
    show D p env (-1 * qa.1.k) (qa.1.ts.map fun t => (-1 * t.1, t.2)) = _
    rw [D_scale, ha.den, Expr.eval]
    cases a.eval p env <;> simp [fr_neg_one_mul]
  eval := by
    show Expr.eval p env (.neg qa.2) = _
    simp only [Expr.eval, ha.eval]

theorem linMul_good {qa qb : Lin × Expr} {a b : Expr} (ha : Good p env qa a) (hb : Good p env qb b) :
    Good p env (linMul a b qa qb) (.mul a b) := by
  unfold linMul
  split
  · rename_i k
    constructor
    · show D p env (Fr.ofInt k * qb.1.k) (qb.1.ts.map fun t => (Fr.ofInt k * t.1, t.2)) = _
      rw [D_scale, hb.den]
      simp only [Expr.eval]
      cases b.eval p env <;> rfl
    · show Expr.eval p env (.mul (.const k) qb.2) = _
      simp only [Expr.eval, hb.eval]
  · rename_i k _
    constructor
    · show D p env (Fr.ofInt k * qa.1.k) (qa.1.ts.map fun t => (Fr.ofInt k * t.1, t.2)) = _
      rw [D_scale, ha.den]
      simp only [Expr.eval]
      cases a.eval p env <;> simp [fr_mul_comm]
    · show Expr.eval p env (.mul qa.2 (.const k)) = _
      simp only [Expr.eval, ha.eval]
  · exact atomOf_good (by simp only [Expr.eval, fin_eval ha, fin_eval hb])

/-! ## Comparisons -/

theorem ofBool_decide_congr {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) :
    Fr.ofBool (decide P) = Fr.ofBool (decide Q) := by
  rw [decide_eq_decide.mpr h]

theorem eqOne_eval {e orig : Expr} (horig : orig.eval p env = (Expr.eq e (.const 1)).eval p env) :
    (eqOne e orig).eval p env = (Expr.eq e (.const 1)).eval p env := by
  simp only [eqOne]
  split
  · rename_i hb
    simp only [Expr.eval]
    cases he : e.eval p env with
    | none => rfl
    | some x =>
        rcases Expr.isBool_eval p env [] (boolsHold_nil env) e x hb he with h | h <;> subst h <;> decide
  · exact horig

theorem eqOne_eval' {e orig : Expr} (horig : orig.eval p env = (Expr.eq (.const 1) e).eval p env) :
    (eqOne e orig).eval p env = (Expr.eq (.const 1) e).eval p env := by
  simp only [eqOne]
  split
  · rename_i hb
    simp only [Expr.eval]
    cases he : e.eval p env with
    | none => rfl
    | some x =>
        rcases Expr.isBool_eval p env [] (boolsHold_nil env) e x hb he with h | h <;> subst h <;> decide
  · exact horig

theorem eqScaled_eval (k c : Int) (x orig : Expr)
    (horig : orig.eval p env = (Expr.eq (.mul (.const k) x) (.const c)).eval p env) :
    (eqScaled k c x orig).eval p env = orig.eval p env := by
  simp only [eqScaled]
  split
  · rename_i hk
    rw [horig]
    simp only [Expr.eval, canon_eval]
    cases x.eval p env with
    | none => rfl
    | some v => exact congrArg some (ofBool_decide_congr (fr_mul_eq_iff hk v _)).symm
  · rfl

theorem mkEqA_eval (a b : Expr) : (mkEqA a b).eval p env = (Expr.eq a b).eval p env := by
  unfold mkEqA
  split
  · rename_i x k c
    simp only [Expr.eval, canon_eval]
    cases x.eval p env with
    | none => rfl
    | some v => exact congrArg some (ofBool_decide_congr (fr_add_eq_iff v _ _).symm)
  · rename_i c x k
    simp only [Expr.eval, canon_eval]
    cases x.eval p env with
    | none => rfl
    | some v =>
        exact congrArg some (ofBool_decide_congr
          (eq_comm.trans ((fr_add_eq_iff v _ _).symm.trans eq_comm)))
  · rename_i x y
    simp only [Expr.eval]
    cases x.eval p env with
    | none => rfl
    | some u =>
      cases y.eval p env with
      | none => rfl
      | some v => exact congrArg some (ofBool_decide_congr ⟨fun h => h ▸ rfl, fr_neg_inj⟩)
  · rename_i k x c
    exact eqScaled_eval k c x _ rfl
  · rename_i x k c _
    refine eqScaled_eval k c x _ ?_
    simp only [Expr.eval]
    cases x.eval p env with
    | none => rfl
    | some v => exact congrArg some (by rw [fr_mul_comm])
  · exact eqOne_eval rfl
  · exact eqOne_eval' rfl
  · rfl

/-! ## Conditionals -/

/-- `select c (select c a b) d` is `select c a d` when `b` cannot fail. -/
theorem select_then_eval (c a b d : Expr) (hb : b.total [] = true) :
    (Expr.select c (.select c a b) d).eval p env = (Expr.select c a d).eval p env := by
  obtain ⟨y, hy⟩ := Expr.total_eval p env [] (boolsHold_nil env) b hb
  simp only [Expr.eval, hy]
  cases c.eval p env <;> cases a.eval p env <;> cases d.eval p env <;> simp
  rename_i x _ _
  cases asBool x <;> simp
  rename_i bc
  cases bc <;> rfl

/-- `select c a (select c b d)` is `select c a d` when `b` cannot fail. -/
theorem select_else_eval (c a b d : Expr) (hb : b.total [] = true) :
    (Expr.select c a (.select c b d)).eval p env = (Expr.select c a d).eval p env := by
  obtain ⟨y, hy⟩ := Expr.total_eval p env [] (boolsHold_nil env) b hb
  simp only [Expr.eval, hy]
  cases c.eval p env <;> cases a.eval p env <;> cases d.eval p env <;> simp
  rename_i x _ _
  cases asBool x <;> simp
  rename_i bc
  cases bc <;> rfl

theorem selElse_eval (c a b : Expr) : (selElse c a b).eval p env = (Expr.select c a b).eval p env := by
  unfold selElse
  split
  · rename_i c' b1 d
    split
    · rename_i h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1
      exact (select_else_eval c' a b1 d h2).symm
    · rfl
  · rfl

/-- `select c c 0` and `select c 1 c` are `c` when `c` is 0 or 1. -/
theorem select_self_eval (c a b : Expr) (hc : c.isBool [] = true)
    (h : (a = c ∧ b = .const 0) ∨ (a = .const 1 ∧ b = c)) :
    c.eval p env = (Expr.select c a b).eval p env := by
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rw [ha, hb] <;> simp only [Expr.eval] <;>
  · cases he : c.eval p env with
    | none => rfl
    | some x =>
        rcases Expr.isBool_eval p env [] (boolsHold_nil env) c x hc he with h | h <;> subst h <;> decide

theorem mkSelectA_eval (c a b : Expr) : (mkSelectA c a b).eval p env = (Expr.select c a b).eval p env := by
  unfold mkSelectA
  split
  · rename_i h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact select_self_eval c a b h.2 (Or.inl h.1)
  · split
    · rename_i _ h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact select_self_eval c a b h.2 (Or.inr h.1)
    · split
      · rename_i c' a1 b1 _ _
        split
        · rename_i h
          simp only [Bool.and_eq_true, beq_iff_eq] at h
          obtain ⟨h1, h2⟩ := h
          subst h1
          rw [selElse_eval, select_then_eval c' a1 b1 b h2]
        · exact selElse_eval _ _ _
      · exact selElse_eval c a b

/-! ## The rewrite -/

mutual
theorem algL_good : ∀ e : Expr, Good p env (algL e) e
  | .var v => atomOf_good rfl
  | .const k => ⟨rfl, rfl⟩
  | .invalid m => atomOf_good rfl
  | .add a b => by rw [algL]; exact linAdd_good (algL_good a) (algL_good b)
  | .neg a => by rw [algL]; exact linNeg_good (algL_good a)
  | .mul a b => by rw [algL]; exact linMul_good (algL_good a) (algL_good b)
  | .lt n a b => by
      rw [algL]
      exact atomOf_good (by simp only [Expr.eval, fin_eval (algL_good a), fin_eval (algL_good b)])
  | .eq a b => by
      rw [algL]
      exact atomOf_good (by rw [mkEqA_eval]; simp only [Expr.eval, fin_eval (algL_good a), fin_eval (algL_good b)])
  | .select c a b => by
      rw [algL]
      exact atomOf_good (by
        rw [mkSelectA_eval]
        simp only [Expr.eval, fin_eval (algL_good c), fin_eval (algL_good a), fin_eval (algL_good b)])
  | .divmod q n a => by
      rw [algL]
      exact atomOf_good (by simp only [Expr.eval, fin_eval (algL_good a)])
  | .hash xs => by
      rw [algL]
      exact atomOf_good (by simp only [Expr.eval, algList_eval xs])
  | .phash h al xs => by
      rw [algL]
      exact atomOf_good (by simp only [Expr.eval, algList_eval xs])
  | .disclose e => by
      rw [algL]
      exact atomOf_good (by simp only [Expr.eval, fin_eval (algL_good e)])
theorem algList_eval : ∀ xs : List Expr, Expr.evalList p env (algList xs) = Expr.evalList p env xs
  | [] => rfl
  | x :: xs => by
      rw [algList]
      simp only [Expr.evalList, fin_eval (algL_good x), algList_eval xs]
end

end Lin

end Damp.IR.Algebra


/-! ## The generic vehicle -/

namespace Damp.IR
open Damp.Zkir (Prims Outcome)

section Vehicle
variable (f : Expr → Expr)

/-- `f` preserves evaluation exactly, failures included. -/
def EvalPreserving : Prop := ∀ (p : Prims) (env : Env) (e : Expr), (f e).eval p env = e.eval p env

variable {f}

theorem Expr.keepLeaves_eval (hf : EvalPreserving f) : EvalPreserving (Expr.keepLeaves f) := by
  intro p env e
  cases e <;> first | rfl | exact hf p env _

theorem Expr.keepLeaves_const (k : Int) : Expr.keepLeaves f (.const k) = .const k := rfl

theorem evalList_map (hf : EvalPreserving f) (p : Prims) (env : Env) :
    ∀ xs : List Expr, Expr.evalList p env (xs.map f) = Expr.evalList p env xs
  | [] => rfl
  | x :: xs => by
      simp only [List.map_cons, Expr.evalList, hf p env x, evalList_map hf p env xs]

/-- Two lists of ledger instructions that behave the same in every respect a
    ledger statement looks at. -/
structure OpsSame (ops' ops : List (Impact.Op Expr)) : Prop where
  empty : ops'.isEmpty = ops.isEmpty
  request : ∀ p env, Exec.request p env ops' = Exec.request p env ops
  groups : ∀ p env active, ledgerGroups p env active ops' = ledgerGroups p env active ops

theorem OpsSame.refl (ops : List (Impact.Op Expr)) : OpsSame ops ops := ⟨rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem OpsSame.map (hf : EvalPreserving f) (hc : ∀ k, f (.const k) = .const k)
    (ops : List (Impact.Op Expr)) : OpsSame (ops.map (·.map f)) ops where
  empty := by cases ops <;> rfl
  request p env := by
    induction ops with
    | nil => rfl
    | cons op ops ih =>
        simp only [List.map_cons, Exec.request]
        rw [Exec.Op.mapM_map f (Expr.eval p env) (Expr.eval p env) (hf p env) op, ih]
  groups p env active := by
    induction ops with
    | nil => rfl
    | cons op ops ih =>
        simp only [List.map_cons, ledgerGroups]
        rw [Op.encode_map f hc, evalList_map hf, ih]

/-- The instructions `Stmt.mapExprs` puts in a ledger statement. -/
theorem OpsSame.mapExprs (hf : EvalPreserving f) (hc : ∀ k, f (.const k) = .const k)
    (reads : List Var) (ops : List (Impact.Op Expr)) :
    OpsSame (if (IR.ledgerProblem reads (ops.map (·.map f))).isNone then ops.map (·.map f) else ops) ops := by
  split
  · exact OpsSame.map hf hc ops
  · exact OpsSame.refl ops

theorem Stmt.mapExprs_ledger (reads : List Var) (guard : Expr) (ops : List (Impact.Op Expr)) :
    Stmt.mapExprs f (.ledger guard reads ops) =
      .ledger (f guard) reads
        (if (IR.ledgerProblem reads (ops.map (·.map f))).isNone then ops.map (·.map f) else ops) := rfl

/-- A statement with its expressions rewritten runs exactly as the original. -/
theorem Stmt.mapExprs_exec (hf : EvalPreserving f) (hc : ∀ k, f (.const k) = .const k)
    (p : Prims) (s : RunState) (st : Stmt) : (st.mapExprs f).exec p s = st.exec p s := by
  cases st with
  | bind v hint e => simp only [Stmt.mapExprs, Stmt.exec, hf p]
  | assert c msg => simp only [Stmt.mapExprs, Stmt.exec, hf p]
  | constrain e r => simp only [Stmt.mapExprs, Stmt.exec, hf p]
  | witness guard name args outs shape => simp only [Stmt.mapExprs, Stmt.exec, hf p]
  | ledger guard reads ops =>
      rw [Stmt.mapExprs_ledger]
      have h := OpsSame.mapExprs hf hc reads ops
      generalize (if (IR.ledgerProblem reads (ops.map (·.map f))).isNone then ops.map (·.map f) else ops) = ops' at h
      simp only [Stmt.exec, hf p, h.empty, h.groups]

/-- The executor runs a statement with its expressions rewritten exactly as the original. -/
theorem Stmt.mapExprs_step (hf : EvalPreserving f) (hc : ∀ k, f (.const k) = .const k)
    {ω σ : Type} (p : Prims) (O : Exec.Oracles ω σ) (s : Exec.State ω σ) (st : Stmt) :
    Exec.step p O s (st.mapExprs f) = Exec.step p O s st := by
  cases st with
  | bind v hint e => simp only [Stmt.mapExprs, Exec.step, hf p]
  | assert c msg => simp only [Stmt.mapExprs, Exec.step, hf p]
  | constrain e r => simp only [Stmt.mapExprs, Exec.step, hf p]
  | witness guard name args outs shape =>
      simp only [Stmt.mapExprs, Exec.step, hf p, evalList_map hf p]
  | ledger guard reads ops =>
      rw [Stmt.mapExprs_ledger]
      have h := OpsSame.mapExprs hf hc reads ops
      generalize (if (IR.ledgerProblem reads (ops.map (·.map f))).isNone then ops.map (·.map f) else ops) = ops' at h
      simp only [Exec.step, hf p, h.empty, h.groups, h.request]

theorem execAll_mapExprs (hf : EvalPreserving f) (hc : ∀ k, f (.const k) = .const k) (p : Prims) :
    ∀ (stmts : List Stmt) (s : RunState), execAll p (stmts.map (Stmt.mapExprs f)) s = execAll p stmts s
  | [], _ => rfl
  | st :: rest, s => by
      simp only [List.map_cons, execAll, Stmt.mapExprs_exec hf hc, execAll_mapExprs hf hc p rest]

theorem steps_mapExprs (hf : EvalPreserving f) (hc : ∀ k, f (.const k) = .const k)
    {ω σ : Type} (p : Prims) (O : Exec.Oracles ω σ) :
    ∀ (stmts : List Stmt) (s : Exec.State ω σ), Exec.steps p O (stmts.map (Stmt.mapExprs f)) s = Exec.steps p O stmts s
  | [], _ => rfl
  | st :: rest, s => by
      simp only [List.map_cons, Exec.steps, Stmt.mapExprs_step hf hc, steps_mapExprs hf hc p O rest]

/-- Rewriting every expression with an evaluation-preserving function does not
    change a run at all. -/
theorem Circuit.mapExprs_run (hf : EvalPreserving f) (p : Prims) (c : Circuit) (inputs priv pub : List Fr) :
    (c.mapExprs f).run p inputs priv pub = c.run p inputs priv pub := by
  have hk := Expr.keepLeaves_eval hf
  simp only [Circuit.run, Circuit.mapExprs, Array.toList_map,
    execAll_mapExprs hk (fun k => Expr.keepLeaves_const k), evalList_map hk]

/-- Rewriting every expression with an evaluation-preserving function does not
    change what the executor does at all. -/
theorem Circuit.mapExprs_exec (hf : EvalPreserving f) {ω σ : Type} (p : Prims) (O : Exec.Oracles ω σ)
    (c : Circuit) (inputs : List Fr) (private_ : ω) (ledger : σ) :
    Exec.run p O (c.mapExprs f) inputs private_ ledger = Exec.run p O c inputs private_ ledger := by
  have hk := Expr.keepLeaves_eval hf
  simp only [Exec.run, Circuit.mapExprs, Array.toList_map,
    steps_mapExprs hk (fun k => Expr.keepLeaves_const k), evalList_map hk]

/-- The generic vehicle: rewriting every expression of a circuit with a
    function that preserves `Expr.eval` is a sound pass. -/
theorem Circuit.mapExprs_sound (hf : EvalPreserving f) : Pass.Sound (Circuit.mapExprs f) :=
  ⟨fun p c inputs priv pub => by rw [Circuit.mapExprs_run hf],
   fun p O c inputs private_ ledger => by rw [Circuit.mapExprs_exec hf]⟩

omit f in
/-- A rewritten statement has no ledger problem when the original had none. -/
theorem Stmt.mapExprs_ledgerProblem (g : Expr → Expr) (st : Stmt) (h : st.ledgerProblem = none) :
    (st.mapExprs g).ledgerProblem = none := by
  cases st with
  | ledger guard reads ops =>
      rw [Stmt.mapExprs_ledger]
      simp only [Stmt.ledgerProblem] at h ⊢
      split
      · rename_i h'
        exact Option.isNone_iff_eq_none.mp h'
      · exact h
  | _ => rfl

omit f in
theorem checkLedgerFrom_mapExprs (g : Expr → Expr) (name : String) :
    ∀ (i : Nat) (stmts : List Stmt), checkLedgerFrom name i stmts = .ok () →
      checkLedgerFrom name i (stmts.map (Stmt.mapExprs g)) = .ok ()
  | _, [], _ => rfl
  | i, st :: rest, h => by
      simp only [checkLedgerFrom] at h
      split at h
      · cases h
      · rename_i hn
        simp only [List.map_cons, checkLedgerFrom, Stmt.mapExprs_ledgerProblem g st hn]
        exact checkLedgerFrom_mapExprs g name (i + 1) rest h

omit f in
/-- Rewriting expressions keeps a circuit's ledger statements well formed,
    whatever the rewrite. -/
theorem Circuit.mapExprs_checkLedger (g : Expr → Expr) (c : Circuit) (h : c.checkLedger = .ok ()) :
    (c.mapExprs g).checkLedger = .ok () := by
  simp only [Circuit.checkLedger, Circuit.mapExprs, Array.toList_map] at h ⊢
  exact checkLedgerFrom_mapExprs _ _ 0 _ h

end Vehicle

end Damp.IR

namespace Damp.IR
open Damp.Zkir (Prims)

/-- The rewrite preserves evaluation exactly, failures included. -/
theorem Expr.alg_eval (p : Prims) (env : Env) (e : Expr) : e.alg.eval p env = e.eval p env :=
  Algebra.fin_eval (Algebra.algL_good e)

/-- The rewrite, guarded by size, preserves evaluation exactly, failures included. -/
theorem Expr.algebra_eval (p : Prims) (env : Env) (e : Expr) : e.algebra.eval p env = e.eval p env := by
  simp only [Expr.algebra]
  split
  · exact Expr.alg_eval p env e
  · rfl

/-- `Circuit.algebra` is sound: for every circuit and input it changes neither
    what a run produces nor what the executor does. -/
theorem Circuit.algebra_sound : Pass.Sound Circuit.algebra :=
  Circuit.mapExprs_sound Expr.algebra_eval

/-- `Circuit.algebra` keeps a circuit's ledger statements well formed. -/
theorem Circuit.algebra_checkLedger (c : Circuit) (h : c.checkLedger = .ok ()) :
    (Circuit.algebra c).checkLedger = .ok () :=
  Circuit.mapExprs_checkLedger Expr.algebra c h

end Damp.IR
