/-
Composite values: tuples, structures, `Maybe`, and `select` and `==.` on every `Value` type.

A value of any `Value` type means the list of field elements its expressions evaluate to
(`Value.Is`, `Args.lean`). For types whose `ofExprs` and `toExprs` agree
(`Value.RoundTrip`, proved for every instance of `Contract.lean` and, per declaration,
for `struct`s: see `Examples/InterfaceMore.lean`), building a value from its parts and
reading the parts back keeps their meaning, `select` picks by its condition, and `==.`
compares all elements.
-/
import Damp.Proofs.Interface.Control

namespace Damp
open IR

variable {p : Zkir.Prims} {env : Env}

/-! ## Lists of expressions -/

/-- Evaluation keeps the length. -/
theorem evalList_length : ∀ {es : List Expr} {xs : List Fr}, Expr.evalList p env es = some xs → xs.length = es.length
  | [], xs, h => by simp [Expr.evalList] at h; subst h; rfl
  | e :: es, xs, h => by
    obtain ⟨x, xs', _, hes, rfl⟩ := evalList_cons.1 h
    simp [evalList_length hes]

/-- Evaluating a concatenation. -/
theorem evalList_append_some {a b : List Expr} {xs ys : List Fr} (ha : Expr.evalList p env a = some xs)
    (hb : Expr.evalList p env b = some ys) : Expr.evalList p env (a ++ b) = some (xs ++ ys) := by
  rw [evalList_append, ha, hb]; rfl

/-- Splitting the value of a concatenation. -/
theorem evalList_append_inv {a b : List Expr} {zs : List Fr} (h : Expr.evalList p env (a ++ b) = some zs) :
    ∃ xs ys, zs = xs ++ ys ∧ Expr.evalList p env a = some xs ∧ Expr.evalList p env b = some ys := by
  rw [evalList_append] at h
  cases ha : Expr.evalList p env a <;> cases hb : Expr.evalList p env b <;> simp [ha, hb] at h
  exact ⟨_, _, h.symm, rfl, rfl⟩

/-- Element-wise `select` of two lists evaluates to one of them. -/
theorem evalList_zipWith_sel {c : Expr} {u : Bool} (hc : c.eval p env = some (Fr.ofBool u)) :
    ∀ (as bs : List Expr) (xs ys : List Fr), as.length = bs.length →
    Expr.evalList p env as = some xs → Expr.evalList p env bs = some ys →
    Expr.evalList p env (List.zipWith (Expr.sel c) as bs) = some (if u then xs else ys)
  | [], [], xs, ys, _, ha, hb => by
    simp [Expr.evalList] at ha hb; subst ha hb; cases u <;> rfl
  | a :: as, b :: bs, xs, ys, hl, ha, hb => by
    obtain ⟨x, xs', hx, hxs, rfl⟩ := evalList_cons.1 ha
    obtain ⟨y, ys', hy, hys, rfl⟩ := evalList_cons.1 hb
    have ih := evalList_zipWith_sel hc as bs xs' ys' (by simpa using hl) hxs hys
    simp only [List.zipWith_cons_cons, Expr.evalList, Expr.eval_sel' hc hx hy, ih]
    cases u <;> rfl
  | [], _ :: _, _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, _, hl, _, _ => by simp at hl

/-! ## Reading a value back -/

/-- A value of a type that round-trips, flattened and read back, means what it meant. -/
theorem Value.ofExprs_toExprs_is {α : Type} [Value α] (h : Value.RoundTrip α) {a : α} {xs : List Fr}
    (hl : (Value.toExprs a).length = Value.width α) :
    Value.Is p env (Value.ofExprs (Value.toExprs a) : α) xs ↔ Value.Is p env a xs := by
  unfold Value.Is; rw [h _ hl p env]

/-! ## `select` on every type -/

/-- **`select` on any `Value` type** picks by its condition, elementwise, given both sides have
    the type's width. -/
theorem select_is {α : Type} [Value α] (h : Value.RoundTrip α) {c : Boolean} {u : Bool} {a b : α}
    {xs ys : List Fr} (hc : Boolean.Is p env c u)
    (hla : (Value.toExprs a).length = Value.width α) (hlb : (Value.toExprs b).length = Value.width α)
    (ha : Value.Is p env a xs) (hb : Value.Is p env b ys) :
    Value.Is p env (select c a b) (if u then xs else ys) := by
  unfold Value.Is select
  rw [h _ (by simp [List.length_zipWith, hla, hlb]) p env]
  exact evalList_zipWith_sel hc _ _ _ _ (hla.trans hlb.symm) ha hb

/-! ## Tuples -/

theorem Value.toExprs_prod {α β : Type} [Value α] [Value β] (a : α) (b : β) :
    Value.toExprs (a, b) = Value.toExprs a ++ Value.toExprs b := rfl

/-- A pair means its parts' meanings, concatenated. -/
theorem prod_is {α β : Type} [Value α] [Value β] {a : α} {b : β} {xs ys : List Fr}
    (ha : Value.Is p env a xs) (hb : Value.Is p env b ys) : Value.Is p env (a, b) (xs ++ ys) :=
  evalList_append_some ha hb

/-- The parts of a pair that means `zs`. -/
theorem prod_is_inv {α β : Type} [Value α] [Value β] {a : α} {b : β} {zs : List Fr}
    (h : Value.Is p env (a, b) zs) : ∃ xs ys, zs = xs ++ ys ∧ Value.Is p env a xs ∧ Value.Is p env b ys :=
  evalList_append_inv h

/-- Reading a pair off a list: the first component takes the first `width α` elements. -/
theorem Value.ofExprs_prod {α β : Type} [Value α] [Value β] (es : List Expr) :
    (Value.ofExprs es : α × β) = (Value.ofExprs (es.take (Value.width α)), Value.ofExprs (es.drop (Value.width α))) :=
  rfl

/-- The components of a pair read off a list of the right length mean the corresponding parts. -/
theorem prod_ofExprs_is {α β : Type} [Value α] [Value β] (hα : Value.RoundTrip α) (hβ : Value.RoundTrip β)
    {es : List Expr} {xs : List Fr} (hl : es.length = Value.width α + Value.width β)
    (h : Expr.evalList p env es = some xs) :
    Value.Is p env (Value.ofExprs es : α × β).1 (xs.take (Value.width α)) ∧
    Value.Is p env (Value.ofExprs es : α × β).2 (xs.drop (Value.width α)) := by
  rw [← List.take_append_drop (Value.width α) es] at h
  obtain ⟨xs₁, ys₁, rfl, h1, h2⟩ := evalList_append_inv h
  have hl1 : xs₁.length = Value.width α := by rw [evalList_length h1]; simp; omega
  refine ⟨?_, ?_⟩
  · unfold Value.Is; rw [Value.ofExprs_prod]
    rw [hα _ (by simp; omega) p env, h1, List.take_left' hl1]
  · unfold Value.Is; rw [Value.ofExprs_prod]
    rw [hβ _ (by simp; omega) p env, h2, List.drop_left' hl1]

/-! ## `Maybe` -/

theorem Value.toExprs_maybe {α : Type} [Value α] (m : Maybe α) :
    Value.toExprs m = m.isSome.expr :: Value.toExprs m.value := rfl

/-- A `Maybe` means its flag followed by its value. -/
theorem maybe_is {α : Type} [Value α] {m : Maybe α} {u : Bool} {xs : List Fr}
    (hf : Boolean.Is p env m.isSome u) (hv : Value.Is p env m.value xs) :
    Value.Is p env m (Fr.ofBool u :: xs) := by
  unfold Value.Is Boolean.Is at *; simp [Value.toExprs_maybe, Expr.evalList, hf, hv]

/-- And conversely: the flag and the value of a `Maybe` that means `x :: xs`. -/
theorem maybe_is_inv {α : Type} [Value α] {m : Maybe α} {x : Fr} {xs : List Fr}
    (h : Value.Is p env m (x :: xs)) : m.isSome.expr.eval p env = some x ∧ Value.Is p env m.value xs := by
  unfold Value.Is at h; rw [Value.toExprs_maybe] at h
  obtain ⟨y, ys, hy, hys, hh⟩ := evalList_cons.1 h
  simp only [List.cons.injEq] at hh; obtain ⟨rfl, rfl⟩ := hh
  exact ⟨hy, hys⟩

/-- `Maybe.some x` is present and holds `x`. -/
theorem Maybe.some_is {α : Type} [Value α] {x : α} {xs : List Fr} (hx : Value.Is p env x xs) :
    Value.Is p env (Maybe.some x) (Fr.ofBool true :: xs) := maybe_is Boolean.true_is hx

theorem Maybe.some_isSome {α : Type} [Value α] (x : α) : Boolean.Is p env (Maybe.some x).isSome true :=
  Boolean.true_is

theorem Maybe.some_value {α : Type} [Value α] (x : α) : (Maybe.some x).value = x := rfl

/-- The all-zero value of a type that round-trips means a list of zeros. -/
theorem Value.zero_is {α : Type} [Value α] (h : Value.RoundTrip α) :
    Value.Is p env (Value.zero α) (List.replicate (Value.width α) 0) := by
  unfold Value.Is Value.zero
  rw [h _ (by simp; rfl) p env]
  show Expr.evalList p env (List.replicate (Value.width α) (.const 0)) = _
  generalize Value.width α = n
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, Expr.evalList, ih]; rfl

/-- `Maybe.none` is absent, and its value is all zeros (Compact's `default`). -/
theorem Maybe.none_is {α : Type} [Value α] (h : Value.RoundTrip α) :
    Value.Is p env (Maybe.none : Maybe α) (Fr.ofBool false :: List.replicate (Value.width α) 0) :=
  maybe_is Boolean.false_is (Value.zero_is h)

theorem Maybe.none_isSome {α : Type} [Value α] : Boolean.Is p env (Maybe.none : Maybe α).isSome false :=
  Boolean.false_is

/-- Reading a `Maybe` off a list: the flag is the first element, the value the rest. -/
theorem Value.ofExprs_maybe {α : Type} [Value α] (e : Expr) (es : List Expr) :
    (Value.ofExprs (e :: es) : Maybe α) = ⟨⟨e⟩, Value.ofExprs es⟩ := rfl

/-! ## Equality of whole values (`==.` on tuples, structures, `Maybe`, vectors, `Bytes`) -/

/-- `valueEq` on any type: all elements equal, given both sides have the type's width. -/
theorem valueEq_means {α : Type} [Value α] {a b : α} {xs ys : List Fr}
    (hla : (Value.toExprs a).length = Value.width α) (hlb : (Value.toExprs b).length = Value.width α)
    (ha : Value.Is p env a xs) (hb : Value.Is p env b ys) :
    Boolean.Is p env (valueEq a b) (decide (xs = ys)) :=
  valueEq_is ha hb (by rw [evalList_length ha, evalList_length hb, hla, hlb])

/-- Two `Maybe`s are equal when the flags and the values are (including the zero padding of an
    absent value). -/
theorem cmpEq_maybe {α : Type} [Value α] {a b : Maybe α} {u v : Bool} {xs ys : List Fr}
    (hla : (Value.toExprs a.value).length = Value.width α) (hlb : (Value.toExprs b.value).length = Value.width α)
    (hfa : Boolean.Is p env a.isSome u) (hfb : Boolean.Is p env b.isSome v)
    (ha : Value.Is p env a.value xs) (hb : Value.Is p env b.value ys) :
    Boolean.Is p env (cmpEq a b) (decide (u = v ∧ xs = ys)) := by
  have := valueEq_is (maybe_is hfa ha) (maybe_is hfb hb)
    (by simp [evalList_length ha, evalList_length hb, hla, hlb])
  simp only [List.cons.injEq, Fr.ofBool_inj] at this
  exact this

/-- Pairs are equal when both components are. -/
theorem cmpEq_prod {α β : Type} [Value α] [Value β] {a a' : α} {b b' : β} {xs xs' ys ys' : List Fr}
    (hla : (Value.toExprs a).length = Value.width α) (hla' : (Value.toExprs a').length = Value.width α)
    (hlb : (Value.toExprs b).length = Value.width β) (hlb' : (Value.toExprs b').length = Value.width β)
    (ha : Value.Is p env a xs) (ha' : Value.Is p env a' xs')
    (hb : Value.Is p env b ys) (hb' : Value.Is p env b' ys') :
    Boolean.Is p env (cmpEq (a, b) (a', b')) (decide (xs = xs' ∧ ys = ys')) := by
  have hx : xs.length = xs'.length := by rw [evalList_length ha, evalList_length ha', hla, hla']
  have hy : ys.length = ys'.length := by rw [evalList_length hb, evalList_length hb', hlb, hlb']
  have h := valueEq_is (prod_is ha hb) (prod_is ha' hb') (by simp [hx, hy])
  have e : decide (xs ++ ys = xs' ++ ys') = decide (xs = xs' ∧ ys = ys') :=
    decide_eq_decide.mpr ⟨fun h => List.append_inj h hx, fun ⟨h1, h2⟩ => h1 ▸ h2 ▸ rfl⟩
  rw [e] at h; exact h

end Damp
