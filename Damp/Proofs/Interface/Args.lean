/-
Circuit arguments at every position and of every shape.

`mkCircuit name names f` allocates one input variable per field element of
each argument, in argument order, numbered from 0, and applies `f` to the
values `Value.ofExprs` reads off those variables. `CircuitFnSpec` states this
once for every circuit function: it is proved for `CircuitM ρ` and for
`α → φ` from the statement for `φ`, following the instance chain of
`CircuitFn`, so it holds for any number of arguments of any `Value` type
(structures, tuples, vectors, `Maybe`, `Bytes`, …).

The main theorem, `mkCircuit_run`, says what running the built circuit means:
it rejects when the number of inputs is wrong or some input fails the range
check of its position (`rangesHold`), and otherwise it is the run of the
statements `f` builds when applied to the decoded arguments
(`CircuitFnSpec.apply f (argVars N)`), with input variable `v` holding the
`v`-th input. `Value.RoundTrip` then says the argument `f` receives means the
inputs at its position.
-/
import Damp.Proofs.Interface

namespace Damp
open IR

/-! ## Allocating inputs -/

/-- Allocating one input per range numbers them from the next free variable. -/
theorem allocInputs_run (name : String) : ∀ (rs : List (Option Range)) (s : Build),
    (rs.mapM fun range => do
        let v ← freshVar
        pure ({ name, var := v, range } : Input) : CircuitM (List Input)).run s =
      (((List.range' s.next rs.length).zip rs).map fun (v, r) => { name, var := v, range := r },
       { s with next := s.next + rs.length })
  | [], s => rfl
  | r :: rs, s => by
    rw [List.mapM_cons, CircuitM.bind_run]
    have h1 : ((do let v ← freshVar; pure ({ name, var := v, range := r } : Input)) : CircuitM Input).run s
        = ({ name, var := s.next, range := r }, { s with next := s.next + 1 }) := rfl
    rw [h1]; dsimp only
    rw [CircuitM.bind_run, allocInputs_run name rs]
    simp [CircuitM.pure_run, List.range'_succ, Nat.add_assoc, Nat.add_comm 1]

/-- One step of `checkUintBounds`. -/
def checkUintBound1 : Ty → CircuitM Unit
  | .uint m => unless m ≤ Uint.maxBound do buildError (Uint.tooLarge m)
  | _ => pure ()

theorem checkUintBounds_cons (t : Ty) (ts : List Ty) :
    checkUintBounds (t :: ts) = (checkUintBound1 t >>= fun _ => checkUintBounds ts) := by
  cases t <;> rfl

/-- `checkUintBounds` only records errors. -/
theorem checkUintBounds_run : ∀ (tys : List Ty) (s : Build),
    ((checkUintBounds tys).run s).2 = { s with errors := ((checkUintBounds tys).run s).2.errors }
  | [], s => rfl
  | t :: ts, s => by
    rw [checkUintBounds_cons, CircuitM.bind_run]
    have hq : ((checkUintBound1 t).run s).2 = { s with errors := ((checkUintBound1 t).run s).2.errors } := by
      cases t with
      | uint m => by_cases h : m ≤ Uint.maxBound <;> simp [checkUintBound1, h] <;> rfl
      | _ => rfl
    generalize (checkUintBound1 t).run s = q at hq
    rw [checkUintBounds_run ts q.2, hq]

/-! ## The specification of `CircuitFn.build` -/

/-- The variables `k, k+1, …, k+n-1` as expressions. -/
def argVars (k n : Nat) : List Expr := (List.range' k n).map Expr.var

/-- What building a circuit function from state `s` produces, when its inputs have the
    ranges `rs` and its body, applied to the input variables, is `body`: the inputs are the
    next `rs.length` variables with those ranges; the statements, the counter and the guard
    are those of `body` run with the variables allocated; the outputs are its result's. -/
structure BuildsAs (rs : List (Option Range)) {ρ : Type} [Value ρ] (body : CircuitM ρ)
    (s : Build) (q : Signature × Build) : Prop where
  inputs : q.1.inputs.map (fun i => (i.var, i.range)) = (List.range' s.next rs.length).zip rs
  outputs : q.1.outputs = Value.toExprs (body.run { s with next := s.next + rs.length }).1
  result : q.1.result = Value.shape ρ
  state : q.2 = { (body.run { s with next := s.next + rs.length }).2 with errors := q.2.errors }

/-- `CircuitFn.build`, specified uniformly in the arguments: `apply f xs` feeds the flat list
    of argument expressions `xs` to `f`, one `Value.ofExprs` per argument. -/
class CircuitFnSpec (φ : Type) [CircuitFn φ] where
  /-- The result type of the circuit. -/
  Res : Type
  [resValue : Value Res]
  /-- The range checks of all inputs, in order. -/
  ranges : List (Option Range)
  /-- Apply the function to arguments read off a flat list of expressions. -/
  apply : φ → List Expr → CircuitM Res
  build_run : ∀ (f : φ) (names : List String) (s : Build),
    BuildsAs ranges (apply f (argVars s.next ranges.length)) s ((CircuitFn.build f names).run s)

set_option warn.classDefReducibility false in
attribute [instance] CircuitFnSpec.resValue

instance CircuitFnSpec.result {ρ : Type} [Value ρ] : CircuitFnSpec (CircuitM ρ) where
  Res := ρ
  ranges := []
  apply m _ := m
  build_run m names s := by
    have hs : ({ s with next := s.next + ([] : List (Option Range)).length } : Build) = s := rfl
    refine ⟨rfl, ?_, rfl, ?_⟩ <;> rw [hs] <;> rfl

theorem argVars_take {k a b : Nat} : (argVars k (a + b)).take a = argVars k a := by
  rw [argVars, ← List.map_take, ← List.range'_append_1, List.take_left' (by simp)]; rfl

theorem argVars_drop {k a b : Nat} : (argVars k (a + b)).drop a = argVars (k + a) b := by
  rw [argVars, ← List.map_drop, ← List.range'_append_1, List.drop_left' (by simp)]; rfl

theorem map_zip_fst {β γ : Type} (g : Nat → γ) : ∀ (l : List Nat) (rs : List β), l.length = rs.length →
    ((l.zip rs).map fun x => g x.1) = l.map g
  | [], _, _ => rfl
  | _ :: _, [], h => by simp at h
  | a :: l, r :: rs, h => by simp [map_zip_fst g l rs (by simpa using h)]

theorem insVars (name : String) (k : Nat) (rs : List (Option Range)) :
    ((((List.range' k rs.length).zip rs).map fun (x : Nat × Option Range) => ({ name, var := x.1, range := x.2 } : Input)).map
      fun i => Expr.var i.var) = argVars k rs.length := by
  rw [List.map_map]; exact map_zip_fst Expr.var _ _ (by simp)

theorem insPairs (name : String) (k : Nat) (rs : List (Option Range)) :
    ((((List.range' k rs.length).zip rs).map fun (x : Nat × Option Range) => ({ name, var := x.1, range := x.2 } : Input)).map
      fun i => (i.var, i.range)) = (List.range' k rs.length).zip rs := by
  rw [List.map_map]; exact List.map_id'' (fun _ => rfl) _

theorem CircuitFnSpec.arrow_build_run {α φ : Type} [Value α] [CircuitFn φ] [CircuitFnSpec φ] (f : α → φ) (names : List String) (s : Build) :
    BuildsAs (Value.ranges α ++ CircuitFnSpec.ranges φ) (CircuitFnSpec.apply (f (Value.ofExprs ((argVars s.next (Value.ranges α ++ CircuitFnSpec.ranges φ).length).take (Value.width α)))) ((argVars s.next (Value.ranges α ++ CircuitFnSpec.ranges φ).length).drop (Value.width α)))
      s ((CircuitFn.build f names).run s) := by
  simp only [CircuitFn.build]
  rw [CircuitM.bind_run, allocInputs_run]
  dsimp only
  rw [CircuitM.bind_run, CircuitM.bind_run, CircuitM.pure_run, insVars]
  have hw : Value.width α = (Value.ranges α).length := rfl
  rw [hw]
  generalize hs1 : ({ s with next := s.next + (Value.ranges α).length } : Build) = s1
  have ih := CircuitFnSpec.build_run (f (Value.ofExprs (argVars s.next (Value.ranges α).length))) names.tail s1
  have hn : s1.next = s.next + (Value.ranges α).length := by rw [← hs1]
  rw [hn] at ih
  generalize (CircuitFn.build (f (Value.ofExprs (argVars s.next (Value.ranges α).length))) names.tail).run s1 = q at ih
  obtain ⟨hi, ho, hr, hst⟩ := ih
  rw [hn] at hi ho hst
  have hs1' : ({ s1 with next := s.next + (Value.ranges α).length + (CircuitFnSpec.ranges φ).length } : Build) = { s with next := s.next + (Value.ranges α ++ CircuitFnSpec.ranges φ).length } := by
    rw [← hs1, List.length_append, Nat.add_assoc]
  rw [hs1'] at ho hst
  rw [List.length_append, argVars_take, argVars_drop]
  refine ⟨?_, ho, hr, ?_⟩
  · simp only [List.map_append, insPairs, hi, List.length_append]
    rw [← List.range'_append_1, List.zip_append (by simp)]
  · rw [checkUintBounds_run, hst]

instance CircuitFnSpec.arrow {α φ : Type} [Value α] [CircuitFn φ] [CircuitFnSpec φ] :
    CircuitFnSpec (α → φ) where
  Res := CircuitFnSpec.Res φ
  ranges := Value.ranges α ++ CircuitFnSpec.ranges φ
  apply f xs := CircuitFnSpec.apply (f (Value.ofExprs (xs.take (Value.width α)))) (xs.drop (Value.width α))
  build_run f names s := CircuitFnSpec.arrow_build_run f names s


/-! ## Running the circuit -/

section Run
variable {p : Zkir.Prims}
/-- Whether each input passes the range check of its position (an unchecked position passes). -/
def rangesHold (rs : List (Option Range)) (xs : List Fr) : Bool :=
  (rs.zip xs).all fun (r, x) => r.all (·.holds x)

/-- Binding inputs to consecutive variables. -/
theorem bindInputs_consecutive : ∀ (ins : List Input) (k : Nat) (env : Env) (xs : List Fr),
    ins.map (·.var) = List.range' k ins.length →
    bindInputs env ins xs = if xs.length = ins.length then
      some (fun v => if k ≤ v ∧ v < k + ins.length then xs.getD (v - k) 0 else env v) else none
  | [], k, env, [], _ => by simp only [bindInputs]; simp; funext v; split <;> first | omega | rfl
  | [], k, env, _ :: _, _ => by simp [bindInputs]
  | _ :: _, k, env, [], _ => by simp [bindInputs]
  | i :: ins, k, env, x :: xs, h => by
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at h
    simp only [bindInputs, List.length_cons, Nat.add_right_cancel_iff]
    rw [bindInputs_consecutive ins (k + 1) _ xs h.2]
    split
    · congr 1; funext v
      simp only [Env.set, h.1]
      by_cases hv : v = k
      · subst hv; simp; intro h; omega
      · by_cases h1 : k + 1 ≤ v ∧ v < k + 1 + ins.length
        · have h2 : k ≤ v ∧ v < k + (ins.length + 1) := by omega
          simp only [h1, h2, and_self, ↓reduceIte]
          obtain ⟨j, rfl⟩ : ∃ j, v = k + 1 + j := ⟨v - (k + 1), by omega⟩
          simp [show k + 1 + j - k = j + 1 by omega, show k + 1 + j - (k + 1) = j by omega]
        · have h2 : ¬ (k ≤ v ∧ v < k + (ins.length + 1)) := by omega
          simp [h1, h2, hv]
    · rfl

/-- Executing the input checks: they pass, changing nothing, exactly when every checked input is in range. -/
theorem execAll_inputChecks_eq : ∀ (ins : List Input) (st : RunState),
    execAll p (inputChecks ins) st =
      if ins.all (fun i => i.range.all (·.holds (st.env i.var))) then some st else none
  | [], st => rfl
  | i :: ins, st => by
    cases hr : i.range with
    | none =>
      have : inputChecks (i :: ins) = inputChecks ins := by simp [inputChecks, hr]
      rw [this, execAll_inputChecks_eq ins st]; simp [hr]
    | some r =>
      have : inputChecks (i :: ins) = Stmt.constrain (.var i.var) r :: inputChecks ins := by
        simp [inputChecks, hr]
      rw [this]
      simp only [execAll, exec_constrain r (show (Expr.var i.var).eval p st.env = some (st.env i.var) from rfl)]
      by_cases hx : r.holds (st.env i.var) = true
      · simp [hx, execAll_inputChecks_eq ins st, hr]
      · simp [hx, hr]

theorem all_zip_range' (env : Env) : ∀ (k : Nat) (rs : List (Option Range)) (xs : List Fr),
    xs.length = rs.length → (∀ j (hj : j < xs.length), env (k + j) = xs[j]) →
    (((List.range' k rs.length).zip rs).all fun (vr : Nat × Option Range) => vr.2.all (·.holds (env vr.1)))
      = rangesHold rs xs
  | _, [], [], _, _ => rfl
  | _, [], _ :: _, h, _ => by simp at h
  | _, _ :: _, [], h, _ => by simp at h
  | k, r :: rs, x :: xs, hl, he => by
    simp only [List.length_cons, List.range'_succ, List.zip_cons_cons, List.all_cons, rangesHold] at *
    have h0 : env k = x := by simpa using he 0 (by simp)
    rw [h0, all_zip_range' env (k + 1) rs xs (by omega) fun j hj => by
      have := he (j + 1) (by simp; omega); simpa [Nat.add_assoc, Nat.add_comm 1] using this]
    rfl

/-- The rest of a run once the inputs are bound: execute the statements, read the outputs,
    and require both transcripts to be used up (the tail of `Circuit.run`). -/
def runBody (p : Zkir.Prims) (stmts : List Stmt) (outs : List Expr) (env : Env) (priv pub : List Fr) :
    Option Zkir.Outcome := do
  let s ← execAll p stmts { env, priv, pub }
  let outputs ← Expr.evalList p s.env outs
  if s.priv.isEmpty && s.pub.isEmpty then pure { outputs, groups := s.groups } else none

theorem mkCircuit_run {φ : Type} [CircuitFn φ] [CircuitFnSpec φ] (name : String) (names : List String) (f : φ)
    (xs priv pub : List Fr) :
    (mkCircuit name names f).run p xs priv pub =
      if xs.length = (CircuitFnSpec.ranges φ).length ∧ rangesHold (CircuitFnSpec.ranges φ) xs = true then
        let r := (CircuitFnSpec.apply f (argVars 0 (CircuitFnSpec.ranges φ).length)).run
          { next := (CircuitFnSpec.ranges φ).length }
        runBody p r.2.stmts.toList (Value.toExprs r.1) (fun v => xs.getD v 0) priv pub
      else none := by
  have hb := CircuitFnSpec.build_run f names {}
  unfold mkCircuit
  generalize (CircuitFn.build f names).run {} = q at hb
  obtain ⟨sig, st⟩ := q
  obtain ⟨hi, ho, -, hst⟩ := hb
  have h0 : ({ ({} : Build) with next := ({} : Build).next + (CircuitFnSpec.ranges φ).length } : Build)
      = { next := (CircuitFnSpec.ranges φ).length } := by simp
  rw [h0] at ho hst
  simp only at hi ho hst ⊢
  generalize (CircuitFnSpec.apply f (argVars 0 (CircuitFnSpec.ranges φ).length)).run
    { next := (CircuitFnSpec.ranges φ).length } = r at ho hst
  generalize hrs : CircuitFnSpec.ranges φ = rs at hi ho hst
  have hlen : sig.inputs.length = rs.length := by
    have := congrArg List.length hi; simpa using this
  have hvars : sig.inputs.map (·.var) = List.range' 0 sig.inputs.length := by
    have := congrArg (List.map Prod.fst) hi
    rw [List.map_map, List.map_fst_zip (by simp)] at this
    rw [hlen]; exact this
  simp only [Circuit.run]
  rw [bindInputs_consecutive _ 0 _ xs hvars, hlen]
  by_cases hx : xs.length = rs.length
  · have henv : (fun v => if 0 ≤ v ∧ v < 0 + rs.length then xs.getD (v - 0) 0 else (fun _ => (0 : Fr)) v)
        = fun v => xs.getD v 0 := by
      funext v; split
      · simp
      · rename_i h; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show xs.length ≤ v by omega)]
    simp only [hx, ↓reduceIte, henv, Array.toList_append]
    change (execAll p (inputChecks sig.inputs ++ st.stmts.toList) { env := fun v => xs.getD v 0, priv, pub }).bind _ = _
    rw [execAll_append, execAll_inputChecks_eq]
    simp only
    have hall : (sig.inputs.all fun i => i.range.all (·.holds (xs.getD i.var 0))) = rangesHold rs xs := by
      have := congrArg (List.all · fun (vr : Nat × Option Range) => vr.2.all (·.holds (xs.getD vr.1 0))) hi
      simp only [List.all_map] at this
      rw [← all_zip_range' (fun v => xs.getD v 0) 0 rs xs hx (fun j hj => by simp [hj])]
      exact this
    rw [hall]
    by_cases hh : rangesHold rs xs = true
    · have hstm : st.stmts = r.2.stmts := (congrArg Build.stmts hst :)
      simp only [hh, ↓reduceIte, true_and, runBody, hstm, ho]
      rfl
    · simp [hh]
  · simp [hx]

end Run

/-! ## Widths of composite values -/

theorem Shape.tysList_eq : ∀ ss : List Shape, Shape.tysList ss = ss.flatMap Shape.tys
  | [] => rfl
  | s :: ss => by simp [Shape.tysList, Shape.tysList_eq ss]
theorem Shape.ranges_tuple (ss : List Shape) : (Shape.tuple ss).ranges = ss.flatMap Shape.ranges := by
  simp [Shape.ranges, Shape.tys, Shape.tysList_eq, List.flatMap_assoc]; rfl
theorem Shape.ranges_struct (n : String) (fs : List String) (ss : List Shape) :
    (Shape.struct n fs ss).ranges = ss.flatMap Shape.ranges := by
  simp [Shape.ranges, Shape.tys, Shape.tysList_eq, List.flatMap_assoc]; rfl
theorem Shape.ranges_vector (n : Nat) (e : Shape) :
    (Shape.vector n e).ranges = (List.replicate n e.ranges).flatten := by
  simp only [Shape.ranges, Shape.tys]
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, List.flatMap_append, ih]
theorem Shape.ranges_prim (t : Ty) : (Shape.prim t).ranges = t.ranges := by
  simp [Shape.ranges, Shape.tys]
theorem Value.width_prod {α β} [Value α] [Value β] : Value.width (α × β) = Value.width α + Value.width β := by
  simp [Value.width, Value.ranges, Value.shape, Shape.ranges_tuple]
theorem Value.width_maybe {α} [Value α] : Value.width (Maybe α) = 1 + Value.width α := by
  simp [Value.width, Value.ranges, Value.shape, Shape.ranges_struct, Shape.ranges_prim, Ty.ranges]; omega
theorem Value.width_vector {α} [Value α] {n} : Value.width (Vector α n) = n * Value.width α := by
  simp [Value.width, Value.ranges, Value.shape, Shape.ranges_vector]
theorem Value.width_bytes {n} : Value.width (Bytes n) = byteLimbs n := by
  simp [Value.width, Value.ranges, Value.shape, Shape.ranges_prim, Ty.ranges]
/-- Two lists of expressions mean the same, everywhere. -/
def ExprsEquiv (es fs : List Expr) : Prop := ∀ p env, Expr.evalList p env es = Expr.evalList p env fs

theorem evalList_append (p : Zkir.Prims) (env : Env) : ∀ (a b : List Expr),
    Expr.evalList p env (a ++ b) = (do let x ← Expr.evalList p env a; let y ← Expr.evalList p env b; pure (x ++ y))
  | [], b => by simp [Expr.evalList]
  | e :: a, b => by
    simp only [List.cons_append, Expr.evalList, evalList_append p env a b]
    cases e.eval p env <;> cases Expr.evalList p env a <;> cases Expr.evalList p env b <;> rfl

theorem ExprsEquiv.refl (es : List Expr) : ExprsEquiv es es := fun _ _ => rfl
theorem ExprsEquiv.append {a b c d : List Expr} (h1 : ExprsEquiv a c) (h2 : ExprsEquiv b d) :
    ExprsEquiv (a ++ b) (c ++ d) := fun p env => by rw [evalList_append, evalList_append, h1, h2]

theorem ExprsEquiv.flatten_ofFn : ∀ {n : Nat} (F G : Fin n → List Expr), (∀ i, ExprsEquiv (F i) (G i)) →
    ExprsEquiv (List.ofFn F).flatten (List.ofFn G).flatten
  | 0, _, _, _ => ExprsEquiv.refl _
  | n + 1, F, G, h => by
    rw [List.ofFn_succ, List.ofFn_succ, List.flatten_cons, List.flatten_cons]
    exact (h 0).append (ExprsEquiv.flatten_ofFn _ _ fun i => h i.succ)

theorem flatten_chunks {β : Type} (w : Nat) : ∀ (n : Nat) (es : List β), es.length = n * w →
    (List.ofFn fun (i : Fin n) => (es.drop (i.val * w)).take w).flatten = es
  | 0, es, h => by simp at h; simp [h]
  | n + 1, es, h => by
    rw [List.ofFn_succ, List.flatten_cons]
    have ih := flatten_chunks w n (es.drop w) (by simp [h, Nat.succ_mul])
    simp only [Fin.val_zero, Nat.zero_mul, List.drop_zero, Fin.val_succ]
    have : ∀ i : Fin n, (es.drop ((i.val + 1) * w)).take w = ((es.drop w).drop (i.val * w)).take w := by
      intro i; rw [List.drop_drop, Nat.succ_mul, Nat.add_comm]
    simp only [this, ih, List.take_append_drop]
/-- Reading a value off a list of the right length and flattening it again keeps the meaning
    of every element. -/
def Value.RoundTrip (α : Type) [Value α] : Prop :=
  ∀ es : List Expr, es.length = Value.width α → ExprsEquiv (Value.toExprs (Value.ofExprs es : α)) es

theorem Value.width_field : Value.width Field = 1 := rfl
theorem Value.width_boolean : Value.width Boolean = 1 := rfl
theorem Value.width_uint {m : Nat} : Value.width (Uint m) = 1 := by
  simp [Value.width, Value.ranges, Value.shape, Shape.ranges_prim, ranges_uint]
theorem Value.width_unit : Value.width Unit = 0 := rfl

theorem single_of_length {β : Type} {es : List β} (h : es.length = 1) : ∃ e, es = [e] := by
  match es, h with
  | [e], _ => exact ⟨e, rfl⟩

theorem roundTrip_field : Value.RoundTrip Field := fun es h => by
  obtain ⟨e, rfl⟩ := single_of_length h; exact ExprsEquiv.refl _
theorem roundTrip_boolean : Value.RoundTrip Boolean := fun es h => by
  obtain ⟨e, rfl⟩ := single_of_length h; exact ExprsEquiv.refl _
theorem roundTrip_unit : Value.RoundTrip Unit := fun es h => by
  match es, h with | [], _ => exact ExprsEquiv.refl _
theorem roundTrip_uint {m : Nat} (hm : m ≤ Uint.maxBound) : Value.RoundTrip (Uint m) := fun es h => by
  obtain ⟨e, rfl⟩ := single_of_length (h.trans Value.width_uint)
  intro p env
  show Expr.evalList p env [Uint.capped m e] = _
  simp [Expr.evalList, Uint.capped_eval hm]
theorem roundTrip_bytes {n : Nat} : Value.RoundTrip (Bytes n) := fun es h => by
  rw [Value.width_bytes] at h
  show ExprsEquiv (es.take (byteLimbs n)) es
  rw [← h, List.take_length]; exact ExprsEquiv.refl _

theorem Value.take_eq {α : Type} [Value α] (es : List Expr) :
    Value.take α es = (Value.ofExprs (es.take (Value.width α)), es.drop (Value.width α)) := rfl

theorem roundTrip_prod {α β : Type} [Value α] [Value β] (ha : Value.RoundTrip α) (hb : Value.RoundTrip β) :
    Value.RoundTrip (α × β) := fun es h => by
  rw [Value.width_prod] at h
  show ExprsEquiv (Value.toExprs (Value.ofExprs (es.take (Value.width α)) : α) ++
    Value.toExprs (Value.ofExprs (es.drop (Value.width α)) : β)) es
  conv => rhs; rw [← List.take_append_drop (Value.width α) es]
  exact (ha _ (by simp; omega)).append (hb _ (by simp; omega))

theorem roundTrip_mprod {α β : Type} [Value α] [Value β] (ha : Value.RoundTrip α) (hb : Value.RoundTrip β) :
    Value.RoundTrip (MProd α β) := fun es h => by
  have hw : Value.width (MProd α β) = Value.width α + Value.width β := by
    simp [Value.width, Value.ranges, Value.shape, Shape.ranges_tuple]
  rw [hw] at h
  show ExprsEquiv (Value.toExprs (Value.ofExprs (es.take (Value.width α)) : α) ++
    Value.toExprs (Value.ofExprs (es.drop (Value.width α)) : β)) es
  conv => rhs; rw [← List.take_append_drop (Value.width α) es]
  exact (ha _ (by simp; omega)).append (hb _ (by simp; omega))

theorem roundTrip_maybe {α : Type} [Value α] (ha : Value.RoundTrip α) : Value.RoundTrip (Maybe α) := fun es h => by
  rw [Value.width_maybe] at h
  match es, h with
  | [], h => simp at h; omega
  | e :: es, h =>
    show ExprsEquiv ([e] ++ Value.toExprs (Value.ofExprs es : α)) ([e] ++ es)
    exact (ExprsEquiv.refl _).append (ha _ (by simp at h; omega))

theorem roundTrip_forInStep {α : Type} [Value α] (ha : Value.RoundTrip α) : Value.RoundTrip (ForInStep α) :=
  fun es h => ha es h

theorem roundTrip_vector {α : Type} [Value α] {n : Nat} (ha : Value.RoundTrip α) :
    Value.RoundTrip (Vector α n) := fun es h => by
  rw [Value.width_vector] at h
  show ExprsEquiv ((Vector.ofFn fun (i : Fin n) =>
    (Value.ofExprs ((es.drop (i.val * Value.width α)).take (Value.width α)) : α)).toList.flatMap Value.toExprs) es
  rw [Vector.toList_ofFn, List.flatMap_def, List.map_ofFn]
  conv => rhs; rw [← flatten_chunks (Value.width α) n es h]
  refine ExprsEquiv.flatten_ofFn _ _ fun i => ha _ ?_
  simp only [List.length_take, List.length_drop, h]
  have : i.val * Value.width α + Value.width α ≤ n * Value.width α := by
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ i.isLt
  omega

/-! ## Each argument means the inputs at its position -/

/-- A value means the list of field elements its expressions evaluate to. -/
def Value.Is (p : Zkir.Prims) (env : Env) {α : Type} [Value α] (a : α) (xs : List Fr) : Prop :=
  Expr.evalList p env (Value.toExprs a) = some xs

section Decode
variable {p : Zkir.Prims}

/-- Feeding arguments to `α → φ`: the first `width α` expressions make the first argument. -/
@[simp] theorem CircuitFnSpec.apply_arrow {α φ : Type} [Value α] [CircuitFn φ] [CircuitFnSpec φ]
    (f : α → φ) (xs : List Expr) :
    CircuitFnSpec.apply f xs =
      CircuitFnSpec.apply (f (Value.ofExprs (xs.take (Value.width α)))) (xs.drop (Value.width α)) := rfl

/-- With no arguments left, the body is the function itself. -/
@[simp] theorem CircuitFnSpec.apply_result {ρ : Type} [Value ρ] (m : CircuitM ρ) (xs : List Expr) :
    CircuitFnSpec.apply m xs = m := rfl

@[simp] theorem CircuitFnSpec.ranges_arrow {α φ : Type} [Value α] [CircuitFn φ] [CircuitFnSpec φ] :
    CircuitFnSpec.ranges (α → φ) = Value.ranges α ++ CircuitFnSpec.ranges φ := rfl

@[simp] theorem CircuitFnSpec.ranges_result {ρ : Type} [Value ρ] : CircuitFnSpec.ranges (CircuitM ρ) = [] := rfl

/-- Feeding the input variables to `α → φ`: the first argument is read off the first `width α`. -/
theorem CircuitFnSpec.apply_argVars {α φ : Type} [Value α] [CircuitFn φ] [CircuitFnSpec φ]
    (f : α → φ) (k : Nat) :
    CircuitFnSpec.apply f (argVars k (CircuitFnSpec.ranges (α → φ)).length) =
      CircuitFnSpec.apply (f (Value.ofExprs (argVars k (Value.width α))))
        (argVars (k + Value.width α) (CircuitFnSpec.ranges φ).length) := by
  rw [CircuitFnSpec.apply_arrow, CircuitFnSpec.ranges_arrow, List.length_append]
  rw [show (Value.ranges α).length = Value.width α from rfl, argVars_take, argVars_drop]

/-- The input variables evaluate to their values. -/
theorem evalList_argVars (env : Env) (k n : Nat) :
    Expr.evalList p env (argVars k n) = some ((List.range' k n).map env) := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => simp [argVars, List.range'_succ, Expr.evalList, Expr.eval] at ih ⊢; rw [ih]; rfl

/-- The values of the input variables `k … k+n-1` are the inputs at those positions. -/
theorem range'_map_getD (xs : List Fr) (k n : Nat) (h : k + n ≤ xs.length) :
    (List.range' k n).map (fun v => xs.getD v 0) = (xs.drop k).take n := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp at h1
  simp [List.getElem_range', List.getElem?_eq_getElem (show k + i < xs.length by omega)]

/-- **Decoding.** An argument of a type that round-trips, read off input variables `k …`,
    means the values of those variables. -/
theorem arg_is {α : Type} [Value α] (h : Value.RoundTrip α) (env : Env) (k : Nat) :
    Value.Is p env (Value.ofExprs (argVars k (Value.width α)) : α) ((List.range' k (Value.width α)).map env) := by
  unfold Value.Is
  rw [h _ (by simp [argVars]) p env, evalList_argVars]

/-- **Decoding**, with the inputs bound as `mkCircuit_run` binds them: an argument at offset `k`
    means the inputs `k … k + width α - 1`. -/
theorem arg_is_inputs {α : Type} [Value α] (h : Value.RoundTrip α) (xs : List Fr) (k : Nat)
    (hk : k + Value.width α ≤ xs.length) :
    Value.Is p (fun v => xs.getD v 0) (Value.ofExprs (argVars k (Value.width α)) : α)
      ((xs.drop k).take (Value.width α)) := by
  rw [← range'_map_getD xs k _ hk]; exact arg_is h _ k

/-- Range checks of consecutive arguments. -/
theorem rangesHold_append (r₁ r₂ : List (Option Range)) (xs : List Fr) (h : r₁.length ≤ xs.length) :
    rangesHold (r₁ ++ r₂) xs = (rangesHold r₁ (xs.take r₁.length) && rangesHold r₂ (xs.drop r₁.length)) := by
  induction r₁ generalizing xs with
  | nil => simp [rangesHold]
  | cons r r₁ ih =>
    match xs, h with
    | x :: xs, h =>
      simp only [List.length_cons, Nat.add_le_add_iff_right] at h
      simp only [rangesHold, List.cons_append, List.zip_cons_cons, List.all_cons, List.length_cons,
        List.take_succ_cons, List.drop_succ_cons] at ih ⊢
      rw [ih xs h, Bool.and_assoc]

/-- A `Uint m` argument whose input passed its range check means the input's number. -/
theorem arg_uint_is {m : Nat} (hm : m ≤ Uint.maxBound) (env : Env) (v : Var)
    (h : rangesHold (Value.ranges (Uint m)) [env v] = true) :
    Uint.Is p env (Value.ofExprs [Expr.var v] : Uint m) (env v).val := by
  rw [valueRanges_uint] at h
  have hv := uint_of_holds (p := p) (env := env) (v := v) (Uint.lt_of_le_maxBound hm)
    (by simpa [rangesHold] using h)
  exact ⟨hv.1, by show (Uint.capped m _).eval p env = _; rw [Uint.capped_eval hm]; exact hv.2⟩

/-- A `Boolean` argument whose input passed its range check means a truth value. -/
theorem arg_boolean_is (env : Env) (v : Var)
    (h : rangesHold (Value.ranges Boolean) [env v] = true) :
    ∃ b, Boolean.Is p env (Value.ofExprs [Expr.var v] : Boolean) b :=
  boolean_of_holds (by simpa [rangesHold, Value.ranges, Value.shape, Shape.ranges_prim, Ty.ranges] using h)

end Decode
end Damp
