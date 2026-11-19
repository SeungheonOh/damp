/-
The ZKIR emitter preserves the meaning of circuits.

`circuitCore_correct` says that running the ZKIR that `Emit.circuitCore`
produces for a circuit, under Midnight's evaluator (`Damp/Zkir/Semantics.lean`),
gives exactly what the IR semantics (`Damp/IR/Semantics.lean`) says the circuit
gives: the same outputs and public inputs, or failure on both sides.

The proof follows the emitter. An invariant (`Inv`) ties the emitter's state
(which register holds each variable and each shared expression) to an IR
environment and a ZKIR memory. Expressions (`Spec`), range checks, input reads,
ledger operands and statements each preserve it, and a run of a statement on
one side is matched by a run of its instructions on the other (`Sim`).
-/
import Damp.Compile.Emit
import Damp.IR.Semantics
import Damp.Proofs.Prune

set_option linter.unusedSimpArgs false

namespace Damp.Emit
open Damp.IR
open Damp.Zkir (Prims Memory Instr Operand Ident Value native natives resolve evalGuard
  readOne exec)

/-! ## Small facts about lists and the ZKIR evaluator -/

/-- Looking up a key other than the first skips the first entry. -/
theorem lookup_cons_ne {α β : Type} [BEq α] [LawfulBEq α] {a k : α} {b : β} {l : List (α × β)}
    (h : a ≠ k) : ((k, b) :: l).lookup a = l.lookup a := by
  rw [List.lookup_cons]
  have : (a == k) = false := by simpa using h
  rw [this]

/-- Running a concatenation runs the first part, then the second. -/
theorem exec_append (p : Prims) :
    ∀ (is₁ is₂ : List Instr) (σ : Zkir.State), exec p (is₁ ++ is₂) σ = (exec p is₁ σ).bind (exec p is₂)
  | [], _, _ => rfl
  | i :: is, is₂, σ => by
      simp only [List.cons_append, Zkir.exec]
      cases i.step p σ with
      | none => rfl
      | some σ' => exact exec_append p is is₂ σ'

/-- Running one instruction is a single step. -/
theorem exec_single (p : Prims) (i : Instr) (σ : Zkir.State) : exec p [i] σ = i.step p σ := by
  simp only [Zkir.exec]
  cases i.step p σ <;> rfl

/-- A register holds a native element exactly when reading it as an operand gives that element. -/
theorem native_var {m : Memory} {r : Ident} {x : Fr} :
    native m (.var r) = some x ↔ m r = some (.native x) := by
  simp only [native, resolve]
  split <;> simp_all

/-- An immediate reads as its field element. -/
theorem native_imm (m : Memory) (c : Int) : native m (.imm c) = some (Fr.ofInt c) := rfl

/-- A native operand also resolves to its value. -/
theorem resolve_of_native {m : Memory} {o : Operand} {x : Fr} (h : native m o = some x) :
    resolve m o = some (.native x) := by
  simp only [native] at h
  split at h <;> simp_all

/-- `asBool` and `bool` read a condition the same way. -/
theorem bool_of_native {m : Memory} {o : Operand} {x : Fr} (h : native m o = some x) :
    Zkir.bool m o = asBool x := by
  simp only [Zkir.bool, h, asBool]

/-- A boolean stored as 0/1 reads back as itself. -/
theorem asBool_ofBool (b : Bool) : asBool (Fr.ofBool b) = some b := by
  cases b <;> simp [asBool, Fr.ofBool, Fr.zero_ne_one.symm]

/-- No operands, no values. -/
theorem natives_nil (m : Memory) : natives m [] = some [] := rfl

/-- Decoding operands one at a time. -/
theorem natives_cons {m : Memory} {o : Operand} {os : List Operand} {x : Fr} {xs : List Fr}
    (h : native m o = some x) (hs : natives m os = some xs) : natives m (o :: os) = some (x :: xs) := by
  simp [natives, h, hs]

/-- Decoding two operand lists decodes their concatenation. -/
theorem natives_append (m : Memory) :
    ∀ (os os' : List Operand) (xs xs' : List Fr), natives m os = some xs → natives m os' = some xs' →
      natives m (os ++ os') = some (xs ++ xs')
  | [], _, xs, _, h, h' => by cases h; simpa using h'
  | o :: os, os', xs, xs', h, h' => by
      cases hx : native m o <;> cases hys : natives m os <;> simp_all [natives]
      rename_i x ys
      subst h
      simp [natives_append m os os' ys xs' hys h']

/-- Native operands decoded together give as many values as operands. -/
theorem natives_length {m : Memory} :
    ∀ {os : List Operand} {xs : List Fr}, natives m os = some xs → os.length = xs.length
  | [], xs, h => by cases h; rfl
  | o :: os, xs, h => by
      cases hx : native m o <;> cases hys : natives m os <;> simp_all [natives]
      subst h
      simp [natives_length hys]

/-- A list of one native operand. -/
theorem natives_single {m : Memory} {o : Operand} {xs : List Fr} :
    natives m [o] = some xs ↔ ∃ x, native m o = some x ∧ xs = [x] := by
  simp only [natives, bind, Option.bind]
  cases native m o <;> simp [eq_comm]

/-- A one-element list evaluates to its element's value. -/
theorem evalList_single (p : Prims) (env : Env) (e : Expr) :
    Expr.evalList p env [e] = (e.eval p env).map fun x => [x] := by
  simp only [Expr.evalList, bind, Option.bind]
  cases e.eval p env <;> rfl

/-- Evaluating a concatenation evaluates both parts. -/
theorem evalList_append (p : Prims) (env : Env) :
    ∀ xs ys : List Expr, Expr.evalList p env (xs ++ ys) =
      (Expr.evalList p env xs).bind fun a => (Expr.evalList p env ys).map fun b => a ++ b
  | [], ys => by simp [Expr.evalList]
  | x :: xs, ys => by
      simp only [List.cons_append, Expr.evalList, evalList_append p env xs ys, bind, Option.bind]
      cases x.eval p env with
      | none => rfl
      | some y =>
        cases Expr.evalList p env xs with
        | none => rfl
        | some ys' => cases Expr.evalList p env ys <;> rfl

/-- Variables of a concatenation are the variables of the parts. -/
theorem varsList_append : ∀ xs ys : List Expr,
    Expr.varsList (xs ++ ys) = Expr.varsList xs ++ Expr.varsList ys
  | [], _ => rfl
  | x :: xs, ys => by simp [Expr.varsList, varsList_append xs ys]


/-! ## Registers and the invariant -/

/-- Every register written in `m` is numbered below `n`. -/
def Fresh (n : Nat) (m : Memory) : Prop := ∀ r : Ident, m r ≠ none → r.id < n

/-- `m'` holds what `m` holds in every register numbered below `n`. -/
def MemEq (n : Nat) (m m' : Memory) : Prop := ∀ r : Ident, r.id < n → m' r = m r

/-- A memory agrees with itself. -/
theorem MemEq.refl (n : Nat) (m : Memory) : MemEq n m m := fun _ _ => rfl

/-- Agreement composes, on the smaller range. -/
theorem MemEq.trans {n n' : Nat} {m₁ m₂ m₃ : Memory} (h₁ : MemEq n m₁ m₂) (h₂ : MemEq n' m₂ m₃)
    (hn : n ≤ n') : MemEq n m₁ m₃ :=
  fun r hr => (h₂ r (by omega)).trans (h₁ r hr)

/-- Agreement on a range implies agreement on a smaller one. -/
theorem MemEq.mono {n n' : Nat} {m m' : Memory} (h : MemEq n' m m') (hn : n ≤ n') : MemEq n m m' :=
  fun r hr => h r (by omega)

/-- Writing a register numbered at least `n` leaves those below `n` alone. -/
theorem MemEq.set {n : Nat} {m : Memory} {r : Ident} {v : Value} (hn : n ≤ r.id) :
    MemEq n m (m.set r v) := by
  intro r' hr'
  simp only [Zkir.Memory.set]
  split
  · next h => subst h; omega
  · rfl

/-- An operand's value survives any change to registers numbered from `n` on,
    when every written register is below `n`. -/
theorem native_stable {n : Nat} {m m' : Memory} {o : Operand} {x : Fr} (h : native m o = some x)
    (hf : Fresh n m) (he : MemEq n m m') : native m' o = some x := by
  cases o with
  | imm c => exact h
  | var r =>
    rw [native_var] at h ⊢
    rw [he r (hf r (by simp [h]))]
    exact h

/-- `native_stable` for a list of operands. -/
theorem natives_stable {n : Nat} {m m' : Memory} (hf : Fresh n m) (he : MemEq n m m') :
    ∀ {os : List Operand} {xs : List Fr}, natives m os = some xs → natives m' os = some xs
  | [], _, h => h
  | o :: os, xs, h => by
      cases hx : native m o <;> cases hys : natives m os <;> simp_all [natives]
      rename_i x ys
      subst h
      exact natives_cons (native_stable hx hf he) (natives_stable hf he hys)

/-- What the emitter state promises about an IR environment and a ZKIR memory. -/
structure Inv (p : Prims) (s : State) (env : Env) (m : Memory) : Prop where
  /-- Each bound variable's register holds the variable's value. -/
  vars : ∀ v o, s.vars.lookup v = some o → native m o = some (env v)
  /-- Each shared expression has a value, and its register holds it. -/
  memo : ∀ e o, s.memo.lookup e = some o → ∃ x, e.eval p env = some x ∧ native m o = some x
  /-- Each shared expression mentions only bound variables. -/
  closed : ∀ e o, s.memo.lookup e = some o → ∀ v ∈ e.vars, s.vars.lookup v ≠ none
  /-- Registers from `s.next` on are unwritten. -/
  fresh : Fresh s.next m

/-- The invariant reads only the counter, the variables and the shared expressions. -/
theorem Inv.congr {p : Prims} {s s' : State} {env : Env} {m : Memory} (h : Inv p s env m)
    (hn : s.next ≤ s'.next) (hv : s'.vars = s.vars) (hm : s'.memo = s.memo) : Inv p s' env m where
  vars := by rw [hv]; exact h.vars
  memo := by rw [hm]; exact h.memo
  closed := by rw [hm, hv]; exact h.closed
  fresh := fun r hr => Nat.lt_of_lt_of_le (h.fresh r hr) hn

/-- Writing a fresh register and advancing the counter past it keeps the invariant. -/
theorem Inv.set {p : Prims} {s : State} {env : Env} {m : Memory} {r : Ident} {v : Value} {n : Nat}
    (h : Inv p s env m) (h₁ : s.next ≤ r.id) (h₂ : r.id < n) :
    Inv p { s with next := n } env (m.set r v) where
  vars := fun w o hw => native_stable (h.vars w o hw) h.fresh (MemEq.set h₁)
  memo := fun e o he => by
    obtain ⟨x, hx, ho⟩ := h.memo e o he
    exact ⟨x, hx, native_stable ho h.fresh (MemEq.set h₁)⟩
  closed := h.closed
  fresh := by
    intro r' hr'
    simp only [Zkir.Memory.set] at hr'
    split at hr'
    · next heq => subst heq; exact h₂
    · have := h.fresh r' hr'; show r'.id < n; omega

/-- Remembering an expression in a register holding its value keeps the invariant. -/
theorem Inv.memo_cons {p : Prims} {s : State} {env : Env} {m : Memory} {e : Expr} {o : Operand}
    {x : Fr} (h : Inv p s env m) (he : e.eval p env = some x) (ho : native m o = some x)
    (hv : ∀ v ∈ e.vars, s.vars.lookup v ≠ none) :
    Inv p { s with memo := (e, o) :: s.memo } env m where
  vars := h.vars
  memo := by
    intro e' o' h'
    by_cases hee : e' = e
    · subst hee
      simp only [List.lookup_cons_self, Option.some.injEq] at h'
      subst h'
      exact ⟨x, he, ho⟩
    · rw [lookup_cons_ne hee] at h'
      exact h.memo e' o' h'
  closed := by
    intro e' o' h'
    by_cases hee : e' = e
    · subst hee; exact hv
    · rw [lookup_cons_ne hee] at h'
      exact h.closed e' o' h'
  fresh := h.fresh

/-- Binding an unbound variable to a register holding its new value keeps the
    invariant. Shared expressions keep their values because they cannot mention
    the variable. -/
theorem Inv.bind {p : Prims} {s : State} {env : Env} {m : Memory} {v : Var} {o : Operand} {x : Fr}
    (h : Inv p s env m) (hv : s.vars.lookup v = none) (ho : native m o = some x) :
    Inv p { s with vars := (v, o) :: s.vars } (env.set v x) m where
  vars := by
    intro w o' hw
    by_cases hwv : w = v
    · subst hwv
      simp only [List.lookup_cons_self, Option.some.injEq] at hw
      subst hw
      simpa [Env.set] using ho
    · rw [lookup_cons_ne hwv] at hw
      simpa [Env.set, hwv] using h.vars w o' hw
  memo := by
    intro e o' he
    obtain ⟨y, hy, ho'⟩ := h.memo e o' he
    refine ⟨y, ?_, ho'⟩
    rw [eval_congr p e (e₂ := env)]
    · exact hy
    · intro w hw
      have hb := h.closed e o' he w hw
      have : w ≠ v := fun hwv => hb (hwv ▸ hv)
      simp [Env.set, this]
  closed := by
    intro e o' he w hw
    by_cases hwv : w = v
    · subst hwv; simp
    · rw [lookup_cons_ne hwv]; exact h.closed e o' he w hw
  fresh := h.fresh

/-- The invariant holds of the empty state and the empty memory. -/
theorem Inv.empty (p : Prims) (env : Env) : Inv p {} env (fun _ => none) where
  vars := by intro v o h; simp at h
  memo := by intro e o h; simp at h
  closed := by intro e o h; simp at h
  fresh := by intro r h; simp at h


/-! ## Expressions -/

/-- What the instructions emitted for a list of expressions achieve: from any
    memory the invariant relates to `env`, they fail exactly when some
    expression has no value; otherwise they write only fresh registers, leave
    the values in the result operands, and re-establish the invariant for the
    new emitter state, which has the same variables. The expressions' variables
    are bound. -/
def Spec (p : Prims) (xs : List Expr) (s : State) (os : List Operand) (is : List Instr)
    (s' : State) : Prop :=
  ∀ (env : Env) (σ : Zkir.State), Inv p s env σ.mem →
    (Expr.evalList p env xs = none → exec p is σ = none) ∧
    ∀ vs, Expr.evalList p env xs = some vs →
      ∃ m', exec p is σ = some { σ with mem := m' } ∧ MemEq s.next σ.mem m' ∧ Inv p s' env m' ∧
        natives m' os = some vs ∧ s.next ≤ s'.next ∧ s'.vars = s.vars ∧
        ∀ v ∈ Expr.varsList xs, s.vars.lookup v ≠ none

/-- `Spec` for a single expression, stated with `Expr.eval`. -/
def Spec1 (p : Prims) (e : Expr) (s : State) (o : Operand) (is : List Instr) (s' : State) : Prop :=
  ∀ (env : Env) (σ : Zkir.State), Inv p s env σ.mem →
    (e.eval p env = none → exec p is σ = none) ∧
    ∀ x, e.eval p env = some x →
      ∃ m', exec p is σ = some { σ with mem := m' } ∧ MemEq s.next σ.mem m' ∧ Inv p s' env m' ∧
        native m' o = some x ∧ s.next ≤ s'.next ∧ s'.vars = s.vars ∧
        ∀ v ∈ e.vars, s.vars.lookup v ≠ none

/-- Decoding a nonempty operand list decodes its head and tail. -/
theorem natives_cons_inv {m : Memory} {o : Operand} {os : List Operand} {vs : List Fr}
    (h : natives m (o :: os) = some vs) :
    ∃ x xs, native m o = some x ∧ natives m os = some xs ∧ vs = x :: xs := by
  cases hx : native m o <;> cases hys : natives m os <;> simp_all [natives]

/-- `Spec1` is `Spec` of a one-element list. -/
theorem Spec1.spec {p : Prims} {e : Expr} {s s' : State} {o : Operand} {is : List Instr}
    (h : Spec1 p e s o is s') : Spec p [e] s [o] is s' := by
  intro env σ hinv
  obtain ⟨f, k⟩ := h env σ hinv
  rw [evalList_single]
  refine ⟨fun hn => f (by cases he : e.eval p env <;> simp_all), fun vs hvs => ?_⟩
  cases he : e.eval p env with
  | none => simp [he] at hvs
  | some x =>
    simp only [he, Option.map_some, Option.some.injEq] at hvs
    subst hvs
    obtain ⟨m', h1, h2, h3, h4, h5, h6, h7⟩ := k x he
    exact ⟨m', h1, h2, h3, natives_cons h4 rfl, h5, h6, by simpa [Expr.varsList] using h7⟩

/-- The converse of `Spec1.spec`. -/
theorem Spec.spec1 {p : Prims} {e : Expr} {s s' : State} {o : Operand} {is : List Instr}
    (h : Spec p [e] s [o] is s') : Spec1 p e s o is s' := by
  intro env σ hinv
  obtain ⟨f, k⟩ := h env σ hinv
  rw [evalList_single] at f k
  refine ⟨fun hn => f (by simp [hn]), fun x hx => ?_⟩
  obtain ⟨m', h1, h2, h3, h4, h5, h6, h7⟩ := k [x] (by simp [hx])
  obtain ⟨y, ys, hy, _, hxy⟩ := natives_cons_inv h4
  simp only [List.cons.injEq] at hxy
  rw [← hxy.1] at hy
  exact ⟨m', h1, h2, h3, hy, h5, h6, by simpa [Expr.varsList] using h7⟩

/-- The empty list of expressions emits nothing. -/
theorem Spec.nil (p : Prims) (s : State) : Spec p [] s [] [] s := by
  intro env σ h
  refine ⟨fun hn => by simp [Expr.evalList] at hn, fun vs hvs => ?_⟩
  simp only [Expr.evalList, Option.some.injEq] at hvs
  subst hvs
  exact ⟨σ.mem, rfl, MemEq.refl _ _, h, rfl, Nat.le_refl _, rfl, by simp [Expr.varsList]⟩

/-- The code for two lists of expressions, one after the other, computes both. -/
theorem Spec.append {p : Prims} {xs ys : List Expr} {s s₁ s₂ : State} {os os' : List Operand}
    {is₁ is₂ : List Instr} (h₁ : Spec p xs s os is₁ s₁) (h₂ : Spec p ys s₁ os' is₂ s₂) :
    Spec p (xs ++ ys) s (os ++ os') (is₁ ++ is₂) s₂ := by
  intro env σ hinv
  obtain ⟨f₁, k₁⟩ := h₁ env σ hinv
  rw [evalList_append, exec_append]
  cases hx : Expr.evalList p env xs with
  | none => simp [f₁ hx]
  | some a =>
    obtain ⟨m₁, he₁, hm₁, hi₁, hn₁, hle₁, hv₁, hb₁⟩ := k₁ a hx
    obtain ⟨f₂, k₂⟩ := h₂ env { σ with mem := m₁ } hi₁
    rw [he₁]
    simp only [Option.bind_some]
    cases hy : Expr.evalList p env ys with
    | none => simp [f₂ hy]
    | some b =>
      obtain ⟨m₂, he₂, hm₂, hi₂, hn₂, hle₂, hv₂, hb₂⟩ := k₂ b hy
      refine ⟨fun hn => by simp at hn, fun vs hvs => ?_⟩
      simp only [Option.map_some, Option.some.injEq] at hvs
      subst hvs
      refine ⟨m₂, he₂, hm₁.trans hm₂ hle₁, hi₂,
        natives_append _ _ _ _ _ (natives_stable hi₁.fresh hm₂ hn₁) hn₂, by omega, hv₂.trans hv₁, ?_⟩
      rw [varsList_append]
      intro v hv
      rcases List.mem_append.1 hv with hv | hv
      · exact hb₁ v hv
      · rw [← hv₁]; exact hb₂ v hv

/-- A shared expression costs nothing: its register already holds its value. -/
theorem spec1_memo {p : Prims} {e : Expr} {s : State} {o : Operand} (h : s.memo.lookup e = some o) :
    Spec1 p e s o [] s := by
  intro env σ hinv
  obtain ⟨x, hx, ho⟩ := hinv.memo e o h
  refine ⟨fun hn => by simp [hx] at hn, fun y hy => ?_⟩
  rw [hx, Option.some.injEq] at hy
  subst hy
  exact ⟨σ.mem, rfl, MemEq.refl _ _, hinv, ho, Nat.le_refl _, rfl, hinv.closed e o h⟩

/-- A variable is read from its register. -/
theorem spec1_var {p : Prims} {v : Var} {s : State} {o : Operand} (h : s.vars.lookup v = some o) :
    Spec1 p (.var v) s o [] s := by
  intro env σ hinv
  refine ⟨fun hn => by simp [Expr.eval] at hn, fun y hy => ?_⟩
  simp only [Expr.eval, Option.some.injEq] at hy
  subst hy
  refine ⟨σ.mem, rfl, MemEq.refl _ _, hinv, hinv.vars v o h, Nat.le_refl _, rfl, ?_⟩
  intro w hw
  simp only [Expr.vars, List.mem_singleton] at hw
  subst hw
  rw [h]
  exact Option.some_ne_none _

/-- A constant is an immediate. -/
theorem spec1_const (p : Prims) (c : Int) (s : State) : Spec1 p (.const c) s (.imm c) [] s := by
  intro env σ hinv
  refine ⟨fun hn => by simp [Expr.eval] at hn, fun y hy => ?_⟩
  simp only [Expr.eval, Option.some.injEq] at hy
  subst hy
  exact ⟨σ.mem, rfl, MemEq.refl _ _, hinv, rfl, Nat.le_refl _, rfl, by simp [Expr.vars]⟩

/-- `disclose` is transparent. -/
theorem Spec1.disclose {p : Prims} {e : Expr} {s s' : State} {o : Operand} {is : List Instr}
    (h : Spec1 p e s o is s') : Spec1 p (.disclose e) s o is s' := by
  simpa only [Spec1, Expr.eval, Expr.vars] using h

/-- One new instruction computing an operation of the operands' values into a
    fresh register, remembered for sharing. -/
theorem spec1_finish {p : Prims} {e : Expr} {xs : List Expr} {hint : String} {mk : Ident → Instr}
    {f : List Fr → Option Fr} {pre : List Instr} {os : List Operand} {s s₂ : State}
    (hsub : Spec p xs s os pre s₂)
    (heval : ∀ env, e.eval p env = (Expr.evalList p env xs).bind f)
    (hvars : e.vars = Expr.varsList xs)
    (hstep : ∀ (σ : Zkir.State) (out : Ident) (vs : List Fr), natives σ.mem os = some vs →
      (mk out).step p σ = (f vs).map fun z => { σ with mem := σ.mem.set out (.native z) }) :
    Spec1 p e s (finish e hint mk pre s₂).1 (finish e hint mk pre s₂).2.1
      (finish e hint mk pre s₂).2.2 := by
  intro env σ hinv
  obtain ⟨f₁, k₁⟩ := hsub env σ hinv
  simp only [finish]
  rw [heval, exec_append]
  cases hx : Expr.evalList p env xs with
  | none => simp [f₁ hx]
  | some vs =>
    obtain ⟨m₁, he₁, hm₁, hi₁, hn₁, hle₁, hv₁, hb₁⟩ := k₁ vs hx
    rw [he₁]
    simp only [Option.bind_some, exec_single]
    rw [hstep _ _ vs hn₁]
    cases hf : f vs with
    | none => simp
    | some z =>
      refine ⟨fun hn => by simp at hn, fun y hy => ?_⟩
      simp only [Option.some.injEq] at hy
      subst hy
      have hout : native (m₁.set ⟨hint, s₂.next⟩ (.native z)) (.var ⟨hint, s₂.next⟩) = some z := by
        rw [native_var]; simp [Zkir.Memory.set]
      refine ⟨m₁.set ⟨hint, s₂.next⟩ (.native z), rfl,
        hm₁.trans (MemEq.set (Nat.le_refl _)) hle₁, ?_, hout, by show s.next ≤ s₂.next + 1; omega, hv₁,
        hvars ▸ hb₁⟩
      have hi := hi₁.set (r := ⟨hint, s₂.next⟩) (v := .native z) (Nat.le_refl _) (Nat.lt_succ_self _)
      refine hi.memo_cons (by rw [heval, hx]; exact hf) hout ?_
      intro v hv
      rw [hv₁]
      exact hb₁ v (hvars ▸ hv)

/-- The persistent hash: one hash, split into both halves, both remembered. -/
theorem spec1_phash {p : Prims} {high : Bool} {align : List Zkir.AlignAtom} {xs : List Expr}
    {s s₁ : State} {os : List Operand} {pre : List Instr} (hsub : Spec p xs s os pre s₁) :
    Spec1 p (.phash high align xs) s (.var (if high then ⟨"t", s₁.next + 2⟩ else ⟨"t", s₁.next + 1⟩))
      (pre ++ [.persistentHash ⟨"bytes", s₁.next⟩ align os,
        .bytesIntoNatives [⟨"t", s₁.next + 1⟩, ⟨"t", s₁.next + 2⟩] (.var ⟨"bytes", s₁.next⟩)])
      { s₁ with next := s₁.next + 3, memo :=
          (Expr.phash true align xs, .var ⟨"t", s₁.next + 2⟩) ::
          (Expr.phash false align xs, .var ⟨"t", s₁.next + 1⟩) :: s₁.memo } := by
  intro env σ hinv
  obtain ⟨f₁, k₁⟩ := hsub env σ hinv
  rw [exec_append]
  cases hx : Expr.evalList p env xs with
  | none => simp [Expr.eval, hx, f₁ hx]
  | some vs =>
    obtain ⟨m₁, he₁, hm₁, hi₁, hn₁, hle₁, hv₁, hb₁⟩ := k₁ vs hx
    rw [he₁]
    simp only [Option.bind_some]
    cases hd : p.persistentHash align vs with
    | none =>
      simp [Expr.eval, hx, hd, Zkir.exec, Zkir.Instr.step, hn₁]
    | some d =>
      simp [Expr.eval, hx, hd, Zkir.exec, Zkir.Instr.step, hn₁, resolve, Zkir.Memory.set]
      rcases hb : Zkir.bytesToNatives d with _ | ⟨lo, _ | ⟨hi, _ | ⟨z, t⟩⟩⟩
      · simp
      · simp
      rotate_left
      · simp
      refine ⟨fun hn => by simp at hn, fun x hx' => ?_⟩
      simp only [Option.some.injEq] at hx'
      subst hx'
      -- The three registers written: the digest, then its two halves.
      let rb : Ident := ⟨"bytes", s₁.next⟩
      let rl : Ident := ⟨"t", s₁.next + 1⟩
      let rh : Ident := ⟨"t", s₁.next + 2⟩
      let m₃ := ((m₁.set rb (.bytes d)).set rl (.native lo)).set rh (.native hi)
      have hl : native m₃ (.var rl) = some lo := by
        rw [native_var]; simp [m₃, rl, rh, Zkir.Memory.set]
      have hh : native m₃ (.var rh) = some hi := by
        rw [native_var]; simp [m₃, rh, Zkir.Memory.set]
      have heval : ∀ b, (Expr.phash b align xs).eval p env = some (if b then hi else lo) := by
        intro b; simp [Expr.eval, hx, hd, hb]
      have hclosed : ∀ b, ∀ v ∈ (Expr.phash b align xs).vars, s₁.vars.lookup v ≠ none := by
        intro b v hv; rw [hv₁]; exact hb₁ v (by simpa [Expr.vars] using hv)
      have hi₃ : Inv p { s₁ with next := s₁.next + 3 } env m₃ :=
        ((hi₁.set (r := rb) (v := .bytes d) (Nat.le_refl _) (Nat.lt_succ_self _)).set
          (r := rl) (v := .native lo) (Nat.le_refl _) (Nat.lt_succ_self _)).set
          (r := rh) (v := .native hi) (Nat.le_refl _) (Nat.lt_succ_self _)
      refine ⟨m₃, rfl, ?_, ?_, ?_, by show s.next ≤ s₁.next + 3; omega, hv₁, ?_⟩
      · exact hm₁.trans ((MemEq.set (Nat.le_refl _)).trans ((MemEq.set (Nat.le_succ _)).trans
          (MemEq.set (Nat.le_succ_of_le (Nat.le_succ _))) (Nat.le_refl _)) (Nat.le_refl _)) hle₁
      · exact (hi₃.memo_cons (heval false) hl (hclosed false)).memo_cons (heval true) hh (hclosed true)
      · cases high <;> assumption
      · intro v hv
        have := hb₁ v (by simpa [Expr.vars] using hv)
        simpa using this

/-- Division by a power of two: one instruction yields quotient and remainder,
    both remembered. -/
theorem spec1_divmod {p : Prims} {quot : Bool} {bits : Nat} {a : Expr} {s s₁ : State}
    {a' : Operand} {pre : List Instr} (hsub : Spec1 p a s a' pre s₁) :
    Spec1 p (.divmod quot bits a) s
      (.var (if quot then ⟨"tmp", s₁.next⟩ else ⟨"tmp", s₁.next + 1⟩))
      (pre ++ [.divModPowerOfTwo [⟨"tmp", s₁.next⟩, ⟨"tmp", s₁.next + 1⟩] a' bits])
      { s₁ with next := s₁.next + 2, memo :=
          (Expr.divmod true bits a, .var ⟨"tmp", s₁.next⟩) ::
          (Expr.divmod false bits a, .var ⟨"tmp", s₁.next + 1⟩) :: s₁.memo } := by
  intro env σ hinv
  obtain ⟨f₁, k₁⟩ := hsub env σ hinv
  rw [exec_append]
  cases hx : a.eval p env with
  | none => simp [Expr.eval, hx, f₁ hx]
  | some x =>
    obtain ⟨m₁, he₁, hm₁, hi₁, hn₁, hle₁, hv₁, hb₁⟩ := k₁ x hx
    rw [he₁]
    simp only [Option.bind_some]
    rcases Nat.lt_or_ge 248 bits with hbits | hbits
    · have : ¬ bits ≤ 248 := by omega
      simp [Expr.eval, hx, this, Zkir.exec, Zkir.Instr.step, hn₁]
    simp [Expr.eval, hx, hbits, Zkir.exec, Zkir.Instr.step, hn₁]
    let rq : Ident := ⟨"tmp", s₁.next⟩
    let rr : Ident := ⟨"tmp", s₁.next + 1⟩
    let vq := Fr.ofNat (x.val / 2 ^ bits)
    let vr := Fr.ofNat (x.val % 2 ^ bits)
    let m₂ := (m₁.set rq (.native vq)).set rr (.native vr)
    have hq : native m₂ (.var rq) = some vq := by
      rw [native_var]; simp [m₂, rq, rr, Zkir.Memory.set]
    have hr : native m₂ (.var rr) = some vr := by
      rw [native_var]; simp [m₂, rr, Zkir.Memory.set]
    have heval : ∀ b, (Expr.divmod b bits a).eval p env =
        some (if b then vq else vr) := by
      intro b; cases b <;> simp [Expr.eval, hx, hbits, vq, vr]
    have hclosed : ∀ b, ∀ v ∈ (Expr.divmod b bits a).vars, s₁.vars.lookup v ≠ none := by
      intro b v hv; rw [hv₁]; exact hb₁ v (by simpa [Expr.vars] using hv)
    have hi₂ : Inv p { s₁ with next := s₁.next + 2 } env m₂ :=
      (hi₁.set (r := rq) (v := .native vq) (Nat.le_refl _) (Nat.lt_succ_self _)).set
        (r := rr) (v := .native vr) (Nat.le_refl _) (Nat.lt_succ_self _)
    refine ⟨?_, ?_, ?_, by omega, hv₁, ?_⟩
    · exact hm₁.trans ((MemEq.set (Nat.le_refl _)).trans (MemEq.set (Nat.le_succ _))
        (Nat.le_refl _)) hle₁
    · exact (hi₂.memo_cons (heval false) hr (hclosed false)).memo_cons (heval true) hq
        (hclosed true)
    · cases quot <;> simpa using (by assumption)
    · intro v hv
      have := hb₁ v (by simpa [Expr.vars] using hv)
      simpa using this

/-! ### The operations, one instruction each -/

/-- Decoding two operands. -/
theorem natives_two {m : Memory} {a b : Operand} {vs : List Fr} (h : natives m [a, b] = some vs) :
    ∃ x y, native m a = some x ∧ native m b = some y ∧ vs = [x, y] := by
  obtain ⟨x, xs, hx, hxs, rfl⟩ := natives_cons_inv h
  obtain ⟨y, ys, hy, hys, rfl⟩ := natives_cons_inv hxs
  cases hys
  exact ⟨x, y, hx, hy, rfl⟩

/-- A binary operation on a two-element list of values. -/
def bin (g : Fr → Fr → Option Fr) : List Fr → Option Fr
  | [x, y] => g x y
  | _ => none

/-! ### The expression lemma -/

mutual
/-- The code emitted for an expression computes its value (`Spec1`). -/
theorem expr_spec (p : Prims) : ∀ (e : Expr) (hint : String) (s : State) (o : Operand)
    (is : List Instr) (s' : State), expr hint e s = .ok (o, is, s') → Spec1 p e s o is s'
  | .var v, _, s, o, is, s', h => by
      simp only [expr] at h
      split at h
      · next o' hv => cases h; exact spec1_var hv
      · cases h
  | .const c, _, s, o, is, s', h => by
      simp only [expr] at h; cases h; exact spec1_const p c s
  | .invalid _, _, _, _, _, _, h => by simp only [expr] at h; cases h
  | .disclose e, hint, s, o, is, s', h => by
      simp only [expr] at h; exact (expr_spec p e hint s o is s' h).disclose
  | .add a b, hint, s, o, is, s', h => by
      simp only [expr] at h
      split at h
      · next o' hm => cases h; exact spec1_memo hm
      split at h
      · cases h
      next a' is1 s1 ha =>
      split at h
      · cases h
      next b' is2 s2 hb =>
      simp only [Except.ok.injEq] at h
      have := spec1_finish (e := .add a b) (hint := hint) (xs := [a, b]) (os := [a', b'])
        (mk := fun x => Instr.add x a' b') (f := bin fun x y => some (x + y))
        ((expr_spec p a "t" s a' is1 s1 ha).spec.append (expr_spec p b "t" s1 b' is2 s2 hb).spec)
        (fun env => by
          cases ha' : a.eval p env <;> cases hb' : b.eval p env <;>
            simp [Expr.eval, Expr.evalList, ha', hb', bin])
        (by simp [Expr.vars, Expr.varsList])
        (fun σ out vs hn => by
          obtain ⟨x, y, hx, hy, rfl⟩ := natives_two hn
          simp [Zkir.Instr.step, hx, hy, resolve_of_native hx, resolve_of_native hy, bin])
      rw [h] at this; exact this
  | .mul a b, hint, s, o, is, s', h => by
      simp only [expr] at h
      split at h
      · next o' hm => cases h; exact spec1_memo hm
      split at h
      · cases h
      next a' is1 s1 ha =>
      split at h
      · cases h
      next b' is2 s2 hb =>
      simp only [Except.ok.injEq] at h
      have := spec1_finish (e := .mul a b) (hint := hint) (xs := [a, b]) (os := [a', b'])
        (mk := fun x => Instr.mul x a' b') (f := bin fun x y => some (x * y))
        ((expr_spec p a "t" s a' is1 s1 ha).spec.append (expr_spec p b "t" s1 b' is2 s2 hb).spec)
        (fun env => by
          cases ha' : a.eval p env <;> cases hb' : b.eval p env <;>
            simp [Expr.eval, Expr.evalList, ha', hb', bin])
        (by simp [Expr.vars, Expr.varsList])
        (fun σ out vs hn => by
          obtain ⟨x, y, hx, hy, rfl⟩ := natives_two hn
          simp [Zkir.Instr.step, hx, hy, resolve_of_native hx, resolve_of_native hy, bin])
      rw [h] at this; exact this
  | .eq a b, hint, s, o, is, s', h => by
      simp only [expr] at h
      split at h
      · next o' hm => cases h; exact spec1_memo hm
      split at h
      · cases h
      next a' is1 s1 ha =>
      split at h
      · cases h
      next b' is2 s2 hb =>
      simp only [Except.ok.injEq] at h
      have := spec1_finish (e := .eq a b) (hint := hint) (xs := [a, b]) (os := [a', b'])
        (mk := fun x => Instr.testEq x a' b') (f := bin fun x y => some (Fr.ofBool (x = y)))
        ((expr_spec p a "t" s a' is1 s1 ha).spec.append (expr_spec p b "t" s1 b' is2 s2 hb).spec)
        (fun env => by
          cases ha' : a.eval p env <;> cases hb' : b.eval p env <;>
            simp [Expr.eval, Expr.evalList, ha', hb', bin])
        (by simp [Expr.vars, Expr.varsList])
        (fun σ out vs hn => by
          obtain ⟨x, y, hx, hy, rfl⟩ := natives_two hn
          simp [Zkir.Instr.step, hx, hy, resolve_of_native hx, resolve_of_native hy, bin])
      rw [h] at this; exact this
  | .lt bits a b, hint, s, o, is, s', h => by
      simp only [expr] at h
      split at h
      · next o' hm => cases h; exact spec1_memo hm
      split at h
      · cases h
      next a' is1 s1 ha =>
      split at h
      · cases h
      next b' is2 s2 hb =>
      simp only [Except.ok.injEq] at h
      have := spec1_finish (e := .lt bits a b) (hint := hint) (xs := [a, b]) (os := [a', b'])
        (mk := fun x => Instr.lessThan x a' b' bits)
        (f := bin fun x y =>
          if Zkir.fitsBits x bits && Zkir.fitsBits y bits then some (Fr.ofBool (x.val < y.val)) else none)
        ((expr_spec p a "t" s a' is1 s1 ha).spec.append (expr_spec p b "t" s1 b' is2 s2 hb).spec)
        (fun env => by
          cases ha' : a.eval p env <;> cases hb' : b.eval p env <;>
            simp [Expr.eval, Expr.evalList, ha', hb', bin])
        (by simp [Expr.vars, Expr.varsList])
        (fun σ out vs hn => by
          obtain ⟨x, y, hx, hy, rfl⟩ := natives_two hn
          simp only [Zkir.Instr.step, hx, hy, bin]
          split <;> simp_all)
      rw [h] at this; exact this
  | .neg a, hint, s, o, is, s', h => by
      simp only [expr] at h
      split at h
      · next o' hm => cases h; exact spec1_memo hm
      split at h
      · cases h
      next a' is1 s1 ha =>
      simp only [Except.ok.injEq] at h
      have := spec1_finish (e := .neg a) (hint := hint) (xs := [a]) (os := [a'])
        (mk := fun x => Instr.neg x a') (f := fun | [x] => some (-x) | _ => none)
        (expr_spec p a "t" s a' is1 s1 ha).spec
        (fun env => by cases ha' : a.eval p env <;> simp [Expr.eval, Expr.evalList, ha'])
        (by simp [Expr.vars, Expr.varsList])
        (fun σ out vs hn => by
          obtain ⟨x, hx, rfl⟩ := natives_single.1 hn; simp [Zkir.Instr.step, hx])
      rw [h] at this; exact this
  | .select c a b, hint, s, o, is, s', h => by
      simp only [expr] at h
      split at h
      · next o' hm => cases h; exact spec1_memo hm
      split at h
      · cases h
      next c' is0 s0 hc =>
      split at h
      · cases h
      next a' is1 s1 ha =>
      split at h
      · cases h
      next b' is2 s2 hb =>
      simp only [Except.ok.injEq] at h
      have := spec1_finish (e := .select c a b) (hint := hint) (xs := [c, a, b]) (os := [c', a', b'])
        (mk := fun x => Instr.condSelect x c' a' b')
        (f := fun
          | [k, x, y] => (asBool k).map fun k => if k then x else y
          | _ => none)
        (((expr_spec p c "t" s c' is0 s0 hc).spec.append
          (expr_spec p a "t" s0 a' is1 s1 ha).spec).append (expr_spec p b "t" s1 b' is2 s2 hb).spec)
        (fun env => by
          cases hc' : c.eval p env <;> cases ha' : a.eval p env <;> cases hb' : b.eval p env <;>
            simp [Expr.eval, Expr.evalList, hc', ha', hb']
          rename_i k _ _
          cases asBool k <;> rfl)
        (by simp [Expr.vars, Expr.varsList])
        (fun σ out vs hn => by
          obtain ⟨k, xs, hk, hxs, rfl⟩ := natives_cons_inv hn
          obtain ⟨x, y, hx, hy, rfl⟩ := natives_two hxs
          simp only [Zkir.Instr.step, bool_of_native hk]
          cases asBool k <;> simp [resolve_of_native hx, resolve_of_native hy])
      rw [h] at this; exact this
  | .hash xs, hint, s, o, is, s', h => by
      simp only [expr] at h
      split at h
      · next o' hm => cases h; exact spec1_memo hm
      split at h
      · cases h
      next xs' is1 s1 hxs =>
      simp only [Except.ok.injEq] at h
      have := spec1_finish (e := .hash xs) (hint := hint) (xs := xs) (os := xs')
        (mk := fun x => Instr.transientHash x xs') (f := fun vs => some (p.transientHash vs))
        (exprs_spec p xs s xs' is1 s1 hxs)
        (fun env => by cases hx : Expr.evalList p env xs <;> simp [Expr.eval, hx])
        (by simp [Expr.vars])
        (fun σ out vs hn => by simp [Zkir.Instr.step, hn])
      rw [h] at this; exact this
  | .phash high align xs, hint, s, o, is, s', h => by
      simp only [expr] at h
      split at h
      · next o' hm => cases h; exact spec1_memo hm
      split at h
      · cases h
      next xs' is1 s1 hxs =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact spec1_phash (exprs_spec p xs s xs' is1 s1 hxs)
  | .divmod quot bits a, hint, s, o, is, s', h => by
      simp only [expr] at h
      split at h
      · next o' hm => cases h; exact spec1_memo hm
      split at h
      · cases h
      next a' is1 s1 ha =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact spec1_divmod (expr_spec p a "t" s a' is1 s1 ha)

/-- The code emitted for a list of expressions computes their values (`Spec`). -/
theorem exprs_spec (p : Prims) : ∀ (xs : List Expr) (s : State) (os : List Operand)
    (is : List Instr) (s' : State), exprs xs s = .ok (os, is, s') → Spec p xs s os is s'
  | [], s, os, is, s', h => by simp only [exprs] at h; cases h; exact Spec.nil p s
  | x :: xs, s, os, is, s', h => by
      simp only [exprs] at h
      split at h
      · cases h
      next x' is1 s1 hx =>
      split at h
      · cases h
      next xs' is2 s2 hxs =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact (expr_spec p x "t" s x' is1 s1 hx).spec.append (exprs_spec p xs s1 xs' is2 s2 hxs)
end

/-! ## Range checks -/

/-- The instructions checking a range fail exactly when the value is out of
    range, and otherwise change only fresh registers. -/
theorem resolve_imm (m : Memory) (c : Int) : resolve m (.imm c) = some (.native (Fr.ofInt c)) := rfl

/-- The instructions checking a range fail exactly when the value is out of
    range, and otherwise change only fresh registers. -/
theorem constrain_spec {p : Prims} {o : Operand} {r : Range} {s s' : State} {cs : List Instr}
    {env : Env} {σ : Zkir.State} {x : Fr} (h : constrain o r s = (cs, s'))
    (hinv : Inv p s env σ.mem) (ho : native σ.mem o = some x) :
    (r.holds x = false → exec p cs σ = none) ∧
    (r.holds x = true → ∃ m', exec p cs σ = some { σ with mem := m' } ∧ MemEq s.next σ.mem m' ∧
      Inv p s' env m' ∧ s.next ≤ s'.next) := by
  have hr := resolve_of_native ho
  cases r with
  | zero =>
    simp only [constrain, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨fun hf => ?_, fun ht => ⟨σ.mem, ?_, MemEq.refl _ _, hinv, Nat.le_refl _⟩⟩
    · simp only [Range.holds, decide_eq_false_iff_not] at hf
      simp [exec_single, Zkir.Instr.step, hr, resolve_imm, Fr.ofInt_zero, hf]
    · simp only [Range.holds, decide_eq_true_eq] at ht
      simp [exec_single, Zkir.Instr.step, hr, resolve_imm, Fr.ofInt_zero, ht]
  | bool =>
    simp only [constrain, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨fun hf => ?_, fun ht => ⟨σ.mem, ?_, MemEq.refl _ _, hinv, Nat.le_refl _⟩⟩
    · simp only [Range.holds, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hf
      simp [exec_single, Zkir.Instr.step, bool_of_native ho, asBool, hf.1, hf.2]
    · simp only [Range.holds, Bool.or_eq_true, decide_eq_true_eq] at ht
      rcases ht with h0 | h1
      · simp [exec_single, Zkir.Instr.step, bool_of_native ho, asBool, h0]
      · simp [exec_single, Zkir.Instr.step, bool_of_native ho, asBool, h1, Fr.zero_ne_one.symm]
  | bits n =>
    simp only [constrain, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨fun hf => ?_, fun ht => ⟨σ.mem, ?_, MemEq.refl _ _, hinv, Nat.le_refl _⟩⟩
    · simp only [Range.holds] at hf
      simp [exec_single, Zkir.Instr.step, ho, hf]
    · simp only [Range.holds] at ht
      simp [exec_single, Zkir.Instr.step, ho, ht]
  | below bound width =>
    simp only [constrain, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hb : native σ.mem (.imm (bound : Int)) = some (Fr.ofInt bound) := rfl
    have ht : ∀ v, native (σ.mem.set ⟨"tmp", s.next⟩ (.native v)) (.var ⟨"tmp", s.next⟩) = some v := by
      intro v; rw [native_var]; simp [Zkir.Memory.set]
    have htb : ∀ v, Zkir.bool (σ.mem.set ⟨"tmp", s.next⟩ (.native v)) (.var ⟨"tmp", s.next⟩) =
        asBool v := fun v => bool_of_native (ht v)
    have hfresh : MemEq s.next σ.mem (σ.mem.set ⟨"tmp", s.next⟩ (.native
        (Fr.ofBool (decide (x.val < (Fr.ofInt bound).val))))) := MemEq.set (Nat.le_refl _)
    refine ⟨fun hf => ?_, fun ht' => ⟨_, ?_, hfresh,
      hinv.set (r := ⟨"tmp", s.next⟩) (Nat.le_refl _) (Nat.lt_succ_self _), Nat.le_succ _⟩⟩
    · simp only [Range.holds, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hf
      simp only [Zkir.exec, Zkir.Instr.step, ho, hb, htb, asBool_ofBool]
      rcases hf with hf | hf <;> simp [hf] <;> intro _ _ <;> rw [htb, asBool_ofBool] <;> simp_all
    · simp only [Range.holds, Bool.and_eq_true, decide_eq_true_eq] at ht'
      simp [Zkir.exec, Zkir.Instr.step, ho, hb, htb, asBool_ofBool, ht']

/-! ## Reading the transcripts -/

/-- The input instruction reading the private (`true`) or public (`false`) transcript. -/
def inputInstr : Bool → Ident → Option Operand → Instr
  | true, o, g => .privateInput .native o g
  | false, o, g => .publicInput .native o g

/-- The transcript an input instruction reads. -/
def getS : Bool → Zkir.State → List Fr
  | true, σ => σ.priv
  | false, σ => σ.pub

/-- A state with a new memory and a new remainder of that transcript. -/
def putS : Bool → Zkir.State → Memory → List Fr → Zkir.State
  | true, σ, m, l => { σ with mem := m, priv := l }
  | false, σ, m, l => { σ with mem := m, pub := l }

@[simp] theorem getS_putS (b : Bool) (σ : Zkir.State) (m : Memory) (l : List Fr) :
    getS b (putS b σ m l) = l := by cases b <;> rfl

@[simp] theorem putS_putS (b : Bool) (σ : Zkir.State) (m m' : Memory) (l l' : List Fr) :
    putS b (putS b σ m l) m' l' = putS b σ m' l' := by cases b <;> rfl

@[simp] theorem putS_mem (b : Bool) (σ : Zkir.State) (m : Memory) (l : List Fr) :
    (putS b σ m l).mem = m := by cases b <;> rfl

@[simp] theorem putS_with_mem (b : Bool) (σ : Zkir.State) (m m' : Memory) (l : List Fr) :
    { putS b σ m l with mem := m' } = putS b σ m' l := by cases b <;> rfl

/-- An input instruction: check the guard, read one value (or a default), store it. -/
theorem step_input (p : Prims) (b : Bool) (σ : Zkir.State) (out : Ident) (g : Option Operand) :
    (inputInstr b out g).step p σ = (evalGuard σ.mem g).bind fun active =>
      (readOne active (getS b σ)).map fun r => putS b σ (σ.mem.set out (.native r.1)) r.2 := by
  cases b <;> simp [inputInstr, Zkir.Instr.step, getS, putS] <;>
    cases evalGuard σ.mem g <;> simp <;> rename_i a <;> cases readOne a _ <;> rfl

/-- Binding a variable succeeds only when it is unbound, and records its register. -/
theorem bindVar_ok {v : Var} {o : Operand} {s s' : State} (h : bindVar v o s = .ok s') :
    s.vars.lookup v = none ∧ s' = { s with vars := (v, o) :: s.vars } := by
  simp only [bindVar] at h
  split at h
  · cases h
  · next hn =>
    cases h
    refine ⟨?_, rfl⟩
    cases hl : s.vars.lookup v
    · rfl
    · simp [hl] at hn

/-- Whether a value passes an optional range check. -/
def rangeOk (x : Fr) : Option Range → Bool
  | some r => r.holds x
  | none => true

/-- The optional range check after a read, as `reads` emits it. -/
def rangeCheck (o : Operand) (s : State) : Option Range → List Instr × State
  | some r => constrain o r s
  | none => ([], s)

/-- `reads`, one step, with the range check named. -/
theorem reads_cons (mk : Ident → Instr) (v : Var) (range : Option Range)
    (rest : List (Var × Option Range)) (s : State) :
    reads mk ((v, range) :: rest) s =
      match bindVar v (.var ⟨"t", s.next⟩) { s with next := s.next + 1 } with
      | .error m => .error m
      | .ok s₁ =>
        match reads mk rest (rangeCheck (.var ⟨"t", s.next⟩) s₁ range).2 with
        | .error m => .error m
        | .ok ((), is, s₃) =>
            .ok ((), mk ⟨"t", s.next⟩ :: (rangeCheck (.var ⟨"t", s.next⟩) s₁ range).1 ++ is, s₃) := by
  simp only [reads]
  cases range <;> rfl

/-- The optional range check after a read, on both sides. -/
theorem optConstrain_spec {p : Prims} {range : Option Range} {o : Operand} {s s' : State}
    {cs : List Instr} {env : Env} {σ : Zkir.State} {x : Fr}
    (h : rangeCheck o s range = (cs, s'))
    (hinv : Inv p s env σ.mem) (ho : native σ.mem o = some x) :
    (rangeOk x range = false → exec p cs σ = none) ∧
    (rangeOk x range = true → ∃ m', exec p cs σ = some { σ with mem := m' } ∧
      MemEq s.next σ.mem m' ∧ Inv p s' env m' ∧ s.next ≤ s'.next) := by
  cases range with
  | some r => exact constrain_spec h hinv ho
  | none =>
    simp only [rangeCheck, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun hf => by simp [rangeOk] at hf, fun _ => ⟨σ.mem, rfl, MemEq.refl _ _, hinv, Nat.le_refl _⟩⟩

/-- `IR.readAll`, one step, with the range check as `rangeOk`. -/
theorem readAll_cons (active : Bool) (env : Env) (v : Var) (range : Option Range)
    (rest : List (Var × Option Range)) (l : List Fr) :
    readAll active env ((v, range) :: rest) l =
      (readOne active l).bind fun r =>
        if rangeOk r.1 range then readAll active (env.set v r.1) rest r.2 else none := by
  simp only [readAll]
  cases readOne active l with
  | none => rfl
  | some r => cases range <;> simp [rangeOk] <;> split <;> simp_all

/-- The reads of a `witness` or `ledger` statement: one input instruction per
    variable, each followed by its range check, against `IR.readAll`. The guard
    must read the same in every memory that keeps the registers written so far. -/
theorem reads_spec (p : Prims) (b : Bool) (g : Option Operand) (active : Bool) :
    ∀ (outs : List (Var × Option Range)) (s s' : State) (is : List Instr) (env : Env) (m : Memory)
      (l : List Fr) (σ : Zkir.State),
    reads (fun o => inputInstr b o g) outs s = .ok ((), is, s') → Inv p s env m →
    (∀ m', MemEq s.next m m' → evalGuard m' g = some active) →
    (readAll active env outs l = none → exec p is (putS b σ m l) = none) ∧
    ∀ env' l', readAll active env outs l = some (env', l') →
      ∃ m', exec p is (putS b σ m l) = some (putS b σ m' l') ∧ MemEq s.next m m' ∧
        Inv p s' env' m' ∧ s.next ≤ s'.next
  | [], s, s', is, env, m, l, σ, h, hinv, _ => by
      simp only [reads, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl⟩ := h
      refine ⟨fun hn => by simp [readAll] at hn, fun env' l' he => ?_⟩
      simp only [readAll, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨m, rfl, MemEq.refl _ _, hinv, Nat.le_refl _⟩
  | (v, range) :: rest, s, s', is, env, m, l, σ, h, hinv, hg => by
      rw [reads_cons] at h
      split at h
      · cases h
      next s₁ hbind =>
      generalize hc : rangeCheck (.var ⟨"t", s.next⟩) s₁ range = c at h
      obtain ⟨cs, s₂⟩ := c
      obtain ⟨hfree, rfl⟩ := bindVar_ok hbind
      split at h
      · cases h
      next is' s₃ hrest =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl⟩ := h
      rw [readAll_cons, List.cons_append]
      simp only [Zkir.exec, step_input, putS_mem, hg m (MemEq.refl _ _), Option.bind_some, getS_putS]
      cases hr : readOne active l with
      | none => simp
      | some r =>
      obtain ⟨x, l₁⟩ := r
      simp only [Option.map_some, Option.bind_some, putS_putS]
      have ho : native (m.set ⟨"t", s.next⟩ (.native x)) (.var ⟨"t", s.next⟩) = some x := by
        simp [native_var, Zkir.Memory.set]
      have hi₁ := (hinv.set (r := ⟨"t", s.next⟩) (v := .native x) (Nat.le_refl _)
        (Nat.lt_succ_self _)).bind (v := v) hfree ho
      obtain ⟨cf, ck⟩ := optConstrain_spec (σ := putS b σ (m.set ⟨"t", s.next⟩ (.native x)) l₁) hc
        (by simpa using hi₁) (by simpa using ho)
      dsimp only at hrest
      simp only [Bind.bind, Option.bind_some, exec_append]
      cases hok : rangeOk x range
      · simp [cf hok]
      obtain ⟨m₂, he₂, hm₂, hi₂, hle₂⟩ := ck hok
      simp only [ite_true, he₂, putS_with_mem, Option.bind_some]
      have hm₂' : MemEq s.next m m₂ :=
        (MemEq.set (r := ⟨"t", s.next⟩) (v := .native x) (Nat.le_refl _)).trans
          (n' := s.next + 1) (by simpa using hm₂) (Nat.le_succ _)
      have hle₂' : s.next ≤ s₂.next := Nat.le_of_succ_le hle₂
      obtain ⟨rf, rk⟩ := reads_spec p b g active rest s₂ s₃ is' (env.set v x) m₂ l₁ σ hrest hi₂
        (fun m' hm => hg m' (hm₂'.trans hm hle₂'))
      refine ⟨rf, fun env' l' he => ?_⟩
      obtain ⟨m₃, he₃, hm₃, hi₃, hle₃⟩ := rk env' l' he
      exact ⟨m₃, he₃, hm₂'.trans hm₃ hle₂', hi₃, Nat.le_trans hle₂' hle₃⟩

/-- With something to read and a guard that is not a boolean, the reads fail. -/
theorem reads_fail (p : Prims) (b : Bool) (g : Option Operand) {outs : List (Var × Option Range)}
    {s s' : State} {is : List Instr} {σ : Zkir.State}
    (h : reads (fun o => inputInstr b o g) outs s = .ok ((), is, s')) (hne : outs ≠ [])
    (hg : evalGuard σ.mem g = none) : exec p is σ = none := by
  cases outs with
  | nil => exact absurd rfl hne
  | cons out rest =>
    obtain ⟨v, range⟩ := out
    rw [reads_cons] at h
    split at h
    · cases h
    split at h
    · cases h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, rfl⟩ := h
    simp [exec_append, Zkir.exec, step_input, hg]

/-- A guard operand, printed as "no guard" when it is literally 1, reads as the
    guard's value does under `asBool`. -/
theorem evalGuard_optGuard {m : Memory} {g : Operand} {x : Fr} (h : native m g = some x) :
    evalGuard m (optGuard g) = asBool x := by
  cases g with
  | var r => exact bool_of_native h
  | imm c =>
    rw [native_imm, Option.some.injEq] at h
    subst h
    by_cases hc : c = 1
    · subst hc
      simp [optGuard, evalGuard, asBool, Fr.ofInt_one, Fr.zero_ne_one.symm]
    · have : optGuard (.imm c) = some (.imm c) := by
        unfold optGuard; split
        · next heq => cases heq; exact absurd rfl hc
        · rfl
      rw [this]
      exact bool_of_native (m := m) (o := .imm c) rfl

/-! ## Ledger operands and public inputs -/

/-- Values of lists of expressions, all or nothing. -/
def evalLists (p : Prims) (env : Env) : List (List Expr) → Option (List (List Fr))
  | [] => some []
  | xs :: rest => do
      let v ← Expr.evalList p env xs
      let r ← evalLists p env rest
      pure (v :: r)

/-- Values of lists of native operands, all or nothing. -/
def nativesL (m : Memory) : List (List Operand) → Option (List (List Fr))
  | [] => some []
  | os :: rest => do
      let v ← natives m os
      let r ← nativesL m rest
      pure (v :: r)

/-- `native_stable` for lists of operand lists. -/
theorem nativesL_stable {n : Nat} {m m' : Memory} (hf : Fresh n m) (he : MemEq n m m') :
    ∀ {oss : List (List Operand)} {vss : List (List Fr)}, nativesL m oss = some vss →
      nativesL m' oss = some vss
  | [], _, h => h
  | os :: rest, vss, h => by
      cases hx : natives m os <;> cases hys : nativesL m rest <;> simp_all [nativesL]
      rename_i x ys
      subst h
      simp [natives_stable hf he hx, nativesL_stable hf he hys]

/-- The code for the operands of a ledger statement's instructions computes them. -/
theorem operands_spec (p : Prims) :
    ∀ (xss : List (List Expr)) (s s' : State) (oss : List (List Operand)) (is : List Instr)
      (env : Env) (σ : Zkir.State), operands xss s = .ok (oss, is, s') → Inv p s env σ.mem →
    (evalLists p env xss = none → exec p is σ = none) ∧
    ∀ vss, evalLists p env xss = some vss →
      ∃ m', exec p is σ = some { σ with mem := m' } ∧ MemEq s.next σ.mem m' ∧ Inv p s' env m' ∧
        nativesL m' oss = some vss ∧ s.next ≤ s'.next
  | [], s, s', oss, is, env, σ, h, hinv => by
      simp only [operands, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨fun hn => by simp [evalLists] at hn, fun vss hv => ?_⟩
      simp only [evalLists, Option.some.injEq] at hv
      subst hv
      exact ⟨σ.mem, rfl, MemEq.refl _ _, hinv, rfl, Nat.le_refl _⟩
  | xs :: rest, s, s', oss, is, env, σ, h, hinv => by
      simp only [operands] at h
      split at h
      · cases h
      next os is₁ s₁ hxs =>
      split at h
      · cases h
      next oss' is₂ s₂ hrest =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨f₁, k₁⟩ := exprs_spec p xs s os is₁ s₁ hxs env σ hinv
      rw [exec_append]
      simp only [evalLists]
      cases hx : Expr.evalList p env xs with
      | none => simp [f₁ hx]
      | some v =>
      obtain ⟨m₁, he₁, hm₁, hi₁, hn₁, hle₁, -, -⟩ := k₁ v hx
      obtain ⟨f₂, k₂⟩ := operands_spec p rest s₁ s₂ oss' is₂ env { σ with mem := m₁ } hrest hi₁
      simp only [he₁, Option.bind_some]
      cases hr : evalLists p env rest with
      | none => simp [f₂ hr]
      | some r =>
      obtain ⟨m₂, he₂, hm₂, hi₂, hn₂, hle₂⟩ := k₂ r hr
      refine ⟨fun hn => by simp at hn, fun vss hv => ?_⟩
      simp only [hx, hr, Option.bind_some, Option.pure_def, Option.some.injEq] at hv
      simp at hv
      subst hv
      refine ⟨m₂, he₂, hm₁.trans hm₂ hle₁, hi₂, ?_, Nat.le_trans hle₁ hle₂⟩
      simp [nativesL, natives_stable hi₁.fresh hm₂ hn₁, hn₂]

/-- The group of public inputs one `impact` declares. -/
def group (active : Bool) (vs : List Fr) : Zkir.Group :=
  { active, vals := if active then vs else vs.map fun _ => 0 }

/-- Zeros, one per operand, are zeros, one per value. -/
theorem map_zero_of_natives {m : Memory} {os : List Operand} {vs : List Fr}
    (h : natives m os = some vs) : os.map (fun _ => (0 : Fr)) = vs.map fun _ => 0 := by
  have hl := natives_length h
  clear h
  induction os generalizing vs with
  | nil => cases vs with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons o os ih => cases vs with
    | nil => simp at hl
    | cons v vs => simp only [List.map_cons, ih (by simpa using hl)]

/-- The `impact` instructions declare one group per ledger instruction. -/
theorem exec_impacts (p : Prims) (g : Operand) (active : Bool) :
    ∀ (oss : List (List Operand)) (vss : List (List Fr)) (σ : Zkir.State),
    Zkir.bool σ.mem g = some active → nativesL σ.mem oss = some vss →
    exec p (oss.map (Instr.impact g)) σ =
      some { σ with groups := σ.groups ++ vss.map (group active) }
  | [], vss, σ, _, h => by
      simp only [nativesL, Option.some.injEq] at h
      subst h
      simp [Zkir.exec]
  | os :: rest, vss, σ, hg, h => by
      cases hx : natives σ.mem os <;> cases hys : nativesL σ.mem rest <;> simp_all [nativesL]
      rename_i vs r
      subst h
      have ih := exec_impacts p g active rest r
        { σ with groups := σ.groups ++ [group active vs] } hg hys
      have hstep : (Instr.impact g os).step p σ =
          some { σ with groups := σ.groups ++ [group active vs] } := by
        cases active <;> simp [Zkir.Instr.step, hg, hx, group, map_zero_of_natives hx]
      simp only [Zkir.exec, hstep, Bind.bind, Option.bind_some, ih]
      simp

/-- The groups a ledger statement declares, through `evalLists`. -/
theorem ledgerGroups_eq (p : Prims) (env : Env) (active : Bool) :
    ∀ ops : List (Impact.Op Expr), ledgerGroups p env active ops =
      (evalLists p env (ops.map fun op => op.encode Expr.const)).map fun vss => vss.map (group active)
  | [] => rfl
  | op :: ops => by
      simp only [ledgerGroups, List.map_cons, evalLists, ledgerGroups_eq p env active ops]
      cases Expr.evalList p env (op.encode Expr.const) <;>
        cases evalLists p env (ops.map fun op => op.encode Expr.const) <;> rfl

/-! ## Statements -/

/-- An IR run state and a ZKIR state related through an emitter state: the
    invariant, the same transcripts left and the same groups, and no outputs yet. -/
structure Rel (p : Prims) (s : State) (ρ : RunState) (σ : Zkir.State) : Prop where
  inv : Inv p s ρ.env σ.mem
  priv : σ.priv = ρ.priv
  pub : σ.pub = ρ.pub
  groups : σ.groups = ρ.groups
  outputs : σ.outputs = []

/-- Both runs fail, or both succeed in related states. -/
def Sim (p : Prims) (s : State) : Option RunState → Option Zkir.State → Prop
  | none, none => True
  | some ρ, some σ => Rel p s ρ σ
  | _, _ => False

/-- `bind`: the expression's register becomes the variable's. -/
theorem stmt_bind {p : Prims} {v : Var} {hint : String} {e : Expr} {s s' : State} {is : List Instr}
    {ρ : RunState} {σ : Zkir.State} (h : stmt (.bind v hint e) s = .ok ((), is, s'))
    (hr : Rel p s ρ σ) : Sim p s' ((Stmt.bind v hint e).exec p ρ) (exec p is σ) := by
  simp only [stmt] at h
  split at h
  · cases h
  next o is₁ s₁ he =>
  split at h
  · cases h
  next s₂ hb =>
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl, rfl⟩ := h
  obtain ⟨hfree, rfl⟩ := bindVar_ok hb
  obtain ⟨f, k⟩ := expr_spec p e hint s o is₁ s₁ he ρ.env σ hr.inv
  cases hx : e.eval p ρ.env with
  | none =>
    have e₁ : (Stmt.bind v hint e).exec p ρ = none := by simp [Stmt.exec, hx]
    rw [e₁, f hx]; trivial
  | some x =>
    obtain ⟨m', he', -, hi, ho, -⟩ := k x hx
    have e₁ : (Stmt.bind v hint e).exec p ρ = some { ρ with env := ρ.env.set v x } := by
      simp [Stmt.exec, hx]
    rw [e₁, he']
    exact ⟨hi.bind hfree ho, hr.priv, hr.pub, hr.groups, hr.outputs⟩

/-- `assert`: one `assert` instruction on the condition's register. -/
theorem stmt_assert {p : Prims} {cond : Expr} {msg : String} {s s' : State} {is : List Instr}
    {ρ : RunState} {σ : Zkir.State} (h : stmt (.assert cond msg) s = .ok ((), is, s'))
    (hr : Rel p s ρ σ) : Sim p s' ((Stmt.assert cond msg).exec p ρ) (exec p is σ) := by
  simp only [stmt] at h
  split at h
  · cases h
  next o is₁ s₁ he =>
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl, rfl⟩ := h
  obtain ⟨f, k⟩ := expr_spec p cond "t" s o is₁ s₁ he ρ.env σ hr.inv
  rw [exec_append]
  cases hx : cond.eval p ρ.env with
  | none =>
    have e₁ : (Stmt.assert cond msg).exec p ρ = none := by simp [Stmt.exec, hx]
    rw [e₁, f hx]; trivial
  | some x =>
    obtain ⟨m', he', -, hi, ho, -⟩ := k x hx
    rw [he', Option.bind_some, exec_single]
    simp only [Zkir.Instr.step, bool_of_native ho]
    cases hb : asBool x with
    | none =>
      have e₁ : (Stmt.assert cond msg).exec p ρ = none := by simp [Stmt.exec, hx, hb]
      rw [e₁]; trivial
    | some c =>
      cases c
      · have e₁ : (Stmt.assert cond msg).exec p ρ = none := by simp [Stmt.exec, hx, hb]
        rw [e₁]; trivial
      · have e₁ : (Stmt.assert cond msg).exec p ρ = some ρ := by simp [Stmt.exec, hx, hb]
        rw [e₁]
        exact ⟨hi, hr.priv, hr.pub, hr.groups, hr.outputs⟩

/-- `constrain`: the range check on the expression's register. -/
theorem stmt_constrain {p : Prims} {e : Expr} {r : Range} {s s' : State} {is : List Instr}
    {ρ : RunState} {σ : Zkir.State} (h : stmt (.constrain e r) s = .ok ((), is, s'))
    (hr : Rel p s ρ σ) : Sim p s' ((Stmt.constrain e r).exec p ρ) (exec p is σ) := by
  simp only [stmt] at h
  split at h
  · cases h
  next o is₁ s₁ he =>
  generalize hc : constrain o r s₁ = c at h
  obtain ⟨cs, s₂⟩ := c
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl, rfl⟩ := h
  obtain ⟨f, k⟩ := expr_spec p e "t" s o is₁ s₁ he ρ.env σ hr.inv
  rw [exec_append]
  cases hx : e.eval p ρ.env with
  | none =>
    have e₁ : (Stmt.constrain e r).exec p ρ = none := by simp [Stmt.exec, hx]
    rw [e₁, f hx]; trivial
  | some x =>
    obtain ⟨m', he', -, hi, ho, -⟩ := k x hx
    rw [he', Option.bind_some]
    obtain ⟨cf, ck⟩ := constrain_spec (σ := { σ with mem := m' }) hc hi ho
    cases hh : r.holds x
    · have e₁ : (Stmt.constrain e r).exec p ρ = none := by simp [Stmt.exec, hx, hh]
      rw [e₁, cf hh]; trivial
    · obtain ⟨m'', he'', -, hi', -⟩ := ck hh
      have e₁ : (Stmt.constrain e r).exec p ρ = some ρ := by simp [Stmt.exec, hx, hh]
      rw [e₁, he'']
      exact ⟨hi', hr.priv, hr.pub, hr.groups, hr.outputs⟩

/-- `witness`: the guard, then one `private_input` per output with its range check. -/
theorem stmt_witness {p : Prims} {guard : Expr} {name : String} {args : List Expr}
    {outs : List (Var × Option Range)} {shape : Shape} {s s' : State} {is : List Instr}
    {ρ : RunState} {σ : Zkir.State} (h : stmt (.witness guard name args outs shape) s = .ok ((), is, s'))
    (hr : Rel p s ρ σ) :
    Sim p s' ((Stmt.witness guard name args outs shape).exec p ρ) (exec p is σ) := by
  simp only [stmt] at h
  split at h
  · cases h
  next g is₁ s₁ he =>
  split at h
  · cases h
  next rs s₂ hreads =>
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl, rfl⟩ := h
  obtain ⟨f, k⟩ := expr_spec p guard "t" s g is₁ s₁ he ρ.env σ hr.inv
  rw [exec_append]
  cases hx : guard.eval p ρ.env with
  | none =>
    have e₁ : (Stmt.witness guard name args outs shape).exec p ρ = none := by simp [Stmt.exec, hx]
    rw [e₁, f hx]; trivial
  | some gv =>
  obtain ⟨m₁, he₁, -, hi₁, hg, -⟩ := k gv hx
  rw [he₁, Option.bind_some]
  have hσ : ({ σ with mem := m₁ } : Zkir.State) = putS true σ m₁ ρ.priv := by
    rw [← hr.priv]; rfl
  cases outs with
  | nil =>
    simp only [reads, Except.ok.injEq, Prod.mk.injEq] at hreads
    obtain ⟨-, rfl, rfl⟩ := hreads
    have e₁ : (Stmt.witness guard name args [] shape).exec p ρ = some ρ := by simp [Stmt.exec, hx]
    rw [e₁]
    exact ⟨hi₁, hr.priv, hr.pub, hr.groups, hr.outputs⟩
  | cons out rest =>
  cases ha : asBool gv with
  | none =>
    have e₁ : (Stmt.witness guard name args (out :: rest) shape).exec p ρ = none := by
      simp [Stmt.exec, hx, ha]
    rw [e₁, reads_fail p true (optGuard g) hreads (List.cons_ne_nil _ _)
      (by rw [evalGuard_optGuard hg, ha])]
    trivial
  | some active =>
  obtain ⟨rf, rk⟩ := reads_spec p true (optGuard g) active (out :: rest) s₁ s₂ rs ρ.env m₁ ρ.priv σ
    hreads hi₁ (fun m' hm => by rw [evalGuard_optGuard (native_stable hg hi₁.fresh hm), ha])
  rw [hσ]
  cases hra : readAll active ρ.env (out :: rest) ρ.priv with
  | none =>
    have e₁ : (Stmt.witness guard name args (out :: rest) shape).exec p ρ = none := by
      simp [Stmt.exec, hx, ha, hra]
    rw [e₁, rf hra]; trivial
  | some r =>
    obtain ⟨env', l'⟩ := r
    obtain ⟨m', he', -, hi', -⟩ := rk env' l' hra
    have e₁ : (Stmt.witness guard name args (out :: rest) shape).exec p ρ =
        some { ρ with env := env', priv := l' } := by
      simp [Stmt.exec, hx, ha, hra]
    rw [e₁, he']
    exact ⟨hi', rfl, hr.pub, hr.groups, hr.outputs⟩

/-- `ledger`: the guard, one `public_input` per read, the operands of every
    instruction, then one `impact` per instruction. -/
theorem stmt_ledger {p : Prims} {guard : Expr} {rds : List Var} {ops : List (Impact.Op Expr)}
    {s s' : State} {is : List Instr} {ρ : RunState} {σ : Zkir.State}
    (h : stmt (.ledger guard rds ops) s = .ok ((), is, s')) (hr : Rel p s ρ σ) :
    Sim p s' ((Stmt.ledger guard rds ops).exec p ρ) (exec p is σ) := by
  simp only [stmt] at h
  split at h
  · cases h
  next g is₁ s₁ he =>
  split at h
  · cases h
  next rs s₂ hreads =>
  split at h
  · cases h
  next oss os s₃ hops =>
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl, rfl⟩ := h
  obtain ⟨f, k⟩ := expr_spec p guard "t" s g is₁ s₁ he ρ.env σ hr.inv
  simp only [exec_append]
  cases hx : guard.eval p ρ.env with
  | none =>
    have e₁ : (Stmt.ledger guard rds ops).exec p ρ = none := by simp [Stmt.exec, hx]
    rw [e₁, f hx]; trivial
  | some gv =>
  obtain ⟨m₁, he₁, -, hi₁, hg, -⟩ := k gv hx
  rw [he₁, Option.bind_some]
  have hσ : ({ σ with mem := m₁ } : Zkir.State) = putS false σ m₁ ρ.pub := by
    rw [← hr.pub]; rfl
  by_cases hemp : rds = [] ∧ ops = []
  · obtain ⟨rfl, rfl⟩ := hemp
    simp only [List.map_nil, reads, Except.ok.injEq, Prod.mk.injEq] at hreads
    obtain ⟨-, rfl, rfl⟩ := hreads
    simp only [List.map_nil, operands, Except.ok.injEq, Prod.mk.injEq] at hops
    obtain ⟨rfl, rfl, rfl⟩ := hops
    have e₁ : (Stmt.ledger guard [] []).exec p ρ = some ρ := by simp [Stmt.exec, hx]
    rw [e₁]
    exact ⟨hi₁, hr.priv, hr.pub, hr.groups, hr.outputs⟩
  have hne : (rds.isEmpty && ops.isEmpty) = false := by
    cases rds <;> cases ops <;> simp_all
  cases ha : asBool gv with
  | none =>
    have e₁ : (Stmt.ledger guard rds ops).exec p ρ = none := by simp [Stmt.exec, hx, ha, hne]
    rw [e₁]
    by_cases hrds : rds = []
    · -- No reads, so some instruction: its `impact` reads the guard and fails.
      subst hrds
      have hops' : ops ≠ [] := fun h' => hemp ⟨rfl, h'⟩
      simp only [List.map_nil, reads, Except.ok.injEq, Prod.mk.injEq] at hreads
      obtain ⟨-, rfl, rfl⟩ := hreads
      simp only [Zkir.exec, Option.bind_some]
      obtain ⟨of, ok⟩ := operands_spec p _ s₁ s₃ oss os ρ.env { σ with mem := m₁ } hops hi₁
      cases hv : evalLists p ρ.env (ops.map fun op => op.encode Expr.const) with
      | none => rw [of hv]; trivial
      | some vss =>
        obtain ⟨m₃, he₃, hm₃, -, hn₃, -⟩ := ok vss hv
        rw [he₃, Option.bind_some]
        cases ops with
        | nil => exact absurd rfl hops'
        | cons op ops =>
        cases oss with
        | nil =>
          simp only [nativesL, Option.some.injEq] at hn₃
          subst hn₃
          simp [evalLists] at hv
          cases hq : Expr.evalList p ρ.env (op.encode Expr.const) <;>
            cases hq' : evalLists p ρ.env (ops.map fun op => op.encode Expr.const) <;> simp_all
        | cons os₁ oss =>
          have hb : Zkir.bool m₃ g = none := by
            rw [bool_of_native (native_stable hg hi₁.fresh hm₃), ha]
          simp [Zkir.exec, Zkir.Instr.step, hb, Sim]
    · rw [reads_fail p false (optGuard g) hreads (by simpa using hrds)
        (by rw [evalGuard_optGuard hg, ha])]
      trivial
  | some active =>
  obtain ⟨rf, rk⟩ := reads_spec p false (optGuard g) active (rds.map fun v => (v, none)) s₁ s₂ rs
    ρ.env m₁ ρ.pub σ hreads hi₁
    (fun m' hm => by rw [evalGuard_optGuard (native_stable hg hi₁.fresh hm), ha])
  rw [hσ]
  cases hra : readAll active ρ.env (rds.map fun v => (v, none)) ρ.pub with
  | none =>
    have e₁ : (Stmt.ledger guard rds ops).exec p ρ = none := by simp [Stmt.exec, hx, ha, hne, hra]
    rw [e₁, rf hra]; trivial
  | some r =>
  obtain ⟨env', l'⟩ := r
  obtain ⟨m₂, he₂, hm₂, hi₂, hle₂⟩ := rk env' l' hra
  rw [he₂, Option.bind_some]
  obtain ⟨of, ok⟩ := operands_spec p _ s₂ s₃ oss os env' (putS false σ m₂ l') hops (by simpa using hi₂)
  cases hv : evalLists p env' (ops.map fun op => op.encode Expr.const) with
  | none =>
    have e₁ : (Stmt.ledger guard rds ops).exec p ρ = none := by
      simp [Stmt.exec, hx, ha, hne, hra, ledgerGroups_eq, hv]
    rw [e₁, of hv]; trivial
  | some vss =>
  obtain ⟨m₃, he₃, hm₃, hi₃, hn₃, -⟩ := ok vss hv
  rw [he₃, Option.bind_some]
  have hb : Zkir.bool m₃ g = some active := by
    rw [bool_of_native (native_stable hg hi₁.fresh (hm₂.trans (by simpa using hm₃) hle₂)), ha]
  rw [exec_impacts p g active oss vss _ (by simpa using hb) (by simpa using hn₃)]
  have e₁ : (Stmt.ledger guard rds ops).exec p ρ =
      some { ρ with env := env', pub := l', groups := ρ.groups ++ vss.map (group active) } := by
    simp [Stmt.exec, hx, ha, hne, hra, ledgerGroups_eq, hv]
  rw [e₁]
  exact ⟨by simpa using hi₃, by simp [putS, hr.priv], by simp [putS],
    by simp [putS, hr.groups], by simp [putS, hr.outputs]⟩

/-- Every statement form. -/
theorem stmt_spec {p : Prims} {st : Stmt} {s s' : State} {is : List Instr} {ρ : RunState}
    {σ : Zkir.State} (h : stmt st s = .ok ((), is, s')) (hr : Rel p s ρ σ) :
    Sim p s' (st.exec p ρ) (exec p is σ) := by
  cases st with
  | bind v hint e => exact stmt_bind h hr
  | assert cond msg => exact stmt_assert h hr
  | constrain e r => exact stmt_constrain h hr
  | witness guard name args outs shape => exact stmt_witness h hr
  | ledger guard rds ops => exact stmt_ledger h hr

/-- A circuit body: statement by statement. -/
theorem stmts_spec (p : Prims) : ∀ (sts : List Stmt) (s s' : State) (is : List Instr)
    (ρ : RunState) (σ : Zkir.State), stmts sts s = .ok ((), is, s') → Rel p s ρ σ →
    Sim p s' (execAll p sts ρ) (exec p is σ)
  | [], s, s', is, ρ, σ, h, hr => by
      simp only [stmts, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl⟩ := h
      exact hr
  | st :: rest, s, s', is, ρ, σ, h, hr => by
      simp only [stmts] at h
      split at h
      · cases h
      next is₁ s₁ hst =>
      split at h
      · cases h
      next is₂ s₂ hrest =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl⟩ := h
      have h₁ := stmt_spec hst hr
      simp only [execAll, exec_append]
      cases he : st.exec p ρ <;> cases hz : exec p is₁ σ <;> rw [he, hz] at h₁
      · trivial
      · exact h₁.elim
      · exact h₁.elim
      · exact stmts_spec p rest s₁ s₂ is₂ _ _ hrest h₁

/-! ## Circuit inputs -/

/-- Binding the circuit inputs: both sides fail together (wrong number of
    inputs), or the invariant holds of what they bind. -/
theorem inputs_spec (p : Prims) : ∀ (ins : List Input) (s s' : State)
    (zins : List (Ident × Zkir.IrType)) (env : Env) (m : Memory) (xs : List Fr),
    inputs ins s = .ok (zins, s') → Inv p s env m →
    (IR.bindInputs env ins xs = none ↔ Zkir.bindInputs m zins xs = none) ∧
    ∀ env' m', IR.bindInputs env ins xs = some env' → Zkir.bindInputs m zins xs = some m' →
      Inv p s' env' m'
  | [], s, s', zins, env, m, xs, h, hinv => by
      simp only [inputs, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      cases xs with
      | nil =>
        refine ⟨by simp [IR.bindInputs, Zkir.bindInputs], fun env' m' h₁ h₂ => ?_⟩
        simp only [IR.bindInputs, Zkir.bindInputs, Option.some.injEq] at h₁ h₂
        subst h₁ h₂
        exact hinv
      | cons x xs => exact ⟨by simp [IR.bindInputs, Zkir.bindInputs], by simp [IR.bindInputs]⟩
  | i :: rest, s, s', zins, env, m, xs, h, hinv => by
      simp only [inputs] at h
      split at h
      · cases h
      next s₁ hb =>
      split at h
      · cases h
      next zins' s₂ hrest =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hfree, rfl⟩ := bindVar_ok hb
      cases xs with
      | nil => exact ⟨by simp [IR.bindInputs, Zkir.bindInputs], by simp [IR.bindInputs]⟩
      | cons x xs =>
        have ho : native (m.set ⟨i.name, s.next⟩ (.native x)) (.var ⟨i.name, s.next⟩) = some x := by
          simp [native_var, Zkir.Memory.set]
        have hi := (hinv.set (r := ⟨i.name, s.next⟩) (v := .native x) (Nat.le_refl _)
          (Nat.lt_succ_self _)).bind (v := i.var) hfree ho
        simp only [IR.bindInputs, Zkir.bindInputs]
        exact inputs_spec p rest _ s₂ zins' _ _ xs hrest hi

/-! ## Only the final instruction is an `output`

`IrSource.run` rejects a circuit whose `output` instructions do not match its
declared outputs, so we check that the emitter emits no `output` except the
final one. -/

/-- No instruction in the list is an `output`. -/
def NoOut (is : List Instr) : Prop := ∀ vals, Instr.output vals ∉ is

/-- The empty list has no `output`. -/
theorem NoOut.nil : NoOut [] := fun _ h => by cases h

/-- Neither part has an `output`, so neither has the whole. -/
theorem NoOut.append {is₁ is₂ : List Instr} (h₁ : NoOut is₁) (h₂ : NoOut is₂) : NoOut (is₁ ++ is₂) :=
  fun vals h => (List.mem_append.1 h).elim (h₁ vals) (h₂ vals)

/-- No element is an `output`. -/
theorem NoOut.of_forall {is : List Instr} (h : ∀ i ∈ is, ∀ vals, i ≠ .output vals) : NoOut is :=
  fun vals hm => h _ hm vals rfl

/-- A non-`output` instruction before a list without one. -/
theorem NoOut.cons {i : Instr} {is : List Instr} (hi : ∀ vals, i ≠ .output vals) (h : NoOut is) :
    NoOut (i :: is) := by
  intro vals hm
  rcases List.mem_cons.1 hm with he | he
  · exact hi vals he.symm
  · exact h vals he

mutual
/-- The code for an expression has no `output`. -/
theorem expr_noOut : ∀ (e : Expr) (hint : String) (s : State) (o : Operand) (is : List Instr)
    (s' : State), expr hint e s = .ok (o, is, s') → NoOut is
  | .var _, _, s, o, is, s', h => by
      simp only [expr] at h; split at h
      · cases h; exact NoOut.nil
      · cases h
  | .const _, _, _, _, _, _, h => by simp only [expr] at h; cases h; exact NoOut.nil
  | .invalid _, _, _, _, _, _, h => by simp only [expr] at h; cases h
  | .disclose e, hint, s, o, is, s', h => by
      simp only [expr] at h; exact expr_noOut e hint s o is s' h
  | .add a b, hint, s, o, is, s', h | .mul a b, hint, s, o, is, s', h
  | .eq a b, hint, s, o, is, s', h | .lt _ a b, hint, s, o, is, s', h => by
      simp only [expr] at h
      split at h
      · cases h; exact NoOut.nil
      split at h
      · cases h
      next a' is1 s1 ha =>
      split at h
      · cases h
      next b' is2 s2 hb =>
      simp only [finish, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      exact ((expr_noOut a _ _ _ _ _ ha).append (expr_noOut b _ _ _ _ _ hb)).append
        (NoOut.cons (by simp) NoOut.nil)
  | .neg a, hint, s, o, is, s', h => by
      simp only [expr] at h
      split at h
      · cases h; exact NoOut.nil
      split at h
      · cases h
      next a' is1 s1 ha =>
      simp only [finish, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      exact (expr_noOut a _ _ _ _ _ ha).append (NoOut.cons (by simp) NoOut.nil)
  | .select c a b, hint, s, o, is, s', h => by
      simp only [expr] at h
      split at h
      · cases h; exact NoOut.nil
      split at h
      · cases h
      next c' is0 s0 hc =>
      split at h
      · cases h
      next a' is1 s1 ha =>
      split at h
      · cases h
      next b' is2 s2 hb =>
      simp only [finish, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      exact (((expr_noOut c _ _ _ _ _ hc).append (expr_noOut a _ _ _ _ _ ha)).append
        (expr_noOut b _ _ _ _ _ hb)).append (NoOut.cons (by simp) NoOut.nil)
  | .hash xs, hint, s, o, is, s', h => by
      simp only [expr] at h
      split at h
      · cases h; exact NoOut.nil
      split at h
      · cases h
      next xs' is1 s1 hxs =>
      simp only [finish, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      exact (exprs_noOut xs _ _ _ _ hxs).append (NoOut.cons (by simp) NoOut.nil)
  | .phash _ _ xs, hint, s, o, is, s', h => by
      simp only [expr] at h
      split at h
      · cases h; exact NoOut.nil
      split at h
      · cases h
      next xs' is1 s1 hxs =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      exact (exprs_noOut xs _ _ _ _ hxs).append
        (NoOut.cons (by simp) (NoOut.cons (by simp) NoOut.nil))
  | .divmod _ _ a, hint, s, o, is, s', h => by
      simp only [expr] at h
      split at h
      · cases h; exact NoOut.nil
      split at h
      · cases h
      next a' is1 s1 ha =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      exact (expr_noOut a _ _ _ _ _ ha).append (NoOut.cons (by simp) NoOut.nil)

/-- The code for a list of expressions has no `output`. -/
theorem exprs_noOut : ∀ (xs : List Expr) (s : State) (os : List Operand) (is : List Instr)
    (s' : State), exprs xs s = .ok (os, is, s') → NoOut is
  | [], s, os, is, s', h => by simp only [exprs] at h; cases h; exact NoOut.nil
  | x :: xs, s, os, is, s', h => by
      simp only [exprs] at h
      split at h
      · cases h
      next x' is1 s1 hx =>
      split at h
      · cases h
      next xs' is2 s2 hxs =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      exact (expr_noOut x _ _ _ _ _ hx).append (exprs_noOut xs _ _ _ _ hxs)
end

/-- A range check has no `output`. -/
theorem constrain_noOut (o : Operand) (r : Range) (s : State) : NoOut (constrain o r s).1 := by
  cases r <;> simp only [constrain] <;>
    exact NoOut.of_forall (by simp)

/-- Input reads have no `output`. -/
theorem reads_noOut (b : Bool) (g : Option Operand) : ∀ (outs : List (Var × Option Range))
    (s s' : State) (is : List Instr), reads (fun o => inputInstr b o g) outs s = .ok ((), is, s') →
    NoOut is
  | [], s, s', is, h => by
      simp only [reads, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      exact NoOut.nil
  | (v, range) :: rest, s, s', is, h => by
      rw [reads_cons] at h
      split at h
      · cases h
      next s₁ _ =>
      split at h
      · cases h
      next is' s₃ hrest =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      refine (NoOut.cons (by cases b <;> simp [inputInstr]) ?_).append (reads_noOut b g rest _ _ _ hrest)
      cases range with
      | none => exact NoOut.nil
      | some r => exact constrain_noOut _ r _

/-- Ledger operands have no `output`. -/
theorem operands_noOut : ∀ (xss : List (List Expr)) (s s' : State) (oss : List (List Operand))
    (is : List Instr), operands xss s = .ok (oss, is, s') → NoOut is
  | [], s, s', oss, is, h => by
      simp only [operands, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      exact NoOut.nil
  | xs :: rest, s, s', oss, is, h => by
      simp only [operands] at h
      split at h
      · cases h
      next os is₁ s₁ hxs =>
      split at h
      · cases h
      next oss' is₂ s₂ hrest =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      exact (exprs_noOut xs _ _ _ _ hxs).append (operands_noOut rest _ _ _ _ hrest)

/-- A statement's code has no `output`. -/
theorem stmt_noOut {st : Stmt} {s s' : State} {is : List Instr}
    (h : stmt st s = .ok ((), is, s')) : NoOut is := by
  cases st with
  | bind v hint e =>
    simp only [stmt] at h
    split at h
    · cases h
    next o is₁ s₁ he =>
    split at h
    · cases h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    exact expr_noOut _ _ _ _ _ _ he
  | assert cond msg =>
    simp only [stmt] at h
    split at h
    · cases h
    next o is₁ s₁ he =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    exact (expr_noOut _ _ _ _ _ _ he).append (NoOut.cons (by simp) NoOut.nil)
  | constrain e r =>
    simp only [stmt] at h
    split at h
    · cases h
    next o is₁ s₁ he =>
    have hc := constrain_noOut o r s₁
    generalize constrain o r s₁ = c at h hc
    obtain ⟨cs, s₂⟩ := c
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    exact (expr_noOut _ _ _ _ _ _ he).append hc
  | witness guard name args outs shape =>
    simp only [stmt] at h
    split at h
    · cases h
    next g is₁ s₁ he =>
    split at h
    · cases h
    next rs s₂ hreads =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    exact (expr_noOut _ _ _ _ _ _ he).append (reads_noOut true _ _ _ _ _ hreads)
  | ledger guard rds ops =>
    simp only [stmt] at h
    split at h
    · cases h
    next g is₁ s₁ he =>
    split at h
    · cases h
    next rs s₂ hreads =>
    split at h
    · cases h
    next oss os s₃ hops =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    refine (((expr_noOut _ _ _ _ _ _ he).append (reads_noOut false _ _ _ _ _ hreads)).append
      (operands_noOut _ _ _ _ _ hops)).append (NoOut.of_forall ?_)
    intro i hi vals
    obtain ⟨os', -, rfl⟩ := List.mem_map.1 hi
    simp

/-- A body's code has no `output`. -/
theorem stmts_noOut : ∀ (sts : List Stmt) (s s' : State) (is : List Instr),
    stmts sts s = .ok ((), is, s') → NoOut is
  | [], s, s', is, h => by
      simp only [stmts, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      exact NoOut.nil
  | st :: rest, s, s', is, h => by
      simp only [stmts] at h
      split at h
      · cases h
      next is₁ s₁ hst =>
      split at h
      · cases h
      next is₂ s₂ hrest =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      exact (stmt_noOut hst).append (stmts_noOut rest _ _ _ hrest)

/-- `exprs` yields one operand per expression. -/
theorem exprs_length : ∀ (xs : List Expr) (s s' : State) (os : List Operand) (is : List Instr),
    exprs xs s = .ok (os, is, s') → os.length = xs.length
  | [], s, s', os, is, h => by simp only [exprs] at h; cases h; rfl
  | x :: xs, s, s', os, is, h => by
      simp only [exprs] at h
      split at h
      · cases h
      split at h
      · cases h
      next xs' is2 s2 hxs =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -, -⟩ := h
      simp [exprs_length xs _ _ _ _ hxs]

/-- The emitted circuit's only `output` lists exactly its declared outputs. -/
theorem outputsDeclared_emitted (ins : List (Ident × Zkir.IrType)) (outputs : List Expr)
    (body tail : List Instr) (outs : List Operand) (hb : NoOut body) (ht : NoOut tail)
    (hl : outs.length = outputs.length) :
    Zkir.IrSource.outputsDeclared
      { inputs := ins, outputs := outputs.map fun _ => .native,
        instructions := (body ++ tail ++ if outs.isEmpty then [] else [Instr.output outs]).toArray } =
      true := by
  simp only [Zkir.IrSource.outputsDeclared, List.all_toArray, List.all_eq_true]
  intro i hi
  rcases List.mem_append.1 hi with hi | hi
  · rcases List.mem_append.1 hi with hi | hi
    · cases i <;> first | rfl | exact absurd hi (hb _)
    · cases i <;> first | rfl | exact absurd hi (ht _)
  · split at hi
    · cases hi
    · simp only [List.mem_singleton] at hi
      subst hi
      simp only [hl, List.length_map, beq_self_eq_true, Bool.true_and, List.all_map,
        List.all_eq_true]
      intro _ _
      rfl

/-! ## The emitter preserves semantics -/

/-- The ZKIR emitted for a circuit, run by Midnight's evaluator, gives exactly
    what the IR semantics gives: the same outputs and public inputs, or failure
    on both sides. -/
theorem circuitCore_correct (p : Zkir.Prims) (c : IR.Circuit) (src : Zkir.IrSource)
    (h : Emit.circuitCore c = .ok src) (inputs priv pub : List Fr) :
    src.run p inputs priv pub = c.run p inputs priv pub := by
  simp only [circuitCore] at h
  split at h
  · cases h
  next ins s₀ hin =>
  split at h
  · cases h
  next body s₁ hbody =>
  split at h
  · cases h
  next outs tail s₂ houts =>
  simp only [Except.ok.injEq] at h
  subst h
  have hdecl := outputsDeclared_emitted ins c.outputs body tail outs
    (stmts_noOut _ _ _ _ hbody) (exprs_noOut _ _ _ _ _ houts) (exprs_length _ _ _ _ _ houts)
  obtain ⟨hI₁, hI₂⟩ := inputs_spec p c.inputs {} s₀ ins (fun _ => 0) (fun _ => none) inputs hin
    (Inv.empty p _)
  simp only [Zkir.IrSource.run, hdecl, Circuit.run, List.toList_toArray, exec_append]
  cases hb : IR.bindInputs (fun _ => 0) c.inputs inputs with
  | none => simp [hI₁.1 hb]
  | some env =>
  cases hz : Zkir.bindInputs (fun _ => none) ins inputs with
  | none => simp [hI₁.2 hz] at hb
  | some m =>
  have hS := stmts_spec p c.body.toList s₀ s₁ body { env, priv, pub } { mem := m, priv, pub } hbody
    ⟨hI₂ env m hb hz, rfl, rfl, rfl, rfl⟩
  simp only [Option.bind_some, Bind.bind, Bool.not_true, Bool.false_eq_true, ite_false]
  cases hA : execAll p c.body.toList { env, priv, pub } <;>
    cases hZ : exec p body { mem := m, priv, pub } <;> rw [hA, hZ] at hS
  · rfl
  · exact hS.elim
  · exact hS.elim
  rename_i ρ₁ σ₁
  simp only [Option.bind_some]
  obtain ⟨f, k⟩ := exprs_spec p c.outputs s₁ outs tail s₂ houts ρ₁.env σ₁ hS.inv
  cases hv : Expr.evalList p ρ₁.env c.outputs with
  | none => simp [f hv]
  | some vs =>
  obtain ⟨m₂, he₂, -, -, hn, -⟩ := k vs hv
  rw [he₂, Option.bind_some]
  have hout : exec p (if outs.isEmpty then [] else [Instr.output outs]) { σ₁ with mem := m₂ } =
      some { σ₁ with mem := m₂, outputs := vs } := by
    have ho := hS.outputs
    cases outs with
    | nil =>
      simp only [natives, Option.some.injEq] at hn
      subst hn
      cases σ₁
      simp_all [Zkir.exec]
    | cons o os =>
      simp [Zkir.exec, Zkir.Instr.step, hn, ho]
  rw [hout]
  simp [hS.priv, hS.pub, hS.groups]

end Damp.Emit
