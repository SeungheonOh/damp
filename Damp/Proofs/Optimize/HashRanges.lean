/-
`Circuit.hashRanges` is sound for hash functions that refuse inputs that do
not fit their alignment (`AlignChecked p`), and `Damp.Crypto.prims` does.

The argument: a statement's expressions are evaluated strictly, so an
expression containing a `phash` that reads `e` as an element of `w` bits fails
when `e` fails or its value has `w` bits or more (`Expr.eval_none_of_slot`). The
statements after a dropped range check certainly reach such a hash, unless they
fail first, and none of them changes `e` on the way (`hashRangesGo_certain`). So
a value the dropped check refuses makes the rest fail, and the run fails
exactly when the original does: the body runs to the same result, failures
included, for `Circuit.run` and for the executor (`hashRangesGo_execAll`,
`hashRangesGo_steps`).
-/
import Damp.Optimize.HashRanges
import Damp.Proofs.Optimize.SoundFor
import Damp.Proofs.Prune
import Damp.Crypto.Prims

namespace Damp.IR
open Damp.Zkir (Prims AlignAtom fitsBits)
open Damp.Exec
open Damp.Emit (Agree eval_congr)

/-! ## Alignments -/

/-- The hash functions refuse inputs that do not fit the bytes their alignment
    reads them as. -/
def AlignChecked (p : Prims) : Prop :=
  ∀ al vals d, p.persistentHash al vals = some d → ∀ x ∈ alignSlots al vals, x.1.val < 2 ^ x.2

theorem hr_parseBytesAtom_spec {n : Nat} {xs : List Fr} {bs : List Nat} {rest : List Fr}
    (h : Crypto.parseBytesAtom n xs = some (bs, rest)) :
    ¬ xs.length < n / 31 + (if n % 31 ≠ 0 then 1 else 0) ∧
    (n % 31 = 0 → (∀ x ∈ xs.take (n / 31), x.val < 2 ^ 248) ∧ rest = xs.drop (n / 31)) ∧
    (n % 31 ≠ 0 → ∃ x r, xs = x :: r ∧ x.val < 2 ^ (8 * (n % 31)) ∧
        (∀ y ∈ r.take (n / 31), y.val < 2 ^ 248) ∧ rest = r.drop (n / 31)) := by
  by_cases hz : n % 31 = 0
  · simp only [Crypto.parseBytesAtom, hz] at h
    simp at h
    refine ⟨by simp [hz]; omega, fun _ => ⟨by simpa using h.2.1, h.2.2.2.symm⟩, fun h' => absurd hz h'⟩
  · cases xs with
    | nil => simp [Crypto.parseBytesAtom, hz] at h
    | cons x r =>
        simp [Crypto.parseBytesAtom, hz] at h
        refine ⟨by simp [hz]; omega, fun h' => absurd h' hz, fun _ => ⟨x, r, rfl, h.2.2.1, by simpa using h.2.1,
          h.2.2.2.2.symm⟩⟩

theorem hr_binaryRepr_slots : ∀ (al : List AlignAtom) (xs : List Fr) (bs : List Nat),
    Crypto.binaryRepr al xs = some bs → ∀ x ∈ alignSlots al xs, x.1.val < 2 ^ x.2
  | [], _, _, _ => by simp [alignSlots]
  | .compress :: _, _, _, _ => by simp [alignSlots]
  | .field :: _, [], _, _ => by simp [alignSlots]
  | .field :: al, f :: xs, bs, h => by
      simp only [Crypto.binaryRepr, Crypto.parseAtom, Option.bind_eq_bind, Option.bind_some,
        Option.bind_eq_some_iff] at h
      obtain ⟨more, hm, _⟩ := h
      simp only [alignSlots]
      exact hr_binaryRepr_slots al xs more hm
  | .bytes n :: al, xs, bs, h => by
      simp only [Crypto.binaryRepr, Crypto.parseAtom, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨bs1, rest⟩, hp, more, hm, _⟩ := h
      obtain ⟨hlen, h0, h1⟩ := hr_parseBytesAtom_spec hp
      intro x hx
      simp only [alignSlots, hlen, ite_false] at hx
      by_cases hz : n % 31 = 0
      · obtain ⟨hall, hrest⟩ := h0 hz
        simp only [hz, ite_true, List.mem_append, List.mem_map] at hx
        rcases hx with ⟨y, hy, rfl⟩ | hx
        · exact hall y hy
        · subst hrest; exact hr_binaryRepr_slots al _ more hm x hx
      · obtain ⟨y, r, rfl, hy, hall, hrest⟩ := h1 hz
        simp only [hz, ite_false, List.mem_cons, List.mem_append, List.mem_map] at hx
        rcases hx with rfl | ⟨z, hz', rfl⟩ | hx
        · exact hy
        · exact hall z hz'
        · subst hrest; exact hr_binaryRepr_slots al _ more hm x hx

/-- Damp's persistent hash refuses inputs that do not fit their alignment. -/
theorem Crypto.prims_alignChecked : AlignChecked Crypto.prims := by
  intro al vals d h
  simp only [Crypto.prims, Crypto.persistentHash, Option.map_eq_some_iff] at h
  obtain ⟨bs, hb, _⟩ := h
  exact hr_binaryRepr_slots al vals bs hb

/-! ## Evaluating lists -/

theorem hr_evalList_length {p : Prims} {env : Env} :
    ∀ {xs : List Expr} {vals : List Fr}, Expr.evalList p env xs = some vals → vals.length = xs.length
  | [], vals, h => by simp [Expr.evalList] at h; simp [← h]
  | x :: xs, vals, h => by
      simp only [Expr.evalList, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨y, _, ys, hys, h⟩ := h
      simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      simp [hr_evalList_length hys]

theorem hr_evalList_take {p : Prims} {env : Env} :
    ∀ (k : Nat) {xs : List Expr} {vals : List Fr}, Expr.evalList p env xs = some vals →
      Expr.evalList p env (xs.take k) = some (vals.take k)
  | 0, _, _, _ => by simp [Expr.evalList]
  | _ + 1, [], vals, h => by simp [Expr.evalList] at h; subst h; simp [Expr.evalList]
  | k + 1, x :: xs, vals, h => by
      simp only [Expr.evalList, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨y, hy, ys, hys, h⟩ := h
      simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      simp [Expr.evalList, hy, hr_evalList_take k hys]

theorem hr_evalList_drop {p : Prims} {env : Env} :
    ∀ (k : Nat) {xs : List Expr} {vals : List Fr}, Expr.evalList p env xs = some vals →
      Expr.evalList p env (xs.drop k) = some (vals.drop k)
  | 0, _, _, h => by simpa using h
  | _ + 1, [], vals, h => by simp [Expr.evalList] at h; subst h; simp [Expr.evalList]
  | k + 1, x :: xs, vals, h => by
      simp only [Expr.evalList, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨y, hy, ys, hys, h⟩ := h
      simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      simpa using hr_evalList_drop k hys

theorem hr_evalList_mem {p : Prims} {env : Env} :
    ∀ {xs : List Expr} {vals : List Fr}, Expr.evalList p env xs = some vals →
      ∀ e ∈ xs, ∃ v ∈ vals, e.eval p env = some v
  | [], _, _, e, he => by simp at he
  | x :: xs, vals, h, e, he => by
      simp only [Expr.evalList, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨y, hy, ys, hys, h⟩ := h
      simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨y, by simp, hy⟩
      · obtain ⟨v, hv, hev⟩ := hr_evalList_mem hys e he
        exact ⟨v, by simp [hv], hev⟩

/-- An element of a list that evaluates to a list evaluates to the element at
    the same position: for `take`, as values of 248 bits. -/
theorem hr_evalList_take_slots {p : Prims} {env : Env} {xs : List Expr} {vals : List Fr} (k : Nat)
    (h : Expr.evalList p env xs = some vals) :
    ∀ y ∈ (xs.take k).map (·, 248), ∃ v, y.1.eval p env = some v ∧ (v, y.2) ∈ (vals.take k).map (·, 248) := by
  intro y hy
  simp only [List.mem_map] at hy
  obtain ⟨e, he, rfl⟩ := hy
  have ht := hr_evalList_take k h
  -- position-wise: zip the two lists
  suffices H : ∀ (es : List Expr) (vs : List Fr), Expr.evalList p env es = some vs → ∀ e ∈ es,
      ∃ v, e.eval p env = some v ∧ v ∈ vs by
    obtain ⟨v, hv, hm⟩ := H _ _ ht e he
    exact ⟨v, hv, by simp only [List.mem_map]; exact ⟨v, hm, rfl⟩⟩
  intro es vs hes e he
  obtain ⟨v, hv, hev⟩ := hr_evalList_mem hes e he
  exact ⟨v, hev, hv⟩

/-- What `alignSlots` finds in expressions evaluates to what it finds in their values. -/
theorem alignSlots_eval {p : Prims} {env : Env} :
    ∀ (al : List AlignAtom) (xs : List Expr) (vals : List Fr), Expr.evalList p env xs = some vals →
      ∀ y ∈ alignSlots al xs, ∃ v, y.1.eval p env = some v ∧ (v, y.2) ∈ alignSlots al vals
  | [], _, _, _ => by simp [alignSlots]
  | .compress :: _, _, _, _ => by simp [alignSlots]
  | .field :: _, [], _, _ => by simp [alignSlots]
  | .field :: al, x :: xs, vals, h => by
      simp only [Expr.evalList, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨y, _, ys, hys, h⟩ := h
      simp only [Option.pure_def, Option.some.injEq] at h
      subst h
      simp only [alignSlots]
      exact alignSlots_eval al xs ys hys
  | .bytes n :: al, xs, vals, h => by
      have hl := hr_evalList_length h
      intro y hy
      simp only [alignSlots] at hy ⊢
      rw [hl]
      by_cases hlen : xs.length < n / 31 + (if n % 31 ≠ 0 then 1 else 0)
      · rw [if_pos hlen] at hy; simp at hy
      rw [if_neg hlen] at hy ⊢
      by_cases hz : n % 31 = 0
      · rw [if_pos hz] at hy ⊢
        rcases List.mem_append.mp hy with hy | hy
        · obtain ⟨v, hv, hm⟩ := hr_evalList_take_slots (n / 31) h y (by simpa using hy)
          exact ⟨v, hv, List.mem_append_left _ hm⟩
        · obtain ⟨v, hv, hm⟩ := alignSlots_eval al _ _ (hr_evalList_drop (n / 31) h) y hy
          exact ⟨v, hv, List.mem_append_right _ hm⟩
      · rw [if_neg hz] at hy ⊢
        cases xs with
        | nil => simp at hy
        | cons x r =>
            simp only [Expr.evalList, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
            obtain ⟨u, hu, us, hus, h⟩ := h
            simp only [Option.pure_def, Option.some.injEq] at h
            subst h
            simp only [List.mem_cons, List.mem_append] at hy ⊢
            rcases hy with rfl | hy | hy
            · exact ⟨u, hu, Or.inl rfl⟩
            · obtain ⟨v, hv, hm⟩ := hr_evalList_take_slots (n / 31) hus y (by simpa using hy)
              exact ⟨v, hv, Or.inr (Or.inl hm)⟩
            · obtain ⟨v, hv, hm⟩ := alignSlots_eval al _ _ (hr_evalList_drop (n / 31) hus) y hy
              exact ⟨v, hv, Or.inr (Or.inr hm)⟩

/-! ## Expressions -/

/-- `y.1` fails, or has a value of `y.2` bits or more, in `env`. -/
def SlotBad (p : Prims) (env : Env) (y : Expr × Nat) : Prop := ∀ v, y.1.eval p env = some v → ¬ v.val < 2 ^ y.2

theorem SlotBad.congr {p : Prims} {env env' : Env} {y : Expr × Nat} (h : SlotBad p env y)
    (ha : Agree y.1.vars env env') : SlotBad p env' y := by
  intro v hv; rw [← eval_congr p y.1 ha] at hv; exact h v hv

section Slots
variable {p : Prims} (hp : AlignChecked p) {env : Env}

include hp in
mutual
/-- An expression fails when something a hash in it reads as bytes is bad. -/
theorem Expr.eval_none_of_slot : ∀ (x : Expr) (y : Expr × Nat), y ∈ x.hashSlots → SlotBad p env y →
    x.eval p env = none
  | .var _, _, h, _ | .const _, _, h, _ | .invalid _, _, h, _ => by simp [Expr.hashSlots] at h
  | .add a b, y, h, hb | .mul a b, y, h, hb | .eq a b, y, h, hb => by
      simp only [Expr.hashSlots, List.mem_append] at h
      rcases h with h | h
      · simp [Expr.eval, Expr.eval_none_of_slot a y h hb]
      · cases a.eval p env <;> simp [Expr.eval, Expr.eval_none_of_slot b y h hb]
  | .lt _ a b, y, h, hb => by
      simp only [Expr.hashSlots, List.mem_append] at h
      rcases h with h | h
      · simp [Expr.eval, Expr.eval_none_of_slot a y h hb]
      · cases a.eval p env <;> simp [Expr.eval, Expr.eval_none_of_slot b y h hb]
  | .neg a, y, h, hb => by
      simp only [Expr.hashSlots] at h; simp [Expr.eval, Expr.eval_none_of_slot a y h hb]
  | .disclose a, y, h, hb => by
      simp only [Expr.hashSlots] at h; simp [Expr.eval, Expr.eval_none_of_slot a y h hb]
  | .divmod _ _ a, y, h, hb => by
      simp only [Expr.hashSlots] at h; simp [Expr.eval, Expr.eval_none_of_slot a y h hb]
  | .select c a b, y, h, hb => by
      simp only [Expr.hashSlots, List.mem_append] at h
      rcases h with (h | h) | h
      · simp [Expr.eval, Expr.eval_none_of_slot c y h hb]
      · cases c.eval p env <;> simp [Expr.eval, Expr.eval_none_of_slot a y h hb]
      · cases c.eval p env <;> cases a.eval p env <;> simp [Expr.eval, Expr.eval_none_of_slot b y h hb]
  | .hash xs, y, h, hb => by
      simp only [Expr.hashSlots] at h; simp [Expr.eval, Expr.evalList_none_of_slot xs y h hb]
  | .phash high al xs, y, h, hb => by
      simp only [Expr.hashSlots, List.mem_append] at h
      rcases h with h | h
      · simp only [Expr.eval]
        cases hxs : Expr.evalList p env xs with
        | none => rfl
        | some vals =>
            obtain ⟨v, hv, hm⟩ := alignSlots_eval al xs vals hxs y h
            cases hd : p.persistentHash al vals with
            | none => simp [hd]
            | some d => exact absurd (hp al vals d hd _ hm) (hb v hv)
      · simp [Expr.eval, Expr.evalList_none_of_slot xs y h hb]
theorem Expr.evalList_none_of_slot : ∀ (xs : List Expr) (y : Expr × Nat), y ∈ Expr.hashSlotsList xs →
    SlotBad p env y → Expr.evalList p env xs = none
  | [], _, h, _ => by simp [Expr.hashSlotsList] at h
  | x :: xs, y, h, hb => by
      simp only [Expr.hashSlotsList, List.mem_append] at h
      rcases h with h | h
      · simp [Expr.evalList, Expr.eval_none_of_slot x y h hb]
      · cases x.eval p env <;> simp [Expr.evalList, Expr.evalList_none_of_slot xs y h hb]
end

end Slots

/-! ## Statements: what they change, and when they certainly fail -/

theorem hr_readAll_keeps {active : Bool} : ∀ (outs : List (Var × Option Range)) (env env' : Env) (st st' : List Fr),
    readAll active env outs st = some (env', st') → ∀ u, u ∉ outs.map Prod.fst → env' u = env u
  | [], env, env', st, st', h, u, _ => by simp [readAll] at h; rw [h.1]
  | (v, r) :: rest, env, env', st, st', h, u, hu => by
      simp only [List.map_cons, List.mem_cons, not_or] at hu
      simp only [readAll, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨x, st₁⟩, _, h⟩ := h
      have h' : readAll active (env.set v x) rest st₁ = some (env', st') := by
        cases r with
        | none => simpa using h
        | some r =>
            by_cases hh : r.holds x
            · simpa [hh] using h
            · simp [hh] at h
      rw [hr_readAll_keeps rest _ _ _ _ h' u hu.2]; simp [Env.set, hu.1]

theorem hr_assign_keeps : ∀ (outs : List (Var × Option Range)) (vals : List Fr) (env env' : Env),
    Exec.assign env outs vals = some env' → ∀ u, u ∉ outs.map Prod.fst → env' u = env u
  | [], [], env, env', h, u, _ => by simp [Exec.assign] at h; rw [h]
  | [], _ :: _, _, _, h, _, _ => by simp [Exec.assign] at h
  | _ :: _, [], _, _, h, _, _ => by simp [Exec.assign] at h
  | (v, r) :: rest, x :: xs, env, env', h, u, hu => by
      simp only [List.map_cons, List.mem_cons, not_or] at hu
      have h' : Exec.assign (env.set v x) rest xs = some env' := by
        cases r with
        | none => simpa [Exec.assign] using h
        | some r =>
            by_cases hh : r.holds x
            · simpa [Exec.assign, hh] using h
            · simp [Exec.assign, hh] at h
      rw [hr_assign_keeps rest xs _ _ h' u hu.2]; simp [Env.set, hu.1]

theorem hr_agree_of_keeps {env env' : Env} {L B : List Var} (hk : ∀ u, u ∉ B → env' u = env u)
    (hd : L.all (fun v => !B.contains v) = true) : Agree L env env' := by
  intro u hu
  have : u ∉ B := by
    have := List.all_eq_true.mp hd u hu
    simpa using this
  exact (hk u this).symm

section Stmts
variable {p : Prims} (hp : AlignChecked p)

/-- A run of a statement changes only the variables it binds. -/
theorem Stmt.exec_keeps {st st' : RunState} : ∀ s : Stmt, s.exec p st = some st' →
    ∀ u, u ∉ s.binds → st'.env u = st.env u
  | .bind v _ e, h, u, hu => by
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨x, _, rfl⟩ := h
      simp only [Stmt.binds, List.mem_singleton] at hu
      simp [Env.set, hu]
  | .assert c _, h, u, _ => by
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨_, _, b, _, h⟩ := h
      split at h <;> simp_all
  | .constrain e r, h, u, _ => by
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨_, _, h⟩ := h
      split at h <;> simp_all
  | .witness g _ _ outs _, h, u, hu => by
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨_, _, h⟩ := h
      split at h
      · simp at h; rw [h]
      · simp only [Option.bind_eq_some_iff] at h
        obtain ⟨_, _, ⟨env, priv⟩, hr, h⟩ := h
        simp only [Option.pure_def, Option.some.injEq] at h
        subst h
        exact hr_readAll_keeps outs _ _ _ _ hr u hu
  | .ledger g reads ops, h, u, hu => by
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨_, _, h⟩ := h
      split at h
      · simp at h; rw [h]
      · simp only [Option.bind_eq_some_iff] at h
        obtain ⟨_, _, ⟨env, pub⟩, hr, _, _, h⟩ := h
        simp only [Option.pure_def, Option.some.injEq] at h
        subst h
        exact hr_readAll_keeps _ _ _ _ _ hr u (by simpa [Stmt.binds, List.map_map, Function.comp_def] using hu)

/-- A step of the executor changes only the variables the statement binds. -/
theorem Stmt.step_keeps {ω σ : Type} {O : Oracles ω σ} {st st' : Exec.State ω σ} : ∀ s : Stmt,
    Exec.step p O st s = some st' → ∀ u, u ∉ s.binds → st'.env u = st.env u
  | .bind v _ e, h, u, hu => by
      simp only [Exec.step, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨x, _, rfl⟩ := h
      simp only [Stmt.binds, List.mem_singleton] at hu
      simp [Env.set, hu]
  | .assert c _, h, u, _ => by
      simp only [Exec.step, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨_, _, b, _, h⟩ := h
      split at h <;> simp_all
  | .constrain e r, h, u, _ => by
      simp only [Exec.step, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨_, _, h⟩ := h
      split at h <;> simp_all
  | .witness g _ args outs _, h, u, hu => by
      simp only [Exec.step, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨_, _, h⟩ := h
      split at h
      · split at h
        · simp only [Option.bind_eq_some_iff] at h
          obtain ⟨_, _, ⟨vals, w⟩, _, h⟩ := h
          split at h
          · simp only [Option.pure_def, Option.some.injEq] at h; rw [← h]
          · simp at h
        · simp at h; rw [h]
      · simp only [Option.bind_eq_some_iff] at h
        obtain ⟨act, _, h⟩ := h
        split at h
        · simp only [Option.bind_eq_some_iff] at h
          obtain ⟨_, _, ⟨vals, w⟩, _, env, he, h⟩ := h
          simp only [Option.pure_def, Option.some.injEq] at h
          subst h
          exact hr_assign_keeps outs _ _ _ he u hu
        · simp only [Option.bind_eq_some_iff] at h
          obtain ⟨env, he, h⟩ := h
          simp only [Option.pure_def, Option.some.injEq] at h
          subst h
          exact hr_assign_keeps outs _ _ _ he u hu
  | .ledger g reads ops, h, u, hu => by
      have hu' : u ∉ (reads.map fun v => (v, (none : Option Range))).map Prod.fst := by
        simpa [Stmt.binds, List.map_map, Function.comp_def] using hu
      simp only [Exec.step, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨_, _, h⟩ := h
      split at h
      · simp at h; rw [h]
      · simp only [Option.bind_eq_some_iff] at h
        obtain ⟨act, _, h⟩ := h
        split at h
        · simp only [Option.bind_eq_some_iff] at h
          obtain ⟨_, _, ⟨vals, l⟩, _, env, he, _, _, h⟩ := h
          simp only [Option.pure_def, Option.some.injEq] at h
          subst h
          exact hr_assign_keeps _ _ _ _ he u hu'
        · simp only [Option.bind_eq_some_iff] at h
          obtain ⟨env, he, _, _, h⟩ := h
          simp only [Option.pure_def, Option.some.injEq] at h
          subst h
          exact hr_assign_keeps _ _ _ _ he u hu'

include hp in
theorem ledgerGroups_none_of_slot {env : Env} (active : Bool) : ∀ (ops : List (Impact.Op Expr)) (y : Expr × Nat),
    y ∈ ops.flatMap (fun op => Expr.hashSlotsList (op.encode Expr.const)) → SlotBad p env y →
      ledgerGroups p env active ops = none
  | [], _, h, _ => by simp at h
  | op :: ops, y, h, hb => by
      simp only [List.flatMap_cons, List.mem_append] at h
      rcases h with h | h
      · simp [ledgerGroups, Expr.evalList_none_of_slot hp _ y h hb]
      · cases Expr.evalList p env (op.encode Expr.const) <;>
          simp [ledgerGroups, ledgerGroups_none_of_slot active ops y h hb]

theorem hr_ledger_slot_split {g : Expr} {reads : List Var} {ops : List (Impact.Op Expr)} {y : Expr × Nat}
    (h : y ∈ (Stmt.ledger g reads ops).hashSlots) :
    y ∈ g.hashSlots ∨ (y ∈ ops.flatMap (fun op => Expr.hashSlotsList (op.encode Expr.const)) ∧
      y.1.vars.all (fun v => !reads.contains v) = true) := by
  simp only [Stmt.hashSlots, List.mem_append, List.mem_filter] at h
  exact h

include hp in
/-- A statement fails when something it certainly hashes is bad. -/
theorem Stmt.exec_none_of_slot {st : RunState} : ∀ (s : Stmt) (y : Expr × Nat), y ∈ s.hashSlots →
    SlotBad p st.env y → s.exec p st = none
  | .bind _ _ e, y, h, hb | .assert e _, y, h, hb | .constrain e _, y, h, hb => by
      simp [Stmt.exec, Expr.eval_none_of_slot hp e y h hb]
  | .witness g .., y, h, hb => by
      simp [Stmt.exec, Expr.eval_none_of_slot hp g y h hb]
  | .ledger g reads ops, y, h, hb => by
      rcases hr_ledger_slot_split h with h | ⟨h, hd⟩
      · simp [Stmt.exec, Expr.eval_none_of_slot hp g y h hb]
      · have hne : ops ≠ [] := by rintro rfl; simp at h
        simp only [Stmt.exec, Option.bind_eq_bind]
        cases g.eval p st.env with
        | none => rfl
        | some gv =>
            simp only [Option.bind_some]
            rw [if_neg (by cases ops <;> simp_all)]
            cases asBool gv with
            | none => rfl
            | some act =>
                simp only [Option.bind_some]
                cases hr : readAll act st.env (reads.map fun v => (v, none)) st.pub with
                | none => rfl
                | some r =>
                    obtain ⟨env, pub⟩ := r
                    have hk := hr_readAll_keeps _ _ _ _ _ hr
                    have hb' := hb.congr (hr_agree_of_keeps (fun u hu => hk u (by
                      simpa [List.map_map, Function.comp_def] using hu)) hd)
                    simp [ledgerGroups_none_of_slot hp act ops y h hb']

include hp in
/-- An executor step fails when something the statement certainly hashes is bad. -/
theorem Stmt.step_none_of_slot {ω σ : Type} {O : Oracles ω σ} {st : Exec.State ω σ} :
    ∀ (s : Stmt) (y : Expr × Nat), y ∈ s.hashSlots → SlotBad p st.env y → Exec.step p O st s = none
  | .bind _ _ e, y, h, hb | .assert e _, y, h, hb | .constrain e _, y, h, hb => by
      simp [Exec.step, Expr.eval_none_of_slot hp e y h hb]
  | .witness g .., y, h, hb => by
      simp [Exec.step, Expr.eval_none_of_slot hp g y h hb]
  | .ledger g reads ops, y, h, hb => by
      rcases hr_ledger_slot_split h with h | ⟨h, hd⟩
      · simp [Exec.step, Expr.eval_none_of_slot hp g y h hb]
      · have hne : ops ≠ [] := by rintro rfl; simp at h
        have hu : ∀ env, Exec.assign st.env (reads.map fun v => (v, none)) env = none ∨
            ∃ env', Exec.assign st.env (reads.map fun v => (v, none)) env = some env' ∧ SlotBad p env' y := by
          intro vals
          cases ha : Exec.assign st.env (reads.map fun v => (v, (none : Option Range))) vals with
          | none => exact Or.inl rfl
          | some env' =>
              refine Or.inr ⟨env', rfl, hb.congr (hr_agree_of_keeps (fun u hu => hr_assign_keeps _ _ _ _ ha u (by
                simpa [List.map_map, Function.comp_def] using hu)) hd)⟩
        simp only [Exec.step, Option.bind_eq_bind]
        cases g.eval p st.env with
        | none => rfl
        | some gv =>
            simp only [Option.bind_some]
            rw [if_neg (by cases ops <;> simp_all)]
            cases asBool gv with
            | none => rfl
            | some act =>
                simp only [Option.bind_some]
                cases act with
                | true =>
                    simp only [ite_true]
                    cases Exec.request p st.env ops with
                    | none => rfl
                    | some req =>
                        simp only [Option.bind_some]
                        cases O.ledger req st.ledger with
                        | none => rfl
                        | some r =>
                            obtain ⟨vals, l⟩ := r
                            simp only [Option.bind_some]
                            rcases hu vals with ha | ⟨env', ha, hb'⟩
                            · simp [ha]
                            · simp [ha, ledgerGroups_none_of_slot hp true ops y h hb']
                | false =>
                    simp only [Bool.false_eq_true, ite_false]
                    rcases hu (reads.map fun _ => 0) with ha | ⟨env', ha, hb'⟩
                    · simp [ha]
                    · simp [ha, ledgerGroups_none_of_slot hp false ops y h hb']

end Stmts

/-! ## The pass -/

theorem hashRangesGo_snd (s : Stmt) (rest : List Stmt) :
    (hashRangesGo (s :: rest)).2 =
      s.hashSlots ++ (hashRangesGo rest).2.filter (fun x => x.1.vars.all fun v => !s.binds.contains v) := by
  conv => lhs; unfold hashRangesGo
  split <;> rfl

section Pass
variable {p : Prims} (hp : AlignChecked p)

include hp in
/-- What `hashRangesGo` collects is certainly hashed: when it is bad, the
    statements fail, for `Circuit.run` and for the executor. -/
theorem hashRangesGo_certain : ∀ (L : List Stmt) (y : Expr × Nat), y ∈ (hashRangesGo L).2 →
    (∀ st : RunState, SlotBad p st.env y → execAll p L st = none) ∧
    (∀ {ω σ : Type} (O : Oracles ω σ) (st : Exec.State ω σ), SlotBad p st.env y → Exec.steps p O L st = none)
  | [], y, h => by simp [hashRangesGo] at h
  | s :: rest, y, h => by
      rw [hashRangesGo_snd] at h
      rcases List.mem_append.mp h with h | h
      · exact ⟨fun st hb => by simp [execAll, Stmt.exec_none_of_slot hp s y h hb],
               fun O st hb => by simp [Exec.steps, Stmt.step_none_of_slot hp s y h hb]⟩
      · obtain ⟨h, hd⟩ := List.mem_filter.mp h
        obtain ⟨ih1, ih2⟩ := hashRangesGo_certain rest y h
        refine ⟨fun st hb => ?_, fun O st hb => ?_⟩
        · simp only [execAll, Option.bind_eq_bind]
          cases he : s.exec p st with
          | none => rfl
          | some st' => exact ih1 st' (hb.congr (hr_agree_of_keeps (Stmt.exec_keeps s he) hd))
        · simp only [Exec.steps, Option.bind_eq_bind]
          cases he : Exec.step p O st s with
          | none => rfl
          | some st' => exact ih2 O st' (hb.congr (hr_agree_of_keeps (Stmt.step_keeps s he) hd))

end Pass

theorem weakenOuts_fst (F : List (Expr × Nat)) :
    ∀ outs : List (Var × Option Range), (weakenOuts F outs).map Prod.fst = outs.map Prod.fst
  | [] => rfl
  | (v, some (.bits n)) :: rest => by
      simp only [weakenOuts]; split <;> simp [weakenOuts_fst F rest]
  | (v, none) :: rest | (v, some .zero) :: rest | (v, some .bool) :: rest
  | (v, some (.below _ _)) :: rest => by simp [weakenOuts, weakenOuts_fst F rest]

theorem weakenOuts_length (F : List (Expr × Nat)) (outs : List (Var × Option Range)) :
    (weakenOuts F outs).length = outs.length := by
  have := congrArg List.length (weakenOuts_fst F outs); simpa using this

theorem hr_not_lt_of_not_holds {x : Fr} {n w : Nat} (hn : n < 255) (hw : w ≤ n)
    (h : ¬ Range.holds x (.bits n) = true) : ¬ x.val < 2 ^ w := by
  simp [Range.holds, fitsBits, Zkir.frBits, hn] at h
  have := Nat.pow_le_pow_right (by decide : 0 < 2) hw
  omega

/-- What `weakenOuts` drops, spelled out. -/
theorem weakenOuts_dropped {F : List (Expr × Nat)} {v : Var} {n : Nat} {rest : List (Var × Option Range)}
    (hc : (hashImplied F (.var v) n && !(rest.any fun o => o.1 == v)) = true) :
    n < 255 ∧ (∃ y ∈ F, y.1 = .var v ∧ y.2 ≤ n) ∧ v ∉ rest.map Prod.fst := by
  simp only [hashImplied, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, beq_iff_eq,
    Bool.not_eq_true', List.any_eq_false, not_exists, not_and] at hc
  obtain ⟨⟨hn, y, hy, hye, hyw⟩, hr⟩ := hc
  refine ⟨hn, ⟨y, hy, hye, hyw⟩, ?_⟩
  simp only [List.mem_map, not_exists, not_and]
  intro o ho hov
  exact hr o ho (by simp [hov])

theorem hr_readAll_weaken {p : Prims} {F : List (Expr × Nat)} {β : Type} (K : Env × List Fr → Option β)
    (hK : ∀ env r y, y ∈ F → SlotBad p env y → K (env, r) = none) (active : Bool) :
    ∀ (outs : List (Var × Option Range)) (env : Env) (stream : List Fr),
      (readAll active env (weakenOuts F outs) stream).bind K = (readAll active env outs stream).bind K
  | [], _, _ => rfl
  | (v, some (.bits n)) :: rest, env, stream => by
      simp only [weakenOuts]
      split
      · rename_i hc
        obtain ⟨hn, ⟨y, hy, hye, hyw⟩, hv⟩ := weakenOuts_dropped hc
        simp only [readAll, Option.bind_eq_bind]
        cases Zkir.readOne active stream with
        | none => rfl
        | some xs =>
            obtain ⟨x, s'⟩ := xs
            simp only [Option.bind_some]
            by_cases hh : Range.holds x (.bits n) = true
            · simp only [hh, ite_true, Option.pure_def, Option.bind_some]
              exact hr_readAll_weaken K hK active rest _ _
            · simp only [hh, Option.pure_def, Option.bind_none]
              cases hr : readAll active (env.set v x) (weakenOuts F rest) s' with
              | none => rfl
              | some r =>
                  obtain ⟨env', r'⟩ := r
                  simp only [Option.bind_some]
                  apply hK env' r' y hy
                  intro w hw
                  rw [hye] at hw
                  simp only [Expr.eval, Option.some.injEq] at hw
                  have hk := hr_readAll_keeps _ _ _ _ _ hr v (by rw [weakenOuts_fst]; exact hv)
                  rw [← hw, hk]
                  simpa [Env.set] using hr_not_lt_of_not_holds hn hyw hh
      · simp only [readAll, Option.bind_eq_bind]
        cases Zkir.readOne active stream with
        | none => rfl
        | some xs =>
            simp only [Option.bind_some]
            split <;> simp [hr_readAll_weaken K hK active rest]
  | (v, none) :: rest, env, stream | (v, some .zero) :: rest, env, stream
  | (v, some .bool) :: rest, env, stream | (v, some (.below _ _)) :: rest, env, stream => by
      simp only [weakenOuts, readAll, Option.bind_eq_bind]
      cases Zkir.readOne active stream with
      | none => rfl
      | some xs =>
          simp only [Option.bind_some]
          try split
          all_goals simp [hr_readAll_weaken K hK active rest]

theorem hr_assign_weaken {p : Prims} {F : List (Expr × Nat)} {β : Type} (K : Env → Option β)
    (hK : ∀ env y, y ∈ F → SlotBad p env y → K env = none) :
    ∀ (outs : List (Var × Option Range)) (env : Env) (vals : List Fr),
      (Exec.assign env (weakenOuts F outs) vals).bind K = (Exec.assign env outs vals).bind K
  | [], _, _ => rfl
  | (v, some (.bits n)) :: rest, env, [] => by simp only [weakenOuts]; split <;> simp [Exec.assign]
  | (v, none) :: rest, env, [] | (v, some .zero) :: rest, env, []
  | (v, some .bool) :: rest, env, [] | (v, some (.below _ _)) :: rest, env, [] => by
      simp [weakenOuts, Exec.assign]
  | (v, some (.bits n)) :: rest, env, x :: xs => by
      simp only [weakenOuts]
      split
      · rename_i hc
        obtain ⟨hn, ⟨y, hy, hye, hyw⟩, hv⟩ := weakenOuts_dropped hc
        by_cases hh : Range.holds x (.bits n) = true
        · simp only [Exec.assign, hh, ite_true]
          exact hr_assign_weaken K hK rest _ _
        · simp only [Exec.assign, hh]
          simp only [Bool.false_eq_true, ite_false, Option.bind_none]
          cases hr : Exec.assign (env.set v x) (weakenOuts F rest) xs with
          | none => rfl
          | some env' =>
              simp only [Option.bind_some]
              apply hK env' y hy
              intro w hw
              rw [hye] at hw
              simp only [Expr.eval, Option.some.injEq] at hw
              have hk := hr_assign_keeps _ _ _ _ hr v (by rw [weakenOuts_fst]; exact hv)
              rw [← hw, hk]
              simpa [Env.set] using hr_not_lt_of_not_holds hn hyw hh
      · simp only [Exec.assign]
        split <;> simp [hr_assign_weaken K hK rest]
  | (v, none) :: rest, env, x :: xs | (v, some .zero) :: rest, env, x :: xs
  | (v, some .bool) :: rest, env, x :: xs | (v, some (.below _ _)) :: rest, env, x :: xs => by
      simp only [weakenOuts, Exec.assign]
      try split
      all_goals simp [hr_assign_weaken K hK rest]

theorem exec_witness_weaken {p : Prims} {F : List (Expr × Nat)} {β : Type} (K : RunState → Option β)
    (hK : ∀ st y, y ∈ F → SlotBad p st.env y → K st = none) (st : RunState) (g : Expr) (name : String)
    (args : List Expr) (outs : List (Var × Option Range)) (shape : Shape) :
    ((Stmt.witness g name args (weakenOuts F outs) shape).exec p st).bind K =
      ((Stmt.witness g name args outs shape).exec p st).bind K := by
  have he : (weakenOuts F outs).isEmpty = outs.isEmpty := by
    have := weakenOuts_length F outs
    cases h1 : weakenOuts F outs <;> cases h2 : outs <;> simp_all
  simp only [Stmt.exec, Option.bind_eq_bind, he]
  cases g.eval p st.env with
  | none => rfl
  | some gv =>
      simp only [Option.bind_some]
      split
      · rfl
      · cases asBool gv with
        | none => rfl
        | some act =>
            simp only [Option.bind_some, Option.bind_assoc]
            refine hr_readAll_weaken (p := p) _ ?_ act outs st.env st.priv
            intro env r y hy hb
            simpa using hK { st with env, priv := r } y hy hb

theorem step_witness_weaken {p : Prims} {F : List (Expr × Nat)} {ω σ β : Type} (O : Oracles ω σ)
    (K : Exec.State ω σ → Option β)
    (hK : ∀ st y, y ∈ F → SlotBad p st.env y → K st = none) (st : Exec.State ω σ) (g : Expr) (name : String)
    (args : List Expr) (outs : List (Var × Option Range)) (shape : Shape) :
    (Exec.step p O st (Stmt.witness g name args (weakenOuts F outs) shape)).bind K =
      (Exec.step p O st (Stmt.witness g name args outs shape)).bind K := by
  have he : (weakenOuts F outs).isEmpty = outs.isEmpty := by
    have := weakenOuts_length F outs
    cases h1 : weakenOuts F outs <;> cases h2 : outs <;> simp_all
  have hz : (weakenOuts F outs).map (fun _ => (0 : Fr)) = outs.map (fun _ => 0) := by
    have := weakenOuts_fst F outs
    have h := congrArg (List.map fun _ => (0 : Fr)) this
    simpa [List.map_map, Function.comp_def] using h
  simp only [Exec.step, Option.bind_eq_bind, he, hz]
  cases g.eval p st.env with
  | none => rfl
  | some gv =>
      simp only [Option.bind_some]
      split
      · rfl
      · cases asBool gv with
        | none => rfl
        | some act =>
            simp only [Option.bind_some]
            cases act with
            | true =>
                simp only [ite_true]
                cases Expr.evalList p st.env args with
                | none => rfl
                | some argVals =>
                    simp only [Option.bind_some]
                    cases O.witness name argVals st.private_ st.ledger with
                    | none => rfl
                    | some r =>
                        obtain ⟨vals, w, l⟩ := r
                        simp only [Option.bind_some, Option.bind_assoc]
                        refine hr_assign_weaken (p := p) _ ?_ outs st.env vals
                        intro env y hy hb
                        simpa using hK { st with env, private_ := w, ledger := l, priv := st.priv ++ vals } y hy hb
            | false =>
                simp only [Bool.false_eq_true, ite_false, Option.bind_assoc]
                refine hr_assign_weaken (p := p) _ ?_ outs st.env _
                intro env y hy hb
                simpa using hK { st with env } y hy hb

section Pass2
variable {p : Prims} (hp : AlignChecked p)

include hp in
/-- The body with the redundant range checks dropped runs to the same result,
    failures included. -/
theorem hashRangesGo_execAll : ∀ (L : List Stmt) (st : RunState),
    execAll p (hashRangesGo L).1 st = execAll p L st
  | [], _ => rfl
  | s :: rest, st => by
      have ih := hashRangesGo_execAll rest
      have cert : ∀ st y, y ∈ (hashRangesGo rest).2 → SlotBad p st.env y → execAll p rest st = none :=
        fun st y hy hb => (hashRangesGo_certain hp rest y hy).1 st hb
      cases s with
      | constrain e r =>
          cases r with
          | bits n =>
              simp only [hashRangesGo]
              split
              · rename_i hi
                simp only [hashImplied, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
                  beq_iff_eq] at hi
                obtain ⟨hn, y, hy, hye, hyw⟩ := hi
                rw [ih]
                simp only [execAll, Stmt.exec, Option.bind_eq_bind]
                cases hev : e.eval p st.env with
                | none =>
                    apply cert st y hy
                    intro w hw; rw [hye, hev] at hw; simp at hw
                | some x =>
                    simp only [Option.bind_some]
                    by_cases hh : Range.holds x (.bits n) = true
                    · simp [hh]
                    · simp only [hh]
                      simp only [Bool.false_eq_true, ite_false, Option.bind_none]
                      apply cert st y hy
                      intro w hw; rw [hye, hev] at hw
                      simp only [Option.some.injEq] at hw
                      rw [← hw]; exact hr_not_lt_of_not_holds hn hyw hh
              · simp only [execAll, ih]
          | zero | bool | below _ _ => simp only [hashRangesGo, execAll, ih]
      | witness g name args outs shape =>
          simp only [hashRangesGo, execAll, ih]
          exact exec_witness_weaken _ cert st g name args outs shape
      | bind | assert | ledger => simp only [hashRangesGo, execAll, ih]

include hp in
/-- ... and so does the executor, for any oracles. -/
theorem hashRangesGo_steps {ω σ : Type} (O : Oracles ω σ) : ∀ (L : List Stmt) (st : Exec.State ω σ),
    Exec.steps p O (hashRangesGo L).1 st = Exec.steps p O L st
  | [], _ => rfl
  | s :: rest, st => by
      have ih := hashRangesGo_steps O rest
      have cert : ∀ st y, y ∈ (hashRangesGo rest).2 → SlotBad p st.env y → Exec.steps p O rest st = none :=
        fun st y hy hb => (hashRangesGo_certain hp rest y hy).2 O st hb
      cases s with
      | constrain e r =>
          cases r with
          | bits n =>
              simp only [hashRangesGo]
              split
              · rename_i hi
                simp only [hashImplied, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
                  beq_iff_eq] at hi
                obtain ⟨hn, y, hy, hye, hyw⟩ := hi
                rw [ih]
                simp only [Exec.steps, Exec.step, Option.bind_eq_bind]
                cases hev : e.eval p st.env with
                | none =>
                    apply cert st y hy
                    intro w hw; rw [hye, hev] at hw; simp at hw
                | some x =>
                    simp only [Option.bind_some]
                    by_cases hh : Range.holds x (.bits n) = true
                    · simp [hh]
                    · simp only [hh]
                      simp only [Bool.false_eq_true, ite_false, Option.bind_none]
                      apply cert st y hy
                      intro w hw; rw [hye, hev] at hw
                      simp only [Option.some.injEq] at hw
                      rw [← hw]; exact hr_not_lt_of_not_holds hn hyw hh
              · simp only [Exec.steps, ih]
          | zero | bool | below _ _ => simp only [hashRangesGo, Exec.steps, ih]
      | witness g name args outs shape =>
          simp only [hashRangesGo, Exec.steps, ih]
          exact step_witness_weaken O _ cert st g name args outs shape
      | bind | assert | ledger => simp only [hashRangesGo, Exec.steps, ih]

include hp in
/-- `Circuit.hashRanges` is sound for hash functions that refuse inputs that
    do not fit their alignment. -/
theorem Circuit.hashRanges_soundForOf : Pass.SoundFor p Circuit.hashRanges :=
  ⟨fun c inputs priv pub => by
    simp only [Circuit.run, Circuit.hashRanges, List.toList_toArray, hashRangesGo_execAll hp],
   fun O c inputs private_ ledger => by
    simp only [Exec.run, Circuit.hashRanges, List.toList_toArray, hashRangesGo_steps hp O]⟩

end Pass2

/-- `Circuit.hashRanges` is sound for Damp's implementation of Midnight's hash
    functions (`--O3`). -/
theorem Circuit.hashRanges_soundFor : Pass.SoundFor Crypto.prims Circuit.hashRanges :=
  Circuit.hashRanges_soundForOf Crypto.prims_alignChecked

/-! ## Ledger statements are untouched -/

theorem hr_forall_cons_of {P : Stmt → Prop} {s : Stmt} {l : List Stmt} (hs : P s) (hl : ∀ t ∈ l, P t) :
    ∀ t ∈ s :: l, P t := by
  intro t ht
  rcases List.mem_cons.mp ht with rfl | ht
  · exact hs
  · exact hl t ht

theorem hashRangesGo_ledgerProblem : ∀ (L : List Stmt), (∀ s ∈ L, s.ledgerProblem = none) →
    ∀ s ∈ (hashRangesGo L).1, s.ledgerProblem = none
  | [], _ => by simp [hashRangesGo]
  | s :: rest, h => by
      have ih := hashRangesGo_ledgerProblem rest (fun t ht => h t (by simp [ht]))
      have hs := h s (by simp)
      cases s with
      | constrain e r =>
          cases r with
          | bits n =>
              simp only [hashRangesGo]
              split
              · exact ih
              · exact hr_forall_cons_of hs ih
          | zero | bool | below _ _ => simpa only [hashRangesGo] using hr_forall_cons_of hs ih
      | witness g name args outs shape =>
          simp only [hashRangesGo]
          exact hr_forall_cons_of rfl ih
      | bind | assert | ledger => simpa only [hashRangesGo] using hr_forall_cons_of hs ih

end Damp.IR
