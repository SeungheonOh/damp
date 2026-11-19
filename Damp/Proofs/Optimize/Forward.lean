/-
Soundness of forward substitution (`Damp/Optimize/Forward.lean`).

The invariant (`Forward.AllHold`): every remembered binding `v := e` has, in
the current environment, `e` evaluating to the value of `v`. Then substituting
the remembered bindings into an expression does not change its value or its
failure (`Forward.subst_eval`, from `Expr.subst_eval` of the simplifier). Every
statement is kept and binds exactly what it bound before, so the original and
the rewritten circuit go through the same environments, and each rewritten
statement runs exactly as the original (`Forward.stmt_exec`, `Forward.stmt_step`).
The invariant survives a statement because what it forgets is everything that
mentions a variable the statement binds (`Forward.AllHold.kill`), and what it
adds after `bind v _ e` does not mention `v`.

Ledger statements: the operands are rewritten only with bindings that mention
no read variable, so they mean the same before the reads (the request) and
after (the public inputs).

So `Circuit.forwardWith` changes no run at all, whatever the eligibility test
(`Circuit.forwardWith_run`, `Circuit.forwardWith_exec`), keeps `checkLedger`
(`Circuit.forwardWith_checkLedger`), and `Circuit.forward` and
`Circuit.forwardOpt` are sound passes.
-/
import Damp.Optimize.Forward
import Damp.Proofs.Optimize.Algebra
import Damp.Proofs.Optimize.Choose
import Damp.Proofs.Optimize.Bounds
import Damp.Proofs.Prune

set_option linter.unusedSimpArgs false

namespace Damp.IR
namespace Forward
open Damp.Zkir (Prims)

section Inv
variable (p : Prims)

/-- Every remembered binding holds in `env`. -/
def AllHold (env : Env) (m : Map) : Prop := ∀ v e, (v, e) ∈ m → e.eval p env = some (env v)

variable {p}

theorem allHold_nil (env : Env) : AllHold p env [] := fun _ _ h => nomatch h

theorem lookup_mem : ∀ {m : Map} {v : Var} {e : Expr}, m.lookup v = some e → (v, e) ∈ m
  | [], _, _, h => by simp [List.lookup] at h
  | (w, f) :: m, v, e, h => by
      by_cases hv : v = w
      · subst hv
        simp [List.lookup] at h
        subst h
        exact List.mem_cons_self ..
      · have hb : (v == w) = false := by simpa using hv
        simp only [List.lookup, hb] at h
        exact List.mem_cons_of_mem _ (lookup_mem h)

theorem AllHold.known {env : Env} {m : Map} (h : AllHold p env m) : KnownHolds p env env m := by
  intro v
  cases hl : m.lookup v with
  | none => simp [Expr.subst, hl, Expr.eval]
  | some e =>
      simp only [Expr.subst, hl, Option.getD_some]
      exact h v e (lookup_mem hl)

/-- Substituting remembered bindings that hold changes no value and no failure. -/
theorem subst_eval {env : Env} {m : Map} (h : AllHold p env m) (e : Expr) :
    (e.subst m).eval p env = e.eval p env :=
  Expr.subst_eval p env env m h.known e

theorem evalList_map_subst {env : Env} {m : Map} (h : AllHold p env m) :
    ∀ xs : List Expr, Expr.evalList p env (xs.map (Expr.subst m)) = Expr.evalList p env xs
  | [] => rfl
  | x :: xs => by
      simp only [List.map_cons, Expr.evalList, subst_eval h x, evalList_map_subst h xs]

/-- What is left after forgetting everything that touches `L` holds in any
    environment that agrees with `env` outside `L`. -/
theorem AllHold.kill {env env' : Env} {m : Map} {L : List Var} (h : AllHold p env m)
    (hu : ∀ w, w ∉ L → env' w = env w) : AllHold p env' (kill m L) := by
  intro v e hmem
  obtain ⟨hm, hc⟩ := List.mem_filter.mp hmem
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
  have hv : v ∉ L := by
    intro hv
    have : L.contains v = true := List.contains_iff_mem.mpr hv
    rw [this] at hc
    simp at hc
  have hvars : ∀ u, u ∈ e.vars → u ∉ L := by
    intro u hu' huL
    have : e.vars.any L.contains = true := List.any_eq_true.mpr ⟨u, hu', List.contains_iff_mem.mpr huL⟩
    rw [this] at hc
    simp at hc
  rw [Emit.eval_congr p e (fun u hu' => hu u (hvars u hu')), h v e hm, hu v hv]

/-- After `bind v _ e'` with value `x`, what is remembered holds. -/
theorem AllHold.bind {env : Env} {m : Map} {v : Var} {e' : Expr} {x : Fr} (h : AllHold p env m)
    (hx : e'.eval p env = some x) (b : Bool) :
    AllHold p (env.set v x)
      (if b && !(e'.vars.contains v) then (v, e') :: Forward.kill m [v] else Forward.kill m [v]) := by
  have hu : ∀ w, w ∉ [v] → env.set v x w = env w := by
    intro w hw
    simp only [List.mem_singleton] at hw
    simp [Env.set, hw]
  have hk := h.kill hu
  split
  · next hc =>
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
    have hnv : v ∉ e'.vars := by
      intro hv
      have : e'.vars.contains v = true := List.contains_iff_mem.mpr hv
      rw [this] at hc
      simp at hc
    intro w f hmem
    rcases List.mem_cons.mp hmem with heq | hmem
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      have hag : Emit.Agree f.vars (env.set w x) env := by
        intro u hu'
        have : u ≠ w := fun h' => hnv (h' ▸ hu')
        simp [Env.set, this]
      rw [Emit.eval_congr p f hag, hx]
      simp [Env.set]
    · exact hk w f hmem
  · exact hk

end Inv

/-! ## Ledger instructions -/

section Ops
variable {p : Prims}

theorem request_subst {env : Env} {m : Map} (h : AllHold p env m) :
    ∀ ops : List (Impact.Op Expr), Exec.request p env (ops.map (·.map (Expr.subst m))) = Exec.request p env ops
  | [] => rfl
  | op :: ops => by
      simp only [List.map_cons, Exec.request]
      rw [Exec.Op.mapM_map (Expr.subst m) (Expr.eval p env) (Expr.eval p env) (subst_eval h) op,
        request_subst h ops]

theorem ledgerGroups_subst {env : Env} {m : Map} (h : AllHold p env m) (active : Bool) :
    ∀ ops : List (Impact.Op Expr), ledgerGroups p env active (ops.map (·.map (Expr.subst m))) =
      ledgerGroups p env active ops
  | [] => rfl
  | op :: ops => by
      simp only [List.map_cons, ledgerGroups]
      rw [Op.encode_map (Expr.subst m) (fun _ => rfl), evalList_map_subst h, ledgerGroups_subst h active ops]

/-- The instructions a rewritten ledger statement carries. -/
abbrev newOps (m : Map) (reads : List Var) (ops : List (Impact.Op Expr)) : List (Impact.Op Expr) :=
  if (IR.ledgerProblem reads (ops.map (·.map (Expr.subst m)))).isNone then
    ops.map (·.map (Expr.subst m)) else ops

theorem newOps_isEmpty (m : Map) (reads : List Var) (ops : List (Impact.Op Expr)) :
    (newOps m reads ops).isEmpty = ops.isEmpty := by
  simp only [newOps]; split <;> cases ops <;> rfl

theorem newOps_groups {env : Env} {m : Map} (h : AllHold p env m) (reads : List Var) (active : Bool)
    (ops : List (Impact.Op Expr)) :
    ledgerGroups p env active (newOps m reads ops) = ledgerGroups p env active ops := by
  simp only [newOps]; split
  · exact ledgerGroups_subst h active ops
  · rfl

theorem newOps_request {env : Env} {m : Map} (h : AllHold p env m) (reads : List Var)
    (ops : List (Impact.Op Expr)) :
    Exec.request p env (newOps m reads ops) = Exec.request p env ops := by
  simp only [newOps]; split
  · exact request_subst h ops
  · rfl

end Ops

theorem bind_congr' {α β : Type} {x : Option α} {f g : α → Option β} (h : ∀ a, x = some a → f a = g a) :
    x.bind f = x.bind g := by
  cases x with
  | none => rfl
  | some a => exact h a rfl

theorem stmt_ledger (elig : Var → Expr → Bool) (m : Map) (g : Expr) (reads : List Var)
    (ops : List (Impact.Op Expr)) :
    stmt elig m (.ledger g reads ops) = (.ledger (g.subst m) reads (newOps (kill m reads) reads ops), kill m reads) :=
  rfl

/-! ## Statements, in the semantics -/

section Run
variable (p : Prims) (elig : Var → Expr → Bool)

/-- A rewritten statement runs exactly as the original, and what is remembered
    after it holds of the state it leaves. -/
theorem stmt_exec {m : Map} {s : RunState} (h : AllHold p s.env m) (st : Stmt) :
    (stmt elig m st).1.exec p s = st.exec p s ∧
      ∀ s', st.exec p s = some s' → AllHold p s'.env (stmt elig m st).2 := by
  cases st with
  | bind v hint e =>
      refine ⟨by simp only [stmt, Stmt.exec, subst_eval h], ?_⟩
      intro s' hs
      simp only [Stmt.exec, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        Option.some.injEq] at hs
      obtain ⟨x, hx, rfl⟩ := hs
      exact h.bind (by rw [subst_eval h]; exact hx) _
  | assert c msg =>
      refine ⟨by simp only [stmt, Stmt.exec, subst_eval h], ?_⟩
      intro s' hs
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at hs
      obtain ⟨x, _, b, _, hs⟩ := hs
      cases b
      · simp at hs
      · simp only [ite_true, Option.pure_def, Option.some.injEq] at hs
        subst hs; exact h
  | constrain e r =>
      refine ⟨by simp only [stmt, Stmt.exec, subst_eval h], ?_⟩
      intro s' hs
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at hs
      obtain ⟨x, _, hs⟩ := hs
      split at hs
      · simp only [Option.pure_def, Option.some.injEq] at hs; subst hs; exact h
      · cases hs
  | witness g name args outs shape =>
      refine ⟨by simp only [stmt, Stmt.exec, subst_eval h], ?_⟩
      intro s' hs
      simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at hs
      obtain ⟨gx, _, hs⟩ := hs
      split at hs
      · simp only [Option.pure_def, Option.some.injEq] at hs; subst hs
        exact h.kill (fun _ _ => rfl)
      · simp only [Option.bind_eq_some_iff] at hs
        obtain ⟨act, _, ⟨r, pv⟩, hrd, hs⟩ := hs
        simp only [Option.pure_def, Option.some.injEq] at hs; subst hs
        exact h.kill (readAll_unchanged hrd)
  | ledger g reads ops =>
      have hk : AllHold p s.env (kill m reads) := h.kill (fun _ _ => rfl)
      constructor
      · rw [stmt_ledger]
        simp only [Stmt.exec, Option.bind_eq_bind, subst_eval h, newOps_isEmpty]
        apply bind_congr'; intro gx _
        split
        · rfl
        apply bind_congr'; intro act _
        apply bind_congr'; intro ⟨r, pv⟩ hrd
        have hu := readAll_unchanged hrd
        rw [reads_vars] at hu
        (try dsimp only); rw [newOps_groups (h.kill hu)]
      · intro s' hs
        rw [stmt_ledger]
        simp only [Stmt.exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at hs
        obtain ⟨gx, _, hs⟩ := hs
        split at hs
        · simp only [Option.pure_def, Option.some.injEq] at hs; subst hs
          exact hk
        · simp only [Option.bind_eq_some_iff] at hs
          obtain ⟨act, _, ⟨r, pv⟩, hrd, gs, _, hs⟩ := hs
          simp only [Option.pure_def, Option.some.injEq] at hs; subst hs
          have hu := readAll_unchanged hrd
          rw [reads_vars] at hu
          exact h.kill hu

theorem go_exec : ∀ (m : Map) (l : List Stmt) (s : RunState), AllHold p s.env m →
    execAll p (go elig m l).1 s = execAll p l s ∧
      ∀ s', execAll p l s = some s' → AllHold p s'.env (go elig m l).2
  | m, [], s, h => ⟨rfl, fun s' hs => by cases hs; exact h⟩
  | m, st :: rest, s, h => by
      obtain ⟨h1, h2⟩ := stmt_exec p elig h st
      simp only [go, execAll, Option.bind_eq_bind, h1]
      constructor
      · cases hs : st.exec p s with
        | none => rfl
        | some s1 => exact (go_exec _ rest s1 (h2 s1 hs)).1
      · intro s' hs
        simp only [Option.bind_eq_some_iff] at hs
        obtain ⟨s1, hs1, hs⟩ := hs
        exact (go_exec _ rest s1 (h2 s1 hs1)).2 s' hs

end Run

/-! ## Statements, in the executor -/

section Executor
variable {ω σ : Type} (p : Prims) (O : Exec.Oracles ω σ) (elig : Var → Expr → Bool)

/-- A rewritten statement runs in the executor exactly as the original, and
    what is remembered after it holds of the state it leaves. -/
theorem stmt_step {m : Map} {s : Exec.State ω σ} (h : AllHold p s.env m) (st : Stmt) :
    Exec.step p O s (stmt elig m st).1 = Exec.step p O s st ∧
      ∀ s', Exec.step p O s st = some s' → AllHold p s'.env (stmt elig m st).2 := by
  cases st with
  | bind v hint e =>
      refine ⟨by simp only [stmt, Exec.step, subst_eval h], ?_⟩
      intro s' hs
      simp only [Exec.step, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        Option.some.injEq] at hs
      obtain ⟨x, hx, rfl⟩ := hs
      exact h.bind (by rw [subst_eval h]; exact hx) _
  | assert c msg =>
      refine ⟨by simp only [stmt, Exec.step, subst_eval h], ?_⟩
      intro s' hs
      simp only [Exec.step, Option.bind_eq_bind, Option.bind_eq_some_iff] at hs
      obtain ⟨x, _, b, _, hs⟩ := hs
      cases b
      · simp at hs
      · simp only [ite_true, Option.pure_def, Option.some.injEq] at hs
        subst hs; exact h
  | constrain e r =>
      refine ⟨by simp only [stmt, Exec.step, subst_eval h], ?_⟩
      intro s' hs
      simp only [Exec.step, Option.bind_eq_bind, Option.bind_eq_some_iff] at hs
      obtain ⟨x, _, hs⟩ := hs
      split at hs
      · simp only [Option.pure_def, Option.some.injEq] at hs; subst hs; exact h
      · cases hs
  | witness g name args outs shape =>
      refine ⟨by simp only [stmt, Exec.step, subst_eval h, evalList_map_subst h], ?_⟩
      intro s' hs
      simp only [Exec.step, Option.bind_eq_bind, Option.bind_eq_some_iff] at hs
      obtain ⟨gx, _, hs⟩ := hs
      split at hs
      · have he : s'.env = s.env := by
          split at hs
          · simp only [Option.bind_eq_some_iff] at hs
            obtain ⟨_, _, ⟨vals, pv⟩, _, hs⟩ := hs
            split at hs
            · simp only [Option.pure_def, Option.some.injEq] at hs; subst hs; rfl
            · cases hs
          · simp only [Option.pure_def, Option.some.injEq] at hs; subst hs; rfl
        rw [he]
        exact h.kill (fun _ _ => rfl)
      · simp only [Option.bind_eq_some_iff] at hs
        obtain ⟨act, _, hs⟩ := hs
        split at hs
        · simp only [Option.bind_eq_some_iff] at hs
          obtain ⟨_, _, ⟨vals, pv⟩, _, r, hasg, hs⟩ := hs
          simp only [Option.pure_def, Option.some.injEq] at hs; subst hs
          exact h.kill (Bounds.assign_post hasg).1
        · simp only [Option.bind_eq_some_iff] at hs
          obtain ⟨r, hasg, hs⟩ := hs
          simp only [Option.pure_def, Option.some.injEq] at hs; subst hs
          exact h.kill (Bounds.assign_post hasg).1
  | ledger g reads ops =>
      have hk : AllHold p s.env (kill m reads) := h.kill (fun _ _ => rfl)
      constructor
      · rw [stmt_ledger]
        simp only [Exec.step, Option.bind_eq_bind, subst_eval h, newOps_isEmpty, newOps_request hk]
        apply bind_congr'; intro gx _
        split
        · rfl
        apply bind_congr'; intro act _
        split
        · apply bind_congr'; intro req _
          apply bind_congr'; intro ⟨vals, lg⟩ _
          apply bind_congr'; intro r hasg
          have hu := (Bounds.assign_post hasg).1
          rw [reads_vars] at hu
          (try dsimp only); rw [newOps_groups (h.kill hu)]
        · apply bind_congr'; intro r hasg
          have hu := (Bounds.assign_post hasg).1
          rw [reads_vars] at hu
          (try dsimp only); rw [newOps_groups (h.kill hu)]
      · intro s' hs
        rw [stmt_ledger]
        simp only [Exec.step, Option.bind_eq_bind, Option.bind_eq_some_iff] at hs
        obtain ⟨gx, _, hs⟩ := hs
        split at hs
        · simp only [Option.pure_def, Option.some.injEq] at hs; subst hs
          exact hk
        · simp only [Option.bind_eq_some_iff] at hs
          obtain ⟨act, _, hs⟩ := hs
          split at hs
          · simp only [Option.bind_eq_some_iff] at hs
            obtain ⟨_, _, ⟨vals, lg⟩, _, r, hasg, gs, _, hs⟩ := hs
            simp only [Option.pure_def, Option.some.injEq] at hs; subst hs
            have hu := (Bounds.assign_post hasg).1
            rw [reads_vars] at hu
            exact h.kill hu
          · simp only [Option.bind_eq_some_iff] at hs
            obtain ⟨r, hasg, gs, _, hs⟩ := hs
            simp only [Option.pure_def, Option.some.injEq] at hs; subst hs
            have hu := (Bounds.assign_post hasg).1
            rw [reads_vars] at hu
            exact h.kill hu

theorem go_steps : ∀ (m : Map) (l : List Stmt) (s : Exec.State ω σ), AllHold p s.env m →
    Exec.steps p O (go elig m l).1 s = Exec.steps p O l s ∧
      ∀ s', Exec.steps p O l s = some s' → AllHold p s'.env (go elig m l).2
  | m, [], s, h => ⟨rfl, fun s' hs => by cases hs; exact h⟩
  | m, st :: rest, s, h => by
      obtain ⟨h1, h2⟩ := stmt_step p O elig h st
      simp only [go, Exec.steps, Option.bind_eq_bind, h1]
      constructor
      · cases hs : Exec.step p O s st with
        | none => rfl
        | some s1 => exact (go_steps _ rest s1 (h2 s1 hs)).1
      · intro s' hs
        simp only [Option.bind_eq_some_iff] at hs
        obtain ⟨s1, hs1, hs⟩ := hs
        exact (go_steps _ rest s1 (h2 s1 hs1)).2 s' hs

end Executor

/-! ## Ledger well-formedness -/

theorem stmt_ledgerProblem (elig : Var → Expr → Bool) (m : Map) (st : Stmt) (h : st.ledgerProblem = none) :
    (stmt elig m st).1.ledgerProblem = none := by
  cases st with
  | ledger g reads ops =>
      rw [stmt_ledger]
      simp only [Stmt.ledgerProblem, newOps] at h ⊢
      split
      · next h' => exact Option.isNone_iff_eq_none.mp h'
      · exact h
  | _ => rfl

theorem go_ledgerProblem (elig : Var → Expr → Bool) : ∀ (m : Map) (l : List Stmt),
    (∀ s ∈ l, s.ledgerProblem = none) → ∀ x ∈ (go elig m l).1, x.ledgerProblem = none
  | _, [], _ => by simp [go]
  | m, st :: rest, h => by
      intro x hx
      simp only [go, List.mem_cons] at hx
      rcases hx with hx | hx
      · subst hx; exact stmt_ledgerProblem elig m st (h st (by simp))
      · exact go_ledgerProblem elig _ rest (fun s hs => h s (by simp [hs])) x hx

end Forward

open Damp.Zkir (Prims)

/-- Forward substitution changes no run at all, whatever the eligibility test. -/
theorem Circuit.forwardWith_run (elig : Var → Expr → Bool) (p : Prims) (c : Circuit)
    (inputs priv pub : List Fr) :
    (c.forwardWith elig).run p inputs priv pub = c.run p inputs priv pub := by
  simp only [Circuit.run, Circuit.forwardWith, List.toList_toArray, Option.bind_eq_bind]
  cases bindInputs (fun _ => 0) c.inputs inputs with
  | none => rfl
  | some env0 =>
      simp only [Option.bind_some]
      obtain ⟨h1, h2⟩ := Forward.go_exec p elig [] c.body.toList { env := env0, priv, pub }
        (Forward.allHold_nil _)
      rw [h1]
      cases h : execAll p c.body.toList { env := env0, priv, pub } with
      | none => rfl
      | some s' =>
          simp only [Option.bind_some]
          rw [Forward.evalList_map_subst (h2 s' h)]

/-- The executor runs the rewritten circuit exactly as the original, whatever
    the eligibility test. -/
theorem Circuit.forwardWith_exec (elig : Var → Expr → Bool) {ω σ : Type} (p : Prims)
    (O : Exec.Oracles ω σ) (c : Circuit) (inputs : List Fr) (private_ : ω) (ledger : σ) :
    Exec.run p O (c.forwardWith elig) inputs private_ ledger = Exec.run p O c inputs private_ ledger := by
  simp only [Exec.run, Circuit.forwardWith, List.toList_toArray, Option.bind_eq_bind]
  cases bindInputs (fun _ => 0) c.inputs inputs with
  | none => rfl
  | some env0 =>
      simp only [Option.bind_some]
      obtain ⟨h1, h2⟩ := Forward.go_steps p O elig [] c.body.toList { env := env0, private_, ledger }
        (Forward.allHold_nil _)
      rw [h1]
      cases h : Exec.steps p O c.body.toList { env := env0, private_, ledger } with
      | none => rfl
      | some s' =>
          simp only [Option.bind_some]
          rw [Forward.evalList_map_subst (h2 s' h)]

/-- Forward substitution keeps a circuit's ledger statements well formed. -/
theorem Circuit.forwardWith_checkLedger (elig : Var → Expr → Bool) (c : Circuit)
    (h : c.checkLedger = .ok ()) : (c.forwardWith elig).checkLedger = .ok () := by
  simp only [Circuit.checkLedger, Circuit.forwardWith, List.toList_toArray] at h ⊢
  rw [Bounds.checkLedgerFrom_ok] at h ⊢
  exact Forward.go_ledgerProblem elig [] _ h

theorem Circuit.forwardWith_sound (elig : Var → Expr → Bool) : Pass.Sound (Circuit.forwardWith elig) :=
  ⟨fun p c i pr pu => by rw [Circuit.forwardWith_run],
   fun p O c i w l => by rw [Circuit.forwardWith_exec]⟩

/-- Forward substitution is sound: for every circuit and input it changes
    neither what a run produces nor what the executor does. -/
theorem Circuit.forward_sound : Pass.Sound Circuit.forward :=
  ⟨fun p c i pr pu => by simp only [Circuit.forward, Circuit.forwardWith_run],
   fun p O c i w l => by simp only [Circuit.forward, Circuit.forwardWith_exec]⟩

theorem Circuit.forwardAll_sound : Pass.Sound Circuit.forwardAll :=
  Circuit.forwardWith_sound _

/-- `forward` keeps a circuit's ledger statements well formed. -/
theorem Circuit.forward_checkLedger (c : Circuit) (h : c.checkLedger = .ok ()) :
    (Circuit.forward c).checkLedger = .ok () :=
  Circuit.forwardWith_checkLedger _ c h

/-- `forward` followed by `algebra` and `simplify`, kept only when smaller, is sound. -/
theorem Circuit.forwardOpt_sound : Pass.Sound Circuit.forwardOpt :=
  Pass.Sound.choose
    (Pass.Sound.comp (Pass.Sound.comp Circuit.forward_sound Circuit.algebra_sound) Circuit.simplify_sound)
    Pass.Sound.id _

end Damp.IR
