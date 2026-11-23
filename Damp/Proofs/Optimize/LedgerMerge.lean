/-
`Circuit.ledgerMerge` (`Damp/Optimize/LedgerMerge.lean`) is sound against the
modelled ledger (`Circuit.ledgerMerge_soundLedger`) and keeps ledger
statements well formed (`Circuit.ledgerMerge_checkLedger`).

* `step_commute`: a ledger statement runs the same before or after a statement
  that is not a ledger statement, when neither reads or binds what the other
  binds (`lcommutes`); so the second ledger statement can be moved up to the
  first (`steps_gap`).
* `step_merge`: two ledger statements that `mergeInto` accepts run, from a
  well-formed ledger state, exactly as their merge: the guard is evaluated
  once (it does not mention the first statement's reads), the second
  statement's operands are evaluated before the first runs (they do not
  mention its reads), the request of the merged program is the two requests
  (`ledgerOracle_merge`), and the read variables are bound in the same order.
* `lmergeGo_steps`: the scan changes nothing the executor does, from a state
  whose ledger is well formed (every ledger state the executor reaches from
  one is, `ledgerOracle_wf`).

The executor's state afterwards is equal, public transcript and public inputs
included: merging changes only how the instructions are grouped into requests.
-/
import Damp.Proofs.Ledger.OptMerge
import Damp.Proofs.Optimize.LedgerReuseBase
import Damp.Proofs.Optimize.LedgerCheck
import Damp.Proofs.Prune
import Damp.Proofs.LedgerAgreement

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Damp.IR
open Damp.Impact Damp.Exec Damp.Ledger
open Damp.Zkir (Prims Group)

/-! ## Requests, public inputs and assignments of concatenated statements -/

section Lists
variable (p : Prims)

theorem lm_request_append (env : Env) : ∀ (a b : List (Op Expr)),
    Exec.request p env (a ++ b) = (Exec.request p env a).bind fun x => (Exec.request p env b).map (x ++ ·)
  | [], b => by simp [Exec.request]
  | op :: a, b => by
      simp only [List.cons_append, Exec.request, Option.bind_eq_bind]
      cases op.mapM (Expr.eval p env) with
      | none => rfl
      | some o =>
        simp only [Option.bind_some]
        rw [lm_request_append env a b]
        cases Exec.request p env a with
        | none => rfl
        | some x => cases Exec.request p env b <;> simp

theorem lm_request_congr {e₁ e₂ : Env} : ∀ (ops : List (Op Expr)), (∀ v ∈ opsVars ops, e₁ v = e₂ v) →
    Exec.request p e₁ ops = Exec.request p e₂ ops
  | [], _ => rfl
  | op :: ops, h => by
      simp only [Exec.request]
      have hop : op.mapM (Expr.eval p e₁) = op.mapM (Expr.eval p e₂) :=
        Op.mapM_congr (c := Expr.const) op fun x hx =>
          eval_congr_of fun w hw => h w (by simp only [opsVars, List.mem_flatMap]; exact ⟨op, by simp, x, hx, hw⟩)
      have hrest : ∀ v ∈ opsVars ops, e₁ v = e₂ v := by
        intro v hv
        apply h v
        simp only [opsVars, List.mem_flatMap] at hv ⊢
        obtain ⟨o, ho, hv⟩ := hv
        exact ⟨o, by simp [ho], hv⟩
      rw [hop, lm_request_congr ops hrest]

theorem lm_ledgerGroups_append (env : Env) (active : Bool) : ∀ (a b : List (Op Expr)),
    ledgerGroups p env active (a ++ b) =
      (ledgerGroups p env active a).bind fun x => (ledgerGroups p env active b).map (x ++ ·)
  | [], b => by simp [ledgerGroups]
  | op :: a, b => by
      simp only [List.cons_append, ledgerGroups, Option.bind_eq_bind]
      cases Expr.evalList p env (op.encode Expr.const) with
      | none => rfl
      | some o =>
        simp only [Option.bind_some]
        rw [lm_ledgerGroups_append env active a b]
        cases ledgerGroups p env active a with
        | none => rfl
        | some x => cases ledgerGroups p env active b <;> simp

theorem ledgerGroups_congr' {e₁ e₂ : Env} (active : Bool) (ops : List (Op Expr))
    (h : ∀ v ∈ opsVars ops, e₁ v = e₂ v) : ledgerGroups p e₁ active ops = ledgerGroups p e₂ active ops :=
  Damp.Emit.ledgerGroups_congr p active ops (fun v hv => h v hv)

end Lists

theorem lm_assign_append : ∀ (env : Env) (rs₁ rs₂ : List Var) (x₁ x₂ : List Fr), x₁.length = rs₁.length →
    Exec.assign env ((rs₁ ++ rs₂).map fun v => (v, none)) (x₁ ++ x₂) =
      (Exec.assign env (rs₁.map fun v => (v, none)) x₁).bind fun e => Exec.assign e (rs₂.map fun v => (v, none)) x₂
  | env, [], rs₂, [], x₂, _ => by simp [Exec.assign]
  | env, r :: rs₁, rs₂, x :: x₁, x₂, h => by
      simp only [List.cons_append, List.map_cons, Exec.assign]
      exact lm_assign_append (env.set r x) rs₁ rs₂ x₁ x₂ (by simpa using h)
  | _, [], _, _ :: _, _, h => by simp at h
  | _, _ :: _, _, [], _, h => by simp at h

theorem lm_assign_length {env env' : Env} {rs : List Var} {xs : List Fr}
    (h : Exec.assign env (rs.map fun v => (v, none)) xs = some env') : xs.length = rs.length := by
  induction rs generalizing env xs with
  | nil => cases xs <;> simp [Exec.assign] at h ⊢
  | cons r rs ih =>
    cases xs with
    | nil => simp [Exec.assign] at h
    | cons x xs => simp only [List.map_cons, Exec.assign] at h; simp [ih h]

/-! ## How many field elements a request reads -/

theorem fieldsOfAtom_length {a : Zkir.AlignAtom} {x : Nat} {f : List Fr} (h : fieldsOfAtom a x = some f) :
    f.length = atomWidth a := by
  cases a with
  | bytes n =>
    simp only [fieldsOfAtom] at h
    split at h
    · simp at h; subst h; simp [atomWidth]; omega
    · split at h
      · simp at h; subst h; simp [atomWidth]; omega
      · simp at h
  | field => simp only [fieldsOfAtom] at h; split at h <;> simp at h <;> subst h <;> rfl
  | compress => simp only [fieldsOfAtom] at h; split at h <;> simp at h <;> subst h <;> rfl

theorem fieldsOf_length : ∀ {a : List Zkir.AlignAtom} {xs : List Nat} {f : List Fr},
    fieldsOf a xs = some f → f.length = (a.map atomWidth).sum
  | [], _, f, h => by simp [fieldsOf] at h; subst h; rfl
  | _ :: _, [], _, h => by simp [fieldsOf] at h
  | a :: as, x :: xs, f, h => by
      simp only [fieldsOf, Option.bind_eq_bind] at h
      obtain ⟨g, hg, h⟩ := bind_some_elim h
      obtain ⟨r, hr, h⟩ := bind_some_elim h
      simp at h; subst h
      simp [fieldsOfAtom_length hg, fieldsOf_length hr]

theorem readBack_width : ∀ {as : List (List Zkir.AlignAtom)} {vs : List AV} {f : List Fr},
    readBack as vs = some f → f.length = (as.map fun a => (a.map atomWidth).sum).sum
  | [], [], f, h => by simp [readBack] at h; subst h; rfl
  | a :: as, v :: vs, f, h => by
      rw [readBack_cons] at h
      obtain ⟨g, hg, h⟩ := bind_some_elim h
      obtain ⟨r, hr, h⟩ := bind_some_elim h
      simp at h; subst h
      simp [fieldsOf_length hg, readBack_width hr]
  | [], _ :: _, _, h => by simp [readBack] at h
  | _ :: _, [], _, h => by simp [readBack] at h

theorem request_aligns {p : Prims} {env : Env} : ∀ {ops : List (Op Expr)} {req : List (Op Fr)},
    Exec.request p env ops = some req → popeqAligns req = opsAligns ops
  | [], req, h => by simp [Exec.request] at h; subst h; rfl
  | op :: ops, req, h => by
      simp only [Exec.request, Option.bind_eq_bind] at h
      obtain ⟨o, ho, h⟩ := bind_some_elim h
      obtain ⟨rest, hrest, h⟩ := bind_some_elim h
      simp at h; subst h
      have ih := request_aligns hrest
      cases op <;> simp [Op.mapM, Option.bind_eq_some_iff] at ho <;>
        (try obtain ⟨_, _, rfl⟩ := ho) <;> (try subst ho) <;> simp [Exec.blank, popeqAligns, opsAligns, ih]

theorem ledgerOracle_width {H : Hooks} {p : Prims} {env : Env} {ops : List (Op Expr)} {req : List (Op Fr)}
    (hr : Exec.request p env ops = some req) {rs : List Var} (hw : widthOk rs ops = true)
    {q q' : LedgerState} {xs : List Fr} (h : ledgerOracle H req q = some (xs, q')) : xs.length = rs.length := by
  unfold ledgerOracle at h
  obtain ⟨rops, _, h⟩ := bind_some_elim h
  obtain ⟨⟨reads, q₁⟩, _, h⟩ := bind_some_elim h
  obtain ⟨vals, hv, h⟩ := bind_some_elim h
  simp at h; obtain ⟨rfl, -⟩ := h
  rw [readBack_width hv, request_aligns hr]
  simpa [widthOk] using hw

/-! ## Two ledger statements as one -/

theorem mergeInto_spec {g : Expr} {rs₁ : List Var} {ops₁ : List (Op Expr)} {l M : Stmt}
    (h : mergeInto g rs₁ ops₁ l = some M) :
    ∃ rs₂ ops₂, l = .ledger g rs₂ ops₂ ∧ M = .ledger g (rs₁ ++ rs₂) (ops₁ ++ ops₂) ∧ ops₁ ≠ [] ∧ ops₂ ≠ [] ∧
      (∀ v ∈ g.vars, v ∉ rs₁) ∧ (∀ v ∈ opsVars ops₂, v ∉ rs₁) ∧ (∀ v ∈ opsVars ops₁, v ∉ rs₂) ∧
      widthOk rs₁ ops₁ = true ∧ widthOk rs₂ ops₂ = true ∧ mergeable ops₁ ops₂ = true := by
  unfold mergeInto at h
  split at h
  · rename_i g₂ rs₂ ops₂
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff,
        List.any_eq_false, Bool.not_eq_true] at hc
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨hg, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, hw1⟩, hw2⟩, hmg⟩ := hc
      simp at h; subst h; subst hg
      refine ⟨rs₂, ops₂, rfl, rfl, h1, h2, ?_, ?_, ?_, hw1, hw2, hmg⟩
      · intro v hv hr; have := h3 v hv; simp_all
      · intro v hv hr; have := h4 v hv; simp_all
      · intro v hv hr; have := h5 v hv; simp_all
    · simp at h
  · simp at h

section Merge
variable {ω σ : Type} (p : Prims)

theorem step_ledger_nf (O : Exec.Oracles ω σ) (s : Exec.State ω σ) (g : Expr) (rs : List Var)
    (ops : List (Op Expr)) (hne : ops ≠ []) :
    Exec.step p O s (.ledger g rs ops) =
      (g.eval p s.env).bind fun gv => (asBool gv).bind fun b =>
        if b then (Exec.request p s.env ops).bind fun req => (O.ledger req s.ledger).bind fun r =>
          (Exec.assign s.env (rs.map fun v => (v, none)) r.1).bind fun env =>
            (ledgerGroups p env true ops).map fun gs =>
              { s with env, ledger := r.2, pub := s.pub ++ r.1, groups := s.groups ++ gs }
        else (Exec.assign s.env (rs.map fun v => (v, none)) (rs.map fun _ => 0)).bind fun env =>
            (ledgerGroups p env false ops).map fun gs => { s with env, groups := s.groups ++ gs } := by
  have he : (rs.isEmpty && ops.isEmpty) = false := by cases ops <;> simp_all
  simp only [Exec.step, he, Bool.false_eq_true, ite_false, Option.bind_eq_bind]
  cases g.eval p s.env with
  | none => rfl
  | some gv =>
    simp only [Option.bind_some]
    cases asBool gv with
    | none => rfl
    | some b =>
      cases b
      · simp only [Option.bind_some, Bool.false_eq_true, ite_false]
        cases Exec.assign s.env (rs.map fun v => (v, none)) (rs.map fun _ => 0) with
        | none => rfl
        | some env => simp only [Option.bind_some]; cases ledgerGroups p env false ops <;> rfl
      · simp only [Option.bind_some, ite_true]
        cases Exec.request p s.env ops with
        | none => rfl
        | some req =>
          simp only [Option.bind_some]
          cases O.ledger req s.ledger with
          | none => rfl
          | some r =>
            simp only [Option.bind_some]
            cases Exec.assign s.env (rs.map fun v => (v, none)) r.1 with
            | none => rfl
            | some env => simp only [Option.bind_some]; cases ledgerGroups p env true ops <;> rfl

theorem assign_zeros (env : Env) (rs : List Var) :
    ∃ env', Exec.assign env (rs.map fun v => (v, none)) (rs.map fun _ => 0) = some env' :=
  assign_plain env rs _ (by simp)

theorem mergeable_parts {ops₁ ops₂ : List (Op Expr)} (h : mergeable ops₁ ops₂ = true) :
    mcheck false mboundary (ops₁.length + 1) ops₁ minit = true ∧
      mcheck true (fun _ => true) (ops₂.length + 1) ops₂ minit = true := by
  simp only [mergeable, Bool.and_eq_true] at h
  exact ⟨h.1.2, h.2⟩

variable (H : Hooks) (w : String → List Fr → ω → Option (List Fr × ω))

/-- **Two statements, one request.** -/
theorem step_merge {g : Expr} {rs₁ : List Var} {ops₁ : List (Op Expr)} {l M : Stmt}
    (hm : mergeInto g rs₁ ops₁ l = some M) (s : Exec.State ω LedgerState) (hwf : s.ledger.WF) :
    (Exec.step p (oracles H w) s (.ledger g rs₁ ops₁)).bind (fun r => Exec.step p (oracles H w) r l) =
      Exec.step p (oracles H w) s M := by
  obtain ⟨rs₂, ops₂, rfl, rfl, hne₁, hne₂, hg, hv₂, hv₁, hw₁, hw₂, hmg⟩ := mergeInto_spec hm
  obtain ⟨hm₁, hm₂⟩ := mergeable_parts hmg
  have hne : ops₁ ++ ops₂ ≠ [] := by simp [hne₁]
  rw [step_ledger_nf p _ s g _ _ hne, step_ledger_nf p _ s g _ _ hne₁]
  -- what the second statement sees after the first bound its reads
  have hframe : ∀ {env₁ : Env} {xs : List Fr}, Exec.assign s.env (rs₁.map fun v => (v, none)) xs = some env₁ →
      g.eval p env₁ = g.eval p s.env ∧ Exec.request p env₁ ops₂ = Exec.request p s.env ops₂ := by
    intro env₁ xs ha
    have hf := fun v (hv : v ∉ rs₁) => assign_frame ha v (by simpa using hv)
    exact ⟨eval_congr_of fun v hv => hf v (hg v hv), lm_request_congr p ops₂ fun v hv => hf v (hv₂ v hv)⟩
  have hgroups : ∀ {env₁ env₂ : Env} {xs : List Fr} (active : Bool),
      Exec.assign env₁ (rs₂.map fun v => (v, none)) xs = some env₂ →
      ledgerGroups p env₂ active ops₁ = ledgerGroups p env₁ active ops₁ := by
    intro env₁ env₂ xs active ha
    exact ledgerGroups_congr' p active ops₁ fun v hv => assign_frame ha v (by simpa using hv₁ v hv)
  cases hgv : g.eval p s.env with
  | none => rfl
  | some gv =>
  simp only [Option.bind_some]
  cases hb : asBool gv with
  | none => rfl
  | some b =>
  simp only [Option.bind_some]
  cases b
  · -- not run
    simp only [Bool.false_eq_true, ite_false]
    obtain ⟨env₁, ha₁⟩ := assign_zeros s.env rs₁
    obtain ⟨env₂, ha₂⟩ := assign_zeros env₁ rs₂
    have ha : Exec.assign s.env ((rs₁ ++ rs₂).map fun v => (v, none)) ((rs₁ ++ rs₂).map fun _ => 0) = some env₂ := by
      rw [List.map_append (f := fun _ => (0 : Fr)), lm_assign_append _ _ _ _ _ (by simp), ha₁]; exact ha₂
    rw [ha₁, ha]
    simp only [Option.bind_some]
    rw [lm_ledgerGroups_append, hgroups false ha₂]
    cases hl₁ : ledgerGroups p env₁ false ops₁ with
    | none => rfl
    | some gs₁ =>
      simp only [Option.map_some, Option.bind_some]
      rw [step_ledger_nf p _ _ g _ _ hne₂]
      simp only [(hframe ha₁).1, hgv, hb, Option.bind_some, Bool.false_eq_true, ite_false, ha₂]
      cases ledgerGroups p env₂ false ops₂ <;> simp [List.append_assoc]
  · -- run
    simp only [ite_true]
    rw [lm_request_append]
    cases hq₁ : Exec.request p s.env ops₁ with
    | none => rfl
    | some req₁ =>
    simp only [Option.bind_some]
    cases hq₂ : Exec.request p s.env ops₂ with
    | none =>
      simp only [Option.map_none, Option.bind_none]
      cases hl : (oracles H w).ledger req₁ s.ledger with
      | none => rfl
      | some r₁ =>
        simp only [Option.bind_some]
        cases ha₁ : Exec.assign s.env (rs₁.map fun v => (v, none)) r₁.1 with
        | none => rfl
        | some env₁ =>
          simp only [Option.bind_some]
          cases ledgerGroups p env₁ true ops₁ with
          | none => rfl
          | some gs₁ =>
            simp only [Option.map_some, Option.bind_some]
            rw [step_ledger_nf p _ _ g _ _ hne₂]
            simp [(hframe ha₁).1, (hframe ha₁).2, hgv, hb, hq₂]
    | some req₂ =>
    simp only [Option.map_some, Option.bind_some]
    simp only [oracles]
    rw [ledgerOracle_merge H hm₁ hm₂ hq₁ hq₂ s.ledger hwf]
    cases ho₁ : ledgerOracle H req₁ s.ledger with
    | none => rfl
    | some r₁ =>
    obtain ⟨x₁, σ₁⟩ := r₁
    have hl₁ := ledgerOracle_width hq₁ hw₁ ho₁
    obtain ⟨env₁, ha₁⟩ := assign_plain s.env rs₁ x₁ hl₁
    simp only [Option.bind_some, ha₁]
    cases ho₂ : ledgerOracle H req₂ σ₁ with
    | none =>
      simp only [Option.map_none, Option.bind_none]
      cases ledgerGroups p env₁ true ops₁ with
      | none => rfl
      | some gs₁ =>
        simp only [Option.map_some, Option.bind_some]
        rw [step_ledger_nf p _ _ g _ _ hne₂]
        simp [(hframe ha₁).1, (hframe ha₁).2, hgv, hb, hq₂, oracles, ho₂]
    | some r₂ =>
    obtain ⟨x₂, σ₂⟩ := r₂
    have hl₂ := ledgerOracle_width hq₂ hw₂ ho₂
    obtain ⟨env₂, ha₂⟩ := assign_plain env₁ rs₂ x₂ hl₂
    simp only [Option.map_some, Option.bind_some]
    rw [lm_assign_append _ _ _ _ _ hl₁, ha₁]
    simp only [Option.bind_some, ha₂]
    rw [lm_ledgerGroups_append, hgroups true ha₂]
    cases ledgerGroups p env₁ true ops₁ with
    | none => rfl
    | some gs₁ =>
      simp only [Option.map_some, Option.bind_some]
      rw [step_ledger_nf p _ _ g _ _ hne₂]
      simp only [(hframe ha₁).1, (hframe ha₁).2, hgv, hb, hq₂, oracles, ho₂, Option.bind_some, ite_true, ha₂]
      cases ledgerGroups p env₂ true ops₂ <;> simp [List.append_assoc]

end Merge

/-! ## A ledger statement moves above a statement that is not one -/

section Commute
variable {ω σ : Type} (p : Prims)

/-- What a statement that is not a ledger statement does: set the variables
    `W` to values `f`, set the private state to `pv`, record `d` in the
    private transcript. -/
structure Patch (ω : Type) where
  W : List Var
  f : Var → Fr
  pv : ω
  d : List Fr

def Patch.env (P : Patch ω) (env : Env) : Env := fun v => if v ∈ P.W then P.f v else env v

def Patch.apply (P : Patch ω) (s : Exec.State ω σ) : Exec.State ω σ :=
  { s with env := P.env s.env, private_ := P.pv, priv := s.priv ++ P.d }

theorem patch_cons_eq (env' env₂ : Env) (v : Var) (x : Fr) (rest : List (Var × Option Range))
    (hv : v ∉ rest.map Prod.fst → env' v = x) :
    (fun u => if u ∈ rest.map Prod.fst then env' u else (env₂.set v x) u) =
      (fun u => if u ∈ (v :: rest.map Prod.fst) then env' u else env₂ u) := by
  funext u
  by_cases hu : u ∈ rest.map Prod.fst
  · simp [hu]
  · by_cases huv : u = v
    · subst huv; simp [hu, Env.set, hv hu]
    · simp [hu, huv, Env.set]

theorem assign_patch : ∀ {env env' : Env} {outs : List (Var × Option Range)} {xs : List Fr},
    Exec.assign env outs xs = some env' →
      ∀ env₂, Exec.assign env₂ outs xs = some (fun v => if v ∈ outs.map Prod.fst then env' v else env₂ v)
  | env, env', [], xs, h, env₂ => by
      cases xs <;> simp [Exec.assign] at h ⊢
  | env, env', (v, r) :: rest, xs, h, env₂ => by
      cases xs with
      | nil => simp [Exec.assign] at h
      | cons x xs =>
        have hv : v ∉ rest.map Prod.fst → ∀ {e : Env}, Exec.assign (e.set v x) rest xs = some env' → env' v = x :=
          fun hn e ha => by rw [assign_frame ha v hn]; simp [Env.set]
        cases r with
        | none =>
          simp only [Exec.assign] at h ⊢
          rw [assign_patch h (env₂.set v x), List.map_cons, ← patch_cons_eq env' env₂ v x rest (fun hn => hv hn h)]
        | some r =>
          simp only [Exec.assign] at h ⊢
          split at h
          · rename_i hr
            rw [if_pos hr, assign_patch h (env₂.set v x), List.map_cons,
              ← patch_cons_eq env' env₂ v x rest (fun hn => hv hn h)]
          · simp at h

theorem assign_none_any : ∀ {env : Env} {outs : List (Var × Option Range)} {xs : List Fr},
    Exec.assign env outs xs = none → ∀ env₂, Exec.assign env₂ outs xs = none
  | env, [], xs, h, env₂ => by cases xs <;> simp [Exec.assign] at h ⊢
  | env, (v, r) :: rest, xs, h, env₂ => by
      cases xs with
      | nil => simp [Exec.assign]
      | cons x xs =>
        cases r with
        | none => simp only [Exec.assign] at h ⊢; exact assign_none_any h _
        | some r =>
          simp only [Exec.assign] at h ⊢
          split at h
          · rw [if_pos ‹_›]; exact assign_none_any h _
          · rw [if_neg ‹_›]

theorem patch_nil_apply (t : Exec.State ω σ) (f : Var → Fr) :
    ({ W := [], f := f, pv := t.private_, d := [] } : Patch ω).apply t = t := by
  cases t; simp only [Patch.apply, List.append_nil]; congr 1

/-- A statement that is not a ledger statement is a patch, the same for every
    state that agrees on what it reads and on the private state. -/
theorem step_patch (O : Exec.Oracles ω σ) (st : Stmt) (hst : st.isLedger = false) (s : Exec.State ω σ) :
    ∃ o : Option (Patch ω), (∀ P ∈ o, ∀ v ∈ P.W, v ∈ st.mBinds) ∧
      ∀ t : Exec.State ω σ, (∀ v ∈ st.mUses, t.env v = s.env v) → t.private_ = s.private_ →
        Exec.step p O t st = o.map (·.apply t) := by
  cases st with
  | ledger => simp [Stmt.isLedger] at hst
  | bind v hint e =>
    refine ⟨(e.eval p s.env).map fun x => ⟨[v], fun _ => x, s.private_, []⟩, ?_, ?_⟩
    · intro P hP u hu
      cases he : e.eval p s.env <;> simp [he] at hP; subst hP; simpa [Stmt.mBinds] using hu
    · intro t ht hpr
      have he : e.eval p t.env = e.eval p s.env := eval_congr_of fun w hw => ht w (by simpa [Stmt.mUses] using hw)
      simp only [Exec.step, he]
      cases e.eval p s.env with
      | none => rfl
      | some x =>
        simp only [Option.bind_eq_bind, Option.bind_some, Option.map_some, Patch.apply, Patch.env, ← hpr]
        simp only [List.append_nil, List.mem_singleton, Option.pure_def, Option.some.injEq]
        congr 1
        funext u; simp [Env.set, Patch.env]
  | assert c msg =>
    refine ⟨((c.eval p s.env).bind asBool).bind fun b => if b then some ⟨[], fun _ => 0, s.private_, []⟩ else none,
      ?_, ?_⟩
    · intro P hP u hu
      simp only [Option.mem_def, Option.bind_eq_some_iff] at hP
      obtain ⟨b, _, hP⟩ := hP; split at hP <;> simp at hP; subst hP; simp at hu
    · intro t ht hpr
      have he : c.eval p t.env = c.eval p s.env := eval_congr_of fun w hw => ht w (by simpa [Stmt.mUses] using hw)
      simp only [Exec.step, he]
      cases c.eval p s.env with
      | none => rfl
      | some x =>
        cases hb : asBool x with
        | none => simp [hb]
        | some b =>
          rw [← hpr]; cases b <;> simp [hb, patch_nil_apply]
  | constrain e r =>
    refine ⟨(e.eval p s.env).bind fun x => if r.holds x then some ⟨[], fun _ => 0, s.private_, []⟩ else none,
      ?_, ?_⟩
    · intro P hP u hu
      simp only [Option.mem_def, Option.bind_eq_some_iff] at hP
      obtain ⟨b, _, hP⟩ := hP; split at hP <;> simp at hP; subst hP; simp at hu
    · intro t ht hpr
      have he : e.eval p t.env = e.eval p s.env := eval_congr_of fun w hw => ht w (by simpa [Stmt.mUses] using hw)
      simp only [Exec.step, he]
      cases e.eval p s.env with
      | none => rfl
      | some x =>
        simp only [Option.bind_some]
        rw [← hpr]; by_cases hr : r.holds x <;> simp [hr, patch_nil_apply]
  | witness g name args outs sh =>
    let o : Option (Patch ω) := (g.eval p s.env).bind fun gv =>
      if outs.isEmpty then
        if gv = 1 then
          (Expr.evalList p s.env args).bind fun argVals => (O.witness name argVals s.private_).bind fun r =>
            if r.1.isEmpty then some ⟨[], fun _ => 0, r.2, []⟩ else none
        else some ⟨[], fun _ => 0, s.private_, []⟩
      else (asBool gv).bind fun b =>
        if b then
          (Expr.evalList p s.env args).bind fun argVals => (O.witness name argVals s.private_).bind fun r =>
            (Exec.assign s.env outs r.1).map fun env' => ⟨outs.map Prod.fst, env', r.2, r.1⟩
        else (Exec.assign s.env outs (outs.map fun _ => 0)).map fun env' => ⟨outs.map Prod.fst, env', s.private_, []⟩
    refine ⟨o, ?_, ?_⟩
    · intro P hP u hu
      simp only [o, Option.mem_def, Option.bind_eq_some_iff] at hP
      obtain ⟨gv, _, hP⟩ := hP
      split at hP
      · split at hP
        · simp only [Option.bind_eq_some_iff] at hP
          obtain ⟨_, _, r, _, hP⟩ := hP; split at hP <;> simp at hP; subst hP; simp at hu
        · simp at hP; subst hP; simp at hu
      · simp only [Option.bind_eq_some_iff] at hP
        obtain ⟨b, _, hP⟩ := hP
        split at hP
        · simp only [Option.bind_eq_some_iff] at hP
          obtain ⟨_, _, r, _, hP⟩ := hP
          obtain ⟨env', _, hP⟩ := Option.map_eq_some_iff.mp hP
          subst hP; simpa [Stmt.mBinds] using hu
        · obtain ⟨env', _, hP⟩ := Option.map_eq_some_iff.mp hP
          subst hP; simpa [Stmt.mBinds] using hu
    · intro t ht hpr
      have hg : g.eval p t.env = g.eval p s.env :=
        eval_congr_of fun w hw => ht w (by simp [Stmt.mUses, hw])
      have ha : Expr.evalList p t.env args = Expr.evalList p s.env args :=
        evalList_congr_of fun w hw => ht w (by simp [Stmt.mUses, hw])
      simp only [Exec.step, hg, ha, hpr, o, Option.bind_eq_bind]
      cases hgv : g.eval p s.env with
      | none => rfl
      | some gv =>
        simp only [Option.bind_some]
        by_cases he : outs.isEmpty = true
        · simp only [he, ite_true]
          by_cases h1 : gv = 1
          · simp only [h1, ite_true]
            cases hav : Expr.evalList p s.env args with
            | none => rfl
            | some av =>
              simp only [Option.bind_some]
              cases hw : O.witness name av s.private_ with
              | none => rfl
              | some r =>
                obtain ⟨vals, pv⟩ := r
                simp only [Option.bind_some]
                by_cases hv : vals.isEmpty = true
                · simp only [hv, ite_true, Option.map_some, Option.pure_def, Option.some.injEq]
                  cases t; simp only [Patch.apply, List.append_nil]; congr 1
                · simp [hv]
          · simp only [h1, ite_false, Option.map_some, Option.pure_def, Option.some.injEq]
            rw [← hpr, patch_nil_apply]
        · simp only [he, Bool.false_eq_true, ite_false]
          cases hb : asBool gv with
          | none => rfl
          | some b =>
            simp only [Option.bind_some]
            cases b
            · simp only [Bool.false_eq_true, ite_false]
              cases hz : Exec.assign s.env outs (outs.map fun _ => 0) with
              | none => simp [assign_none_any hz t.env]
              | some env' =>
                simp only [assign_patch hz t.env, Option.bind_some, Option.map_some, Option.pure_def,
                  Option.some.injEq]
                cases t; simp only at hpr; subst hpr; simp only [Patch.apply, List.append_nil]; rfl
            · simp only [ite_true]
              cases hav : Expr.evalList p s.env args with
              | none => rfl
              | some av =>
                simp only [Option.bind_some]
                cases hw : O.witness name av s.private_ with
                | none => rfl
                | some r =>
                  obtain ⟨vals, pv⟩ := r
                  simp only [Option.bind_some]
                  cases hz : Exec.assign s.env outs vals with
                  | none => simp [assign_none_any hz t.env]
                  | some env' =>
                    simp only [assign_patch hz t.env, Option.bind_some, Option.map_some, Option.pure_def,
                      Option.some.injEq]
                    simp only [Patch.apply]; rfl

theorem assign_patchenv (P : Patch ω) : ∀ (e : Env) (rs : List Var) (xs : List Fr), (∀ v ∈ rs, v ∉ P.W) →
    Exec.assign (P.env e) (rs.map fun v => (v, none)) xs = (Exec.assign e (rs.map fun v => (v, none)) xs).map P.env
  | e, [], xs, _ => by cases xs <;> simp [Exec.assign]
  | e, r :: rs, [], _ => by simp [Exec.assign]
  | e, r :: rs, x :: xs, h => by
      simp only [List.map_cons, Exec.assign]
      have : (P.env e).set r x = P.env (e.set r x) := by
        funext u
        simp only [Env.set, Patch.env]
        by_cases hu : u ∈ P.W
        · have : u ≠ r := fun hur => h r (by simp) (hur ▸ hu)
          simp [hu, this]
        · simp [hu]
      rw [this]
      exact assign_patchenv P (e.set r x) rs xs fun v hv => h v (by simp [hv])

/-- A patch that does not touch what a ledger statement reads or binds commutes with it. -/
theorem step_ledger_patch (O : Exec.Oracles ω σ) (P : Patch ω) (s : Exec.State ω σ) (g : Expr) (rs : List Var)
    (ops : List (Op Expr)) (hne : ops ≠ []) (hu : ∀ v ∈ g.vars ++ opsVars ops, v ∉ P.W)
    (hb : ∀ v ∈ rs, v ∉ P.W) :
    Exec.step p O (P.apply s) (.ledger g rs ops) = (Exec.step p O s (.ledger g rs ops)).map P.apply := by
  have hagree : ∀ e : Env, ∀ v, v ∉ P.W → P.env e v = e v := fun e v hv => by simp [Patch.env, hv]
  rw [step_ledger_nf p O _ g rs ops hne, step_ledger_nf p O _ g rs ops hne]
  have hg : g.eval p (P.apply s).env = g.eval p s.env :=
    eval_congr_of fun w hw => hagree _ w (hu w (by simp [hw]))
  have hq : Exec.request p (P.apply s).env ops = Exec.request p s.env ops :=
    lm_request_congr p ops fun w hw => hagree _ w (hu w (by simp [hw]))
  have hl : ∀ (act : Bool) (e : Env), ledgerGroups p (P.env e) act ops = ledgerGroups p e act ops :=
    fun act e => ledgerGroups_congr' p act ops fun w hw => hagree _ w (hu w (by simp [hw]))
  rw [hg, hq]
  cases g.eval p s.env with
  | none => rfl
  | some gv =>
    simp only [Option.bind_some]
    cases asBool gv with
    | none => rfl
    | some b =>
      simp only [Option.bind_some]
      cases b
      · simp only [Bool.false_eq_true, ite_false]
        show (Exec.assign (P.env s.env) _ _).bind _ = _
        rw [assign_patchenv P s.env rs _ hb]
        cases Exec.assign s.env (rs.map fun v => (v, none)) (rs.map fun _ => 0) with
        | none => rfl
        | some env =>
          simp only [Option.map_some, Option.bind_some, hl]
          cases ledgerGroups p env false ops <;> rfl
      · simp only [ite_true]
        cases Exec.request p s.env ops with
        | none => rfl
        | some req =>
          simp only [Option.bind_some]
          show (O.ledger req s.ledger).bind _ = _
          cases O.ledger req s.ledger with
          | none => rfl
          | some r =>
            simp only [Option.bind_some]
            show (Exec.assign (P.env s.env) _ _).bind _ = _
            rw [assign_patchenv P s.env rs _ hb]
            cases Exec.assign s.env (rs.map fun v => (v, none)) r.1 with
            | none => rfl
            | some env =>
              simp only [Option.map_some, Option.bind_some, hl]
              cases ledgerGroups p env true ops <;> rfl

theorem ledger_step_private (O : Exec.Oracles ω σ) {s r : Exec.State ω σ} {g : Expr} {rs : List Var}
    {ops : List (Op Expr)} (h : Exec.step p O s (.ledger g rs ops) = some r) : r.private_ = s.private_ := by
  simp only [Exec.step, Option.bind_eq_bind] at h
  cases hg : g.eval p s.env with
  | none => simp [hg] at h
  | some gv =>
    simp only [hg, Option.bind_some] at h
    split at h
    · simp at h; subst h; rfl
    · cases hb : asBool gv with
      | none => simp [hb] at h
      | some b =>
        cases b
        · simp only [hb, Option.bind_some, Bool.false_eq_true, ite_false] at h
          obtain ⟨env, _, h⟩ := bind_some_elim h
          obtain ⟨gs, _, h⟩ := bind_some_elim h
          simp at h; subst h; rfl
        · simp only [hb, Option.bind_some, ite_true] at h
          obtain ⟨req, _, h⟩ := bind_some_elim h
          obtain ⟨x, _, h⟩ := bind_some_elim h
          obtain ⟨env, _, h⟩ := bind_some_elim h
          obtain ⟨gs, _, h⟩ := bind_some_elim h
          simp at h; subst h; rfl

/-- **A ledger statement and a statement that is not one commute**, when
    neither reads or binds what the other binds. -/
theorem step_commute (O : Exec.Oracles ω σ) (x : Stmt) (hx : x.isLedger = false) (g : Expr) (rs : List Var)
    (ops : List (Op Expr)) (hne : ops ≠ []) (hc : lcommutes (.ledger g rs ops) x = true) (s : Exec.State ω σ) :
    (Exec.step p O s x).bind (fun r => Exec.step p O r (.ledger g rs ops)) =
      (Exec.step p O s (.ledger g rs ops)).bind (fun r => Exec.step p O r x) := by
  simp only [lcommutes, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false, Bool.or_eq_false_iff] at hc
  obtain ⟨hc1, hc2⟩ := hc
  obtain ⟨o, hW, ho⟩ := step_patch p O x hx s
  rw [ho s (fun _ _ => rfl) rfl]
  -- after the ledger statement, `x` sees what it saw before
  have hafter : ∀ r, Exec.step p O s (.ledger g rs ops) = some r → Exec.step p O r x = o.map (·.apply r) := by
    intro r hr
    apply ho r
    · intro v hv
      apply step_env_frame p O hr v
      intro hvr
      have := hc2 v (by simpa [Stmt.mBinds, Stmt.lrBinds] using hvr)
      simp [hv] at this
    · exact ledger_step_private p O hr
  cases o with
  | none =>
    simp only [Option.map_none, Option.bind_none]
    cases h : Exec.step p O s (.ledger g rs ops) with
    | none => rfl
    | some r => simp [hafter r h]
  | some P =>
    simp only [Option.map_some, Option.bind_some]
    have hPW : ∀ v ∈ P.W, v ∈ x.mBinds := hW P rfl
    rw [step_ledger_patch p O P s g rs ops hne
      (fun v hv hvW => by have := hc1 v (by simpa [Stmt.mUses] using hv); simp [hPW v hvW] at this)
      (fun v hv hvW => by have := hc2 v (by simpa [Stmt.mBinds] using hv); simp [hPW v hvW] at this)]
    cases h : Exec.step p O s (.ledger g rs ops) with
    | none => rfl
    | some r => simp [hafter r h]

/-- The ledger statement `l` moves above statements it commutes with. -/
theorem steps_gap (O : Exec.Oracles ω σ) (g : Expr) (rs : List Var) (ops : List (Op Expr)) (hne : ops ≠ []) :
    ∀ (gap R : List Stmt), (∀ x ∈ gap, x.isLedger = false ∧ lcommutes (.ledger g rs ops) x = true) →
      ∀ s, Exec.steps p O (gap ++ .ledger g rs ops :: R) s = Exec.steps p O (.ledger g rs ops :: gap ++ R) s
  | [], R, _, s => rfl
  | x :: gap, R, h, s => by
      have hx := h x (by simp)
      have ih := steps_gap O g rs ops hne gap R (fun y hy => h y (by simp [hy]))
      simp only [List.cons_append, Exec.steps, Option.bind_eq_bind]
      have e1 : (Exec.step p O s x).bind (fun r => Exec.steps p O (gap ++ .ledger g rs ops :: R) r) =
          ((Exec.step p O s x).bind fun r => Exec.step p O r (.ledger g rs ops)).bind
            (fun r => Exec.steps p O (gap ++ R) r) := by
        cases Exec.step p O s x with
        | none => rfl
        | some r => simp only [Option.bind_some]; rw [ih r]; rfl
      rw [e1, step_commute p O x hx.1 g rs ops hne hx.2 s]
      cases Exec.step p O s (.ledger g rs ops) with
      | none => rfl
      | some r => rfl

end Commute

theorem nextLedger_spec : ∀ {n : Nat} {l : List Stmt} {gap rest : List Stmt} {st : Stmt},
    nextLedger n l = some (gap, st, rest) → l = gap ++ st :: rest ∧ ∀ x ∈ gap, x.isLedger = false
  | 0, _, _, _, _, h => by simp [nextLedger] at h
  | _ + 1, [], _, _, _, h => by simp [nextLedger] at h
  | n + 1, s :: l, gap, rest, st, h => by
      simp only [nextLedger] at h
      split at h
      · simp at h; obtain ⟨rfl, rfl, rfl⟩ := h; simp
      · rename_i hs
        obtain ⟨⟨gap', st', rest'⟩, h', h⟩ := Option.map_eq_some_iff.mp h
        simp at h; obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨rfl, hg⟩ := nextLedger_spec h'
        refine ⟨by simp, fun x hx => ?_⟩
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · simpa using hs
        · exact hg x hx

/-! ## The scan -/

section Go
variable {ω : Type} (p : Prims) (H : Hooks) (w : String → List Fr → ω → Option (List Fr × ω))

theorem step_wf {s r : Exec.State ω LedgerState} {st : Stmt} (h : Exec.step p (oracles H w) s st = some r)
    (hwf : s.ledger.WF) : r.ledger.WF := by
  cases st with
  | ledger g rs ops =>
    rcases step_ledger_cases p _ h with ⟨_, rfl⟩ | ⟨gv, _, h⟩
    · exact hwf
    · rcases h with ⟨_, hl, _⟩ | ⟨_, req, xs, _, ho, _⟩
      · rw [hl]; exact hwf
      · exact ledgerOracle_wf ho
  | _ => rw [step_ledger_same p _ h (by simp)]; exact hwf

theorem lmergeGo_steps : ∀ (fuel : Nat) (stmts : List Stmt) (s : Exec.State ω LedgerState), s.ledger.WF →
    Exec.steps p (oracles H w) (lmergeGo fuel stmts) s = Exec.steps p (oracles H w) stmts s
  | 0, stmts, s, _ => rfl
  | _ + 1, [], s, _ => rfl
  | fuel + 1, st :: rest, s, hwf => by
      have keep : Exec.steps p (oracles H w) (st :: lmergeGo fuel rest) s = Exec.steps p (oracles H w) (st :: rest) s := by
        simp only [Exec.steps, Option.bind_eq_bind]
        cases h : Exec.step p (oracles H w) s st with
        | none => rfl
        | some r => exact lmergeGo_steps fuel rest r (step_wf p H w h hwf)
      unfold lmergeGo
      split
      · rename_i g rs ops
        split
        · rename_i gap l rest' hn
          split
          · rename_i hall
            split
            · rename_i M hm
              rw [lmergeGo_steps fuel _ s hwf]
              obtain ⟨rs₂, ops₂, rfl, rfl, hne₁, hne₂, -⟩ := mergeInto_spec hm
              obtain ⟨rfl, hgap⟩ := nextLedger_spec hn
              have hc : ∀ x ∈ gap, x.isLedger = false ∧ lcommutes (.ledger g rs₂ ops₂) x = true :=
                fun x hx => ⟨hgap x hx, List.all_eq_true.mp hall x hx⟩
              simp only [Exec.steps, Option.bind_eq_bind]
              have e1 : (Exec.step p (oracles H w) s (.ledger g rs ops)).bind
                  (fun r => Exec.steps p (oracles H w) (gap ++ .ledger g rs₂ ops₂ :: rest') r) =
                  ((Exec.step p (oracles H w) s (.ledger g rs ops)).bind
                    fun r => Exec.step p (oracles H w) r (.ledger g rs₂ ops₂)).bind
                    (fun r => Exec.steps p (oracles H w) (gap ++ rest') r) := by
                cases Exec.step p (oracles H w) s (.ledger g rs ops) with
                | none => rfl
                | some r =>
                  simp only [Option.bind_some]
                  rw [steps_gap p _ g rs₂ ops₂ hne₂ gap rest' hc r]
                  rfl
              rw [e1, step_merge p H w hm s hwf]
              rfl
            · exact keep
          · exact keep
        · exact keep
      · exact keep

end Go

/-- `Circuit.ledgerMerge` is sound against the modelled ledger: from a
    well-formed ledger state the executor does exactly what it does on the
    original circuit (only the grouping of the instructions into requests
    differs, which none of the compared results records). -/
theorem Circuit.ledgerMerge_soundLedger : Pass.SoundLedger Circuit.ledgerMerge := by
  refine ⟨fun {ω} H p w c inputs pr σ hσ => ?_⟩
  simp only [Exec.run, Circuit.ledgerMerge, List.toList_toArray, Option.bind_eq_bind]
  cases bindInputs (fun _ => 0) c.inputs inputs with
  | none => rfl
  | some env =>
    simp only [Option.bind_some]
    rw [lmergeGo_steps p H w _ c.body.toList ⟨env, [], [], [], pr, σ⟩ hσ]


/-! ## Merged statements are well formed -/

theorem blank_encode_sub (op : Op Expr) : ∀ x ∈ op.blank.encode Expr.const, x ∈ op.encode Expr.const := by
  intro x hx
  cases op with
  | popeq c a r =>
    simp only [Op.blank, Op.encode, List.append_nil] at hx ⊢
    exact List.mem_append_left _ hx
  | _ => exact hx

theorem results_encode_sub (op : Op Expr) : ∀ x ∈ op.results, x ∈ op.encode Expr.const := by
  intro x hx
  cases op <;> simp_all [Op.results, Op.encode]

theorem mem_opsVars {ops : List (Op Expr)} {op : Op Expr} (hop : op ∈ ops) {x : Expr} (hx : x ∈ op.encode Expr.const)
    {v : Var} (hv : v ∈ x.vars) : v ∈ opsVars ops := by
  simp only [opsVars, List.mem_flatMap]; exact ⟨op, hop, x, hx, hv⟩

theorem blank_vars_opsVars {ops : List (Op Expr)} {v : Var}
    (hv : v ∈ Expr.varsList (ops.flatMap fun op => op.blank.encode Expr.const)) : v ∈ opsVars ops := by
  rw [Damp.Emit.varsList_eq_flatMap] at hv
  simp only [List.mem_flatMap] at hv
  obtain ⟨x, ⟨op, hop, hx⟩, hv⟩ := hv
  exact mem_opsVars hop (blank_encode_sub op x hx) hv

theorem reads_opsVars {ops : List (Op Expr)} {rs : List Var} (h : allResults ops = rs.map Expr.var) {v : Var}
    (hv : v ∈ rs) : v ∈ opsVars ops := by
  have : Expr.var v ∈ allResults ops := by rw [h]; exact List.mem_map_of_mem hv
  simp only [allResults, List.mem_flatMap] at this
  obtain ⟨op, hop, hx⟩ := this
  exact mem_opsVars hop (results_encode_sub op _ hx) (by simp [Expr.vars])

theorem merged_ledgerProblem {rs₁ rs₂ : List Var} {ops₁ ops₂ : List (Op Expr)}
    (h₁ : ledgerProblem rs₁ ops₁ = none) (h₂ : ledgerProblem rs₂ ops₂ = none)
    (hv₂ : ∀ v ∈ opsVars ops₂, v ∉ rs₁) (hv₁ : ∀ v ∈ opsVars ops₁, v ∉ rs₂) :
    ledgerProblem (rs₁ ++ rs₂) (ops₁ ++ ops₂) = none := by
  rw [LedgerWF.ledgerProblem_none_iff] at h₁ h₂ ⊢
  obtain ⟨a₁, n₁, b₁⟩ := h₁
  obtain ⟨a₂, n₂, b₂⟩ := h₂
  refine ⟨by simp [allResults, a₁, a₂] at *; simp [← a₁, ← a₂, allResults], ?_, ?_⟩
  · rw [List.nodup_append]
    exact ⟨n₁, n₂, fun a ha b hb hab => by subst hab; exact hv₁ a (reads_opsVars a₁ ha) hb⟩
  · intro v hv hmem
    rw [List.flatMap_append, LedgerWF.varsList_append, List.mem_append] at hv
    rcases hv with hv | hv
    · rcases List.mem_append.mp hmem with h | h
      · exact b₁ v hv h
      · exact hv₁ v (blank_vars_opsVars hv) h
    · rcases List.mem_append.mp hmem with h | h
      · exact hv₂ v (blank_vars_opsVars hv) h
      · exact b₂ v hv h

theorem lmergeGo_ledgerProblem : ∀ (fuel : Nat) (stmts : List Stmt), (∀ s ∈ stmts, s.ledgerProblem = none) →
    ∀ s ∈ lmergeGo fuel stmts, s.ledgerProblem = none
  | 0, stmts, h => by simpa [lmergeGo] using h
  | _ + 1, [], _ => by simp [lmergeGo]
  | fuel + 1, st :: rest, h => by
      have keep : ∀ s ∈ st :: lmergeGo fuel rest, s.ledgerProblem = none := by
        intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact h s (by simp)
        · exact lmergeGo_ledgerProblem fuel rest (fun x hx => h x (by simp [hx])) s hs
      unfold lmergeGo
      split
      · rename_i g rs ops
        split
        · rename_i gap l rest' hn
          split
          · split
            · rename_i M hm
              apply lmergeGo_ledgerProblem
              obtain ⟨rs₂, ops₂, rfl, rfl, -, -, -, hv₂, hv₁, -⟩ := mergeInto_spec hm
              obtain ⟨rfl, -⟩ := nextLedger_spec hn
              intro x hx
              simp only [List.cons_append, List.mem_cons, List.mem_append] at hx
              rcases hx with rfl | hx | hx
              · have h1 := h (.ledger g rs ops) (by simp)
                have h2 := h (.ledger g rs₂ ops₂) (by simp)
                exact merged_ledgerProblem h1 h2 hv₂ hv₁
              · exact h x (by simp [hx])
              · exact h x (by simp [hx])
            · exact keep
          · exact keep
        · exact keep
      · exact keep

/-- `Circuit.ledgerMerge` keeps a circuit's ledger statements well formed. -/
theorem Circuit.ledgerMerge_checkLedger : Pass.KeepsLedger Circuit.ledgerMerge := by
  intro c h
  rw [LedgerWF.Circuit.checkLedger_ok_iff] at h ⊢
  intro s hs
  simp only [Circuit.ledgerMerge, List.toList_toArray] at hs
  exact lmergeGo_ledgerProblem _ _ h s hs

end Damp.IR
