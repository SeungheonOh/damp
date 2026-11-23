/-
`Circuit.ledgerReuse` (`Damp/Optimize/LedgerReuse.lean`) is sound against the
modelled ledger: `Circuit.ledgerReuse_soundLedger : Pass.SoundLedger
Circuit.ledgerReuse`.

The proof runs the original and the rewritten circuit side by side with the
executor, the ledger being `ledgerOracle H`. The two states agree on
everything but the public transcript and public inputs (`State.obs`), and every
fact the pass holds is true (`LFact.Holds`): the fact's guard evaluates to a
boolean; if it is on, the plain read it describes answers the fact's values
on the current ledger state (`readSpec`, `Damp/Proofs/Ledger/OptVm.lean`);
if off, the values are zeros. The ledger state stays well formed
(`ledgerOracle_wf`). A plain read answered by a fact is then exactly the
bindings the pass puts in its place: the original statement cannot fail, and
leaves the ledger state as it was.
-/
import Damp.Proofs.Optimize.LedgerReuseBase
import Damp.Proofs.Ledger.Cell

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Damp.IR
open Damp.Impact Damp.Exec Damp.Ledger
open Damp.Zkir (Prims Group)

section
variable (p : Prims)

/-- What a fact claims, at environment `env` and ledger state `q`. -/
def LFact.Holds (f : LFact) (env : Env) (q : LedgerState) : Prop :=
  f.n ≤ 2 ∧ ∃ gv b, f.guard.eval p env = some gv ∧ asBool gv = some b ∧
    (∀ k ∈ f.path, ∀ x ∈ k.vals, (x.eval p env).isSome) ∧
    (b = true → ∃ path' xs, f.path.mapM (fun k : Aligned Expr => k.mapM (Expr.eval p env)) = some path' ∧
        readSpec f.n path' f.align q = some xs ∧ Expr.evalList p env f.vals = some xs) ∧
    (b = false → Expr.evalList p env f.vals = some (f.vals.map fun _ => 0))

/-- The invariant of the scan. -/
def LInv (fs : List LFact) (env : Env) (q : LedgerState) : Prop := q.WF ∧ ∀ f ∈ fs, f.Holds p env q

/-! ### Facts and the environment -/

theorem pathMapM_congr {e₁ e₂ : Env} : ∀ (path : List (Aligned Expr)), (∀ w ∈ pathVars path, e₁ w = e₂ w) →
    path.mapM (fun k : Aligned Expr => k.mapM (Expr.eval p e₁)) =
      path.mapM (fun k : Aligned Expr => k.mapM (Expr.eval p e₂))
  | [], _ => rfl
  | k :: ks, h => by
      have hk : k.vals.mapM (Expr.eval p e₁) = k.vals.mapM (Expr.eval p e₂) := by
        rw [← evalList_eq_mapM, ← evalList_eq_mapM]
        exact evalList_congr_of fun w hw => h w (by simp [pathVars, List.mem_flatMap]; exact Or.inl hw)
      have ih := pathMapM_congr ks fun w hw => h w (by
        simp only [pathVars, List.flatMap_cons, List.mem_append] at hw ⊢; exact Or.inr hw)
      rw [List.mapM_cons, List.mapM_cons, ih]
      simp only [Aligned.mapM, hk]

theorem LFact.Holds.env {f : LFact} {env env' : Env} {q : LedgerState} (h : f.Holds p env q)
    (he : ∀ w ∈ f.vars, env' w = env w) : f.Holds p env' q := by
  obtain ⟨hn, gv, b, hg, hb, hpath, hon, hoff⟩ := h
  have hg' : f.guard.vars ⊆ f.vars := fun w hw => by simp [LFact.vars, hw]
  have hp' : pathVars f.path ⊆ f.vars := fun w hw => by simp [LFact.vars, hw]
  have hv' : Expr.varsList f.vals ⊆ f.vars := fun w hw => by simp [LFact.vars, hw]
  refine ⟨hn, gv, b, ?_, hb, ?_, ?_, ?_⟩
  · rw [eval_congr_of (fun w hw => he w (hg' hw))]; exact hg
  · intro k hk x hx
    rw [eval_congr_of (fun w hw => he w (hp' (by
      simp only [pathVars, List.mem_flatMap]; exact ⟨k, hk, mem_varsList hx hw⟩)))]
    exact hpath k hk x hx
  · intro hb1
    obtain ⟨path', xs, h1, h2, h3⟩ := hon hb1
    refine ⟨path', xs, ?_, h2, ?_⟩
    · rw [pathMapM_congr p f.path (fun w hw => he w (hp' hw))]; exact h1
    · rw [evalList_congr_of (fun w hw => he w (hv' hw))]; exact h3
  · intro hb0
    rw [evalList_congr_of (fun w hw => he w (hv' hw))]; exact hoff hb0

theorem LFact.Holds.ledger {f : LFact} {env : Env} {q q' : LedgerState} (h : f.Holds p env q)
    (hq : q'.comp f.n = q.comp f.n) : f.Holds p env q' := by
  obtain ⟨hn, gv, b, hg, hb, hpath, hon, hoff⟩ := h
  refine ⟨hn, gv, b, hg, hb, hpath, fun hb1 => ?_, hoff⟩
  obtain ⟨path', xs, h1, h2, h3⟩ := hon hb1
  exact ⟨path', xs, h1, by rw [readSpec_congr hq]; exact h2, h3⟩

theorem mem_forgetVars {vs : List Var} {fs : List LFact} {f : LFact} (h : f ∈ forgetVars vs fs) :
    f ∈ fs ∧ ∀ w ∈ f.vars, w ∉ vs := by
  simp only [forgetVars, List.mem_filter, Bool.not_eq_true', List.any_eq_false] at h
  exact ⟨h.1, fun w hw hv => h.2 w hw (by simpa using hv)⟩

theorem mem_addFact {f g : LFact} {fs : List LFact} (h : f ∈ addFact g fs) : f = g ∨ f ∈ fs := by
  have := List.mem_of_mem_take h
  simpa using this

/-! ### Recognizing the statements -/

theorem alignedSame_eq {x y : Aligned Expr} (h : alignedSame x y = true) : x = y := by
  cases x; cases y
  simp only [alignedSame, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h; subst h1 h2; rfl

theorem pathSame_eq : ∀ {x y : List (Aligned Expr)}, pathSame x y = true → x = y
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
      simp only [pathSame, Bool.and_eq_true] at h
      rw [alignedSame_eq h.1, pathSame_eq h.2]
  | [], _ :: _, h => by simp [pathSame] at h
  | _ :: _, [], h => by simp [pathSame] at h

theorem plainRead?_spec {rs : List Var} {ops : List (Op Expr)} {n : Nat} {path : List (Aligned Expr)}
    {a : List Zkir.AlignAtom} (h : plainRead? rs ops = some (n, path, a)) :
    ∃ ci c, ops = [.dup n, .idx ci false path, .popeq c a (rs.map Expr.var)] ∧ n ≤ 2 ∧ (ci = false ∨ 1 ≤ n) ∧
      rs ≠ [] ∧ rs.Nodup ∧ ∀ w ∈ pathVars path, w ∉ rs := by
  unfold plainRead? at h
  split at h
  · rename_i n' ci path' c a' res
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff,
        beq_iff_eq, List.any_eq_false, Bool.or_eq_true] at hc
      have h1 := hc.1.1.1.1.1
      have h0 := hc.1.1.1.1.2
      have h2 := hc.1.1.1.2
      have h3 := hc.1.1.2
      have h4 := hc.1.2
      have h5 := hc.2
      exact ⟨ci, c, by rw [h3], h1, by simpa using h0, h2, h4, fun w hw hr => h5 w hw (by simpa using hr)⟩
    · simp at h
  · simp at h

theorem findFact_spec {g : Expr} {n : Nat} {path : List (Aligned Expr)} {a : List Zkir.AlignAtom} {rs : List Var} :
    ∀ {fs : List LFact} {f : LFact}, findFact g n path a rs fs = some f →
      f ∈ fs ∧ f.guard = g ∧ f.n = n ∧ f.path = path ∧ f.align = a ∧ f.vals.length = rs.length ∧
        ∀ w ∈ Expr.varsList f.vals, w ∉ rs
  | [], f, h => by simp [findFact] at h
  | f' :: fs, f, h => by
      unfold findFact at h
      split at h
      · rename_i hc
        simp only [Option.some.injEq] at h; subst h
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.any_eq_false] at hc
        have h1 := hc.1.1.1.1.1
        have h2 := hc.1.1.1.1.2
        have h3 := hc.1.1.1.2
        have h4 := hc.1.1.2
        have h5 := hc.1.2
        have h7 := hc.2
        exact ⟨List.mem_cons_self .., h1, h2, pathSame_eq h3, h4, h5, fun w hw hr => h7 w hw (by simpa using hr)⟩
      · have := findFact_spec h
        exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩

theorem cellWrite?_spec {ops : List (Op Expr)} {k v : Aligned Expr} (h : cellWrite? ops = some (k, v)) :
    ops = [.push false k, .push true v, .ins false 1] := by
  unfold cellWrite? at h
  split at h
  · simp at h; obtain ⟨rfl, rfl⟩ := h; rfl
  · simp at h

theorem singleLimb_spec {a : List Zkir.AlignAtom} (h : singleLimb a = true) : SingleLimb a := by
  intro x hx n hn
  subst hn
  have := List.all_eq_true.mp h _ hx
  simpa using this

/-! ### Public inputs of a plain read -/

theorem evalList_append_isSome {env : Env} {xs ys : List Expr} :
    (Expr.evalList p env (xs ++ ys)).isSome ↔ (Expr.evalList p env xs).isSome ∧ (Expr.evalList p env ys).isSome := by
  simp only [evalList_isSome_iff, List.mem_append]
  constructor
  · intro h; exact ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩
  · rintro ⟨h1, h2⟩ x (hx | hx)
    · exact h1 x hx
    · exact h2 x hx

theorem const_isSome (env : Env) (c : Int) : ((Expr.const c).eval p env).isSome := rfl

theorem ledgerGroups_isSome_iff (env : Env) (act : Bool) :
    ∀ ops : List (Op Expr), (ledgerGroups p env act ops).isSome ↔
      ∀ op ∈ ops, (Expr.evalList p env (op.encode Expr.const)).isSome
  | [] => by simp [ledgerGroups]
  | op :: ops => by
      have ih := ledgerGroups_isSome_iff env act ops
      simp only [ledgerGroups, List.mem_cons, forall_eq_or_imp]
      cases h1 : Expr.evalList p env (op.encode Expr.const) <;>
        cases h2 : ledgerGroups p env act ops <;> simp_all

theorem encode_aligned_isSome (env : Env) (k : Aligned Expr) :
    (Expr.evalList p env (k.encode Expr.const)).isSome ↔ ∀ x ∈ k.vals, (x.eval p env).isSome := by
  simp only [Aligned.encode, evalList_isSome_iff, List.mem_cons, List.mem_append, List.mem_map]
  constructor
  · intro h x hx; exact h x (Or.inr hx)
  · rintro h x ((rfl | ⟨a, _, rfl⟩) | hx)
    · rfl
    · rfl
    · exact h x hx

theorem plain_groups_isSome (env : Env) (act : Bool) (n : Nat) (path : List (Aligned Expr)) (ci c : Bool)
    (a : List Zkir.AlignAtom) (rs : List Var) :
    (ledgerGroups p env act [.dup n, .idx ci false path, .popeq c a (rs.map Expr.var)]).isSome ↔
      ∀ k ∈ path, ∀ x ∈ k.vals, (x.eval p env).isSome := by
  rw [ledgerGroups_isSome_iff]
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  have hdup : (Expr.evalList p env ((Op.dup n : Op Expr).encode Expr.const)).isSome := by
    simp [Op.encode, Expr.evalList, Expr.eval]
  have hpop : (Expr.evalList p env ((Op.popeq c a (rs.map Expr.var) : Op Expr).encode Expr.const)).isSome := by
    simp only [Op.encode, evalList_isSome_iff, List.mem_cons, List.mem_append, List.mem_map]
    rintro x ((rfl | rfl | ⟨_, _, rfl⟩) | ⟨v, _, rfl⟩) <;> rfl
  simp only [hdup, hpop, true_and, and_true]
  simp only [Op.encode, evalList_isSome_iff, List.mem_cons, List.mem_flatMap, forall_eq_or_imp]
  constructor
  · rintro ⟨_, h⟩ k hk x hx
    exact h x ⟨k, hk, by simp [Aligned.encode, hx]⟩
  · intro h
    refine ⟨rfl, ?_⟩
    rintro x ⟨k, hk, hx⟩
    exact (encode_aligned_isSome p env k).mpr (h k hk) |> fun hh =>
      (evalList_isSome_iff p env _).mp hh x hx

theorem write_groups_isSome {env : Env} {act : Bool} {k v : Aligned Expr}
    (h : (ledgerGroups p env act [.push false k, .push true v, .ins false 1]).isSome) :
    (∀ x ∈ k.vals, (x.eval p env).isSome) ∧ (∀ x ∈ v.vals, (x.eval p env).isSome) := by
  rw [ledgerGroups_isSome_iff] at h
  have hk := h _ (List.mem_cons_self ..)
  have hv := h (.push true v) (by simp)
  simp only [Op.encode, evalList_isSome_iff, List.mem_cons] at hk hv
  refine ⟨fun x hx => hk x (Or.inr (Or.inr ?_)), fun x hx => hv x (Or.inr (Or.inr ?_))⟩
  all_goals simp [Aligned.encode, hx]

theorem pathMapM_isSome {env : Env} : ∀ {path : List (Aligned Expr)} {path'},
    path.mapM (fun k : Aligned Expr => k.mapM (Expr.eval p env)) = some path' →
      ∀ k ∈ path, ∀ x ∈ k.vals, (x.eval p env).isSome
  | [], _, _ => by simp
  | k :: ks, path', h => by
      simp only [List.mapM_cons] at h
      cases hk : k.mapM (Expr.eval p env) with
      | none => simp [hk] at h
      | some k' =>
        cases hks : ks.mapM (fun k : Aligned Expr => k.mapM (Expr.eval p env)) with
        | none => simp [hk, hks] at h
        | some ks' =>
          intro k₀ hk₀ x hx
          rcases List.mem_cons.mp hk₀ with rfl | hk₀
          · have := (aligned_mapM_vals _ _ _ hk).2
            rw [← evalList_eq_mapM] at this
            exact (evalList_isSome_iff p env _).mp (by simp [this]) x hx
          · exact pathMapM_isSome hks k₀ hk₀ x hx

theorem pathMapM_some {env : Env} : ∀ {path : List (Aligned Expr)},
    (∀ k ∈ path, ∀ x ∈ k.vals, (x.eval p env).isSome) →
      ∃ path', path.mapM (fun k : Aligned Expr => k.mapM (Expr.eval p env)) = some path'
  | [], _ => ⟨[], rfl⟩
  | k :: ks, h => by
      obtain ⟨ks', hks⟩ := pathMapM_some (path := ks) fun k hk => h k (List.mem_cons_of_mem _ hk)
      have hv : (Expr.evalList p env k.vals).isSome := (evalList_isSome_iff p env _).mpr (h k (List.mem_cons_self ..))
      rw [evalList_eq_mapM] at hv
      obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp hv
      have hk : k.mapM (Expr.eval p env) = some ⟨k.align, vs⟩ := by simp [Aligned.mapM, hvs]
      exact ⟨⟨k.align, vs⟩ :: ks', by rw [List.mapM_cons, hk, hks]; rfl⟩

/-! ### Replacing a read by bindings -/

theorem bindReads_steps {ω : Type} (O : Exec.Oracles ω LedgerState) :
    ∀ (rs : List Var) (vals : List Expr) (xs : List Fr) (t : Exec.State ω LedgerState) (env₀ : Env),
      vals.length = rs.length → Expr.evalList p env₀ vals = some xs →
      (∀ w ∈ Expr.varsList vals, w ∉ rs) → (∀ w ∈ Expr.varsList vals, t.env w = env₀ w) →
      ∀ env', Exec.assign t.env (rs.map fun v => (v, none)) xs = some env' →
        Exec.steps p O (bindReads rs vals) t = some { t with env := env' }
  | [], [], xs, t, env₀, _, hx, _, _, env', ha => by
      simp [Expr.evalList] at hx; subst hx
      simp [Exec.assign] at ha; subst ha
      simp [bindReads, Exec.steps]
  | r :: rs, e :: vals, xs, t, env₀, hl, hx, hv, ht, env', ha => by
      simp only [Expr.evalList] at hx
      cases he : e.eval p env₀ with
      | none => simp [he] at hx
      | some x =>
        cases hes : Expr.evalList p env₀ vals with
        | none => simp [he, hes] at hx
        | some ys =>
          simp [he, hes] at hx; subst hx
          simp only [List.map_cons, Exec.assign] at ha
          have hev : e.eval p t.env = some x := by
            rw [eval_congr_of (e₂ := env₀) (fun w hw => ht w (by simp [Expr.varsList, hw]))]; exact he
          have hstep : Exec.step p O t (.bind r "ledger" e) = some { t with env := t.env.set r x } := by
            simp [Exec.step, hev]
          have ih := bindReads_steps O rs vals ys { t with env := t.env.set r x } env₀ (by simpa using hl) hes
            (fun w hw hw' => hv w (by simp [Expr.varsList, hw]) (by simp [hw']))
            (fun w hw => by
              have hwr : w ≠ r := fun h => hv w (by simp [Expr.varsList, hw]) (by simp [h])
              simp only [Env.set, hwr, ite_false]
              exact ht w (by simp [Expr.varsList, hw]))
            env' ha
          simp only [bindReads, List.zip_cons_cons, List.map_cons, Exec.steps, hstep, Option.bind_eq_bind,
            Option.bind_some]
          exact ih
  | [], _ :: _, _, _, _, hl, _, _, _, _, _ => by simp at hl
  | _ :: _, [], _, _, _, hl, _, _, _, _, _ => by simp at hl

/-! ### Selecting on the guard -/

theorem evalList_select {env : Env} {g : Expr} {gv : Fr} {b : Bool} (hg : g.eval p env = some gv)
    (hb : asBool gv = some b) : ∀ es : List Expr, (∀ e ∈ es, (e.eval p env).isSome) →
      Expr.evalList p env (es.map fun e => .select g e (.const 0)) =
        if b then Expr.evalList p env es else some (es.map fun _ => 0)
  | [], _ => by cases b <;> simp [Expr.evalList]
  | e :: es, h => by
      have ih := evalList_select hg hb es (fun x hx => h x (List.mem_cons_of_mem _ hx))
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (h e (List.mem_cons_self ..))
      simp only [List.map_cons, Expr.evalList, ih]
      cases b
      · simp [Expr.eval, hg, hx, hb, Fr.ofInt]
        rfl
      · simp [Expr.eval, hg, hx, hb]

theorem ledgerOracle_write_some {H : Hooks} {k' v' : Aligned Fr} {q q' : LedgerState} {xs : List Fr}
    (h : ledgerOracle H (writeOps k' v') q = some (xs, q')) : ∃ vv, AV.ofAligned v' = some vv := by
  cases hv : AV.ofAligned v' with
  | some vv => exact ⟨vv, rfl⟩
  | none =>
    unfold ledgerOracle at h
    cases hk : AV.ofAligned k' <;> simp [writeOps, Op.toR, hk, hv] at h

/-! ### Steps that keep the facts -/

theorem emit_case {ω : Type} (O : Exec.Oracles ω LedgerState) (st : Stmt) (rest out : List Stmt)
    (fs' : List LFact) (s t : Exec.State ω LedgerState) (hobs : s.obs = t.obs)
    (hinv : ∀ r, Exec.step p O s st = some r → LInv p fs' r.env r.ledger)
    (ih : ∀ s t : Exec.State ω LedgerState, s.obs = t.obs → LInv p fs' s.env s.ledger →
      (Exec.steps p O out t).map Exec.State.obs = (Exec.steps p O rest s).map Exec.State.obs) :
    (Exec.steps p O (st :: out) t).map Exec.State.obs = (Exec.steps p O (st :: rest) s).map Exec.State.obs := by
  have e := step_obs p O hobs st
  simp only [Exec.steps, Option.bind_eq_bind]
  cases h1 : Exec.step p O s st <;> cases h2 : Exec.step p O t st <;> rw [h1, h2] at e <;> simp at e ⊢
  rename_i r1 r2
  exact ih r1 r2 e (hinv r1 h1)

theorem inv_quiet {ω : Type} (O : Exec.Oracles ω LedgerState) {st : Stmt} {s r : Exec.State ω LedgerState}
    {fs fs' : List LFact} (hinv : LInv p fs s.env s.ledger) (h : Exec.step p O s st = some r)
    (hst : ∀ g rs ops, st ≠ .ledger g rs ops) (hfs : ∀ f ∈ fs', f ∈ fs ∧ ∀ w ∈ f.vars, w ∉ st.lrBinds) :
    LInv p fs' r.env r.ledger := by
  have hl := step_ledger_same p O h hst
  have he := step_env_frame p O h
  refine ⟨hl ▸ hinv.1, fun f hf => ?_⟩
  obtain ⟨hf1, hf2⟩ := hfs f hf
  rw [hl]
  exact (hinv.2 f hf1).env p fun w hw => he w (hf2 w hw)

end

/-! ## The scan -/

section Scan
variable (p : Prims) (H : Hooks) {ω : Type} (wit : String → List Fr → ω → Option (List Fr × ω))


/-- A plain read answered by a fact. -/
theorem go_hit {g : Expr} {rs : List Var} {ops : List (Op Expr)} {rest : List Stmt} {fs : List LFact}
    (ih : ∀ (fs : List LFact) (s t : Exec.State ω LedgerState), s.obs = t.obs → LInv p fs s.env s.ledger →
      (Exec.steps p (oracles H wit) (ledgerReuseGo fs rest) t).map Exec.State.obs =
        (Exec.steps p (oracles H wit) rest s).map Exec.State.obs)
    {n : Nat} {path : List (Aligned Expr)} {a : List Zkir.AlignAtom} (hpr : plainRead? rs ops = some (n, path, a))
    {f : LFact} (hff : findFact g n path a rs fs = some f) {s t : Exec.State ω LedgerState}
    (hobs : s.obs = t.obs) (hinv : LInv p fs s.env s.ledger) :
    (Exec.steps p (oracles H wit) (bindReads rs f.vals ++ ledgerReuseGo (forgetVars rs fs) rest) t).map
        Exec.State.obs =
      (Exec.steps p (oracles H wit) (.ledger g rs ops :: rest) s).map Exec.State.obs := by
  obtain ⟨ci, c, rfl, hn2, hci, hne, hnd, hpv⟩ := plainRead?_spec hpr
  obtain ⟨hmem, rfl, rfl, rfl, rfl, hlen, hvr⟩ := findFact_spec hff
  obtain ⟨_, gv, b, hg, hb, hpath, hon, hoff⟩ := hinv.2 f hmem
  have hte : t.env = s.env := by
    have := congrArg (fun x => x.1) hobs; exact this.symm
  -- the values read
  obtain ⟨xs, hxs, hread⟩ : ∃ xs, Expr.evalList p s.env f.vals = some xs ∧
      (b = true → ∃ path', f.path.mapM (fun k : Aligned Expr => k.mapM (Expr.eval p s.env)) = some path' ∧
        readSpec f.n path' f.align s.ledger = some xs) ∧ (b = false → xs = f.vals.map fun _ => 0) := by
    cases b
    · exact ⟨_, hoff rfl, fun h => by simp at h, fun _ => rfl⟩
    · obtain ⟨path', xs, h1, h2, h3⟩ := hon rfl
      exact ⟨xs, h3, fun _ => ⟨path', h1, h2⟩, fun h => by simp at h⟩
  have hxl : xs.length = rs.length := by rw [evalList_length hxs, hlen]
  have hzl : (rs.map fun _ => (0 : Fr)).length = rs.length := by simp
  -- the environment after the read
  obtain ⟨env', ha⟩ := assign_plain s.env rs xs hxl
  have hframe := assign_frame ha
  have hpath' : ∀ k ∈ f.path, ∀ x ∈ k.vals, (x.eval p env').isSome := by
    intro k hk x hx
    rw [eval_congr_of (e₂ := s.env) (fun w hw => hframe w (by
      simpa using hpv w (by simp only [pathVars, List.mem_flatMap]; exact ⟨k, hk, mem_varsList hx hw⟩)))]
    exact hpath k hk x hx
  obtain ⟨gs, hgs⟩ := Option.isSome_iff_exists.mp
    ((plain_groups_isSome p env' b f.n f.path ci c f.align rs).mpr hpath')
  have hrs : (rs.isEmpty && [Op.dup f.n, Op.idx ci false f.path, Op.popeq c f.align (rs.map Expr.var)].isEmpty) = false := by
    cases rs with
    | nil => exact absurd rfl hne
    | cons => rfl
  -- the original statement
  have hstep : Exec.step p (oracles H wit) s
      (.ledger f.guard rs [.dup f.n, .idx ci false f.path, .popeq c f.align (rs.map Expr.var)]) =
      some { s with env := env', pub := s.pub ++ (if b then xs else []), groups := s.groups ++ gs } := by
    cases b
    · have hx0 := (hread.2 rfl)
      subst hx0
      have hz : f.vals.map (fun _ => (0 : Fr)) = rs.map (fun _ => 0) := by
        rw [List.map_const', List.map_const', hlen]
      rw [hz] at ha
      simp only [Exec.step, hg, hrs, hb, Option.bind_eq_bind, Option.bind_some, Bool.false_eq_true, if_false]
      rw [ha]; simp only [Option.bind_some]; rw [hgs]; simp
    · obtain ⟨path', hp', hrd⟩ := hread.1 rfl
      have hor := ledgerOracle_read H f.n hn2 path' ci c hci f.align s.ledger hinv.1
      rw [hrd] at hor
      simp only [Exec.step, hg, hrs, hb, Option.bind_eq_bind, Option.bind_some, if_true, request_plain, hp',
        Option.map_some, oracles, hor, Option.map_some]
      rw [ha]; simp only [Option.bind_some]; rw [hgs]; rfl
  -- the rewritten statements
  have hbind := bindReads_steps p (oracles H wit) rs f.vals xs t s.env hlen hxs (fun w hw hr => hvr w hw hr)
    (fun w _ => by rw [hte]) env' (by rw [hte]; exact ha)
  rw [Exec.steps_append p (oracles H wit), hbind, Option.bind_some]
  simp only [Exec.steps, hstep, Option.bind_eq_bind, Option.bind_some]
  apply ih
  · simp only [Exec.State.obs, Prod.mk.injEq] at hobs ⊢
    simp [hobs]
  · refine ⟨hinv.1, fun f' hf' => ?_⟩
    obtain ⟨hf1, hf2⟩ := mem_forgetVars hf'
    exact (hinv.2 f' hf1).env p fun w hw => hframe w (by simpa using hf2 w hw)

/-- What the step of a plain read does, on a well-formed state. -/
theorem plain_step {g : Expr} {rs : List Var} {n : Nat} {path : List (Aligned Expr)} {ci c : Bool}
    {a : List Zkir.AlignAtom} {s r : Exec.State ω LedgerState} (hn : n ≤ 2) (hci : ci = false ∨ 1 ≤ n)
    (hne : rs ≠ []) (hwf : s.ledger.WF)
    (h : Exec.step p (oracles H wit) s (.ledger g rs [.dup n, .idx ci false path, .popeq c a (rs.map Expr.var)]) =
      some r) :
    r.ledger = s.ledger ∧ ∃ gv b, g.eval p s.env = some gv ∧ asBool gv = some b ∧
      (ledgerGroups p r.env b [.dup n, .idx ci false path, .popeq c a (rs.map Expr.var)]).isSome ∧
      ∃ xs, Exec.assign s.env (rs.map fun v => (v, none)) xs = some r.env ∧
        (b = true → ∃ path', path.mapM (fun k : Aligned Expr => k.mapM (Expr.eval p s.env)) = some path' ∧
          readSpec n path' a s.ledger = some xs) ∧ (b = false → xs = rs.map fun _ => 0) := by
  rcases step_ledger_cases p _ h with ⟨hsk, _⟩ | ⟨gv, hg, ⟨hb, hl, ha, hgr⟩ | ⟨hb, req, xs, hreq, hor, ha, hgr⟩⟩
  · cases rs with
    | nil => exact absurd rfl hne
    | cons => simp at hsk
  · exact ⟨hl, gv, false, hg, hb, hgr, _, ha, fun h => by simp at h, fun _ => rfl⟩
  · rw [request_plain] at hreq
    cases hp : path.mapM (fun k : Aligned Expr => k.mapM (Expr.eval p s.env)) with
    | none => simp [hp] at hreq
    | some path' =>
      simp [hp] at hreq; subst hreq
      have := ledgerOracle_read H n hn path' ci c hci a s.ledger hwf
      simp only [oracles] at hor
      rw [hor] at this
      cases hrs : readSpec n path' a s.ledger with
      | none => simp [hrs] at this
      | some ys =>
        simp [hrs] at this
        obtain ⟨rfl, hle⟩ := this
        exact ⟨hle, gv, true, hg, hb, hgr, xs, ha, fun _ => ⟨path', rfl, hrs⟩, fun h => by simp at h⟩

/-- After a plain read the pass does not answer, its facts hold. -/
theorem go_miss_inv {g : Expr} {rs : List Var} {ops : List (Op Expr)} {fs : List LFact}
    {n : Nat} {path : List (Aligned Expr)} {a : List Zkir.AlignAtom} (hpr : plainRead? rs ops = some (n, path, a))
    {s r : Exec.State ω LedgerState} (hinv : LInv p fs s.env s.ledger)
    (h : Exec.step p (oracles H wit) s (.ledger g rs ops) = some r) :
    LInv p (missFacts g rs n path a fs) r.env r.ledger := by
  obtain ⟨ci, c, rfl, hn2, hci, hne, hnd, hpv⟩ := plainRead?_spec hpr
  obtain ⟨hle, gv, b, hg, hb, hgr, xs, ha, hon, hoff⟩ := plain_step p H wit hn2 hci hne hinv.1 h
  have hframe := assign_frame ha
  have hold : ∀ f ∈ forgetVars rs fs, f.Holds p r.env r.ledger := fun f hf => by
    obtain ⟨hf1, hf2⟩ := mem_forgetVars hf
    rw [hle]; exact (hinv.2 f hf1).env p fun w hw => hframe w (by simpa using hf2 w hw)
  refine ⟨hle ▸ hinv.1, ?_⟩
  unfold missFacts
  split
  · exact hold
  · rename_i hgv
    intro f hf
    rcases mem_addFact hf with rfl | hf
    · have hgv' : ∀ w ∈ g.vars, w ∉ rs := fun w hw hr => hgv (List.any_eq_true.mpr ⟨w, hw, by simpa using hr⟩)
      have hpath := (plain_groups_isSome p r.env b n path ci c a rs).mp hgr
      have hreads : (rs.map Expr.var).mapM (Expr.eval p r.env) = some (rs.map r.env) := by
        rw [← evalList_eq_mapM]; exact evalList_vars p r.env rs
      refine ⟨hn2, gv, b, ?_, hb, hpath, ?_, ?_⟩
      · rw [eval_congr_of (e₂ := s.env) (fun w hw => hframe w (by simpa using hgv' w hw))]; exact hg
      · intro hb1
        obtain ⟨path', hp', hrs⟩ := hon hb1
        refine ⟨path', xs, ?_, by rw [hle]; exact hrs, ?_⟩
        · rw [pathMapM_congr p path (fun w hw => hframe w (by simpa using hpv w hw))]; exact hp'
        · rw [evalList_vars, assign_reads hnd ha]
      · intro hb0
        rw [evalList_vars, assign_reads hnd ha, hoff hb0, List.map_map]; rfl
    · exact hold f hf

theorem writeFact_spec {g : Expr} {k v : Aligned Expr} {f : LFact} (h : writeFact g k v = some f) :
    singleLimb v.align = true ∧ v.vals.length = v.align.length ∧
      f = { guard := g, n := 0, path := [k], align := v.align,
            vals := if g == .const 1 then v.vals else v.vals.map fun e => .select g e (.const 0) } := by
  unfold writeFact at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact ⟨hc.1.1, hc.1.2, h.symm⟩
  · simp at h

theorem mapM_eval_length {env : Env} {xs : List Expr} {ys : List Fr} (h : xs.mapM (Expr.eval p env) = some ys) :
    ys.length = xs.length := by
  rw [← evalList_eq_mapM] at h; exact evalList_length h

/-- After any other ledger statement, the facts the pass keeps hold. -/
theorem go_other_inv {g : Expr} {rs : List Var} {ops : List (Op Expr)} {fs : List LFact}
    {s r : Exec.State ω LedgerState} (hinv : LInv p fs s.env s.ledger)
    (h : Exec.step p (oracles H wit) s (.ledger g rs ops) = some r) :
    LInv p (otherFacts g rs ops fs) r.env r.ledger := by
  have hframe := step_env_frame p _ h
  -- the ledger state after: well formed, same call context
  have hq : r.ledger.WF ∧ r.ledger.context = s.ledger.context := by
    rcases step_ledger_cases p _ h with ⟨_, rfl⟩ | ⟨gv, _, ⟨_, hl, _⟩ | ⟨_, req, xs, _, hor, _⟩⟩
    · exact ⟨hinv.1, rfl⟩
    · rw [hl]; exact ⟨hinv.1, rfl⟩
    · exact ⟨ledgerOracle_wf hor, ledgerOracle_context hor⟩
  have hold : ∀ f ∈ forgetVars rs (fs.filter (·.n == 2)), f.Holds p r.env r.ledger := fun f hf => by
    obtain ⟨hf1, hf2⟩ := mem_forgetVars hf
    obtain ⟨hf1, hn⟩ := List.mem_filter.mp hf1
    have hn : f.n = 2 := by simpa using hn
    refine ((hinv.2 f hf1).env p fun w hw => hframe w (by simpa [Stmt.lrBinds] using hf2 w hw)).ledger p ?_
    rw [hn]; exact hq.2
  refine ⟨hq.1, ?_⟩
  unfold otherFacts
  cases hrs : rs with
  | cons r₀ rs₀ => simp only; exact hrs ▸ hold
  | nil =>
  cases hcw : cellWrite? ops with
  | none => simp only; exact hrs ▸ hold
  | some kv =>
  obtain ⟨k, v⟩ := kv
  cases hwf : writeFact g k v with
  | none => simp only [hwf]; exact hrs ▸ hold
  | some f =>
      simp only [hwf]
      intro f' hf'
      subst hrs
      rcases mem_addFact hf' with rfl | hf'
      · obtain ⟨hsl, hvl, rfl⟩ := writeFact_spec hwf
        have hops := cellWrite?_spec hcw
        subst hops
        rcases step_ledger_cases p _ h with ⟨hsk, _⟩ | ⟨gv, hg, ⟨hb, hl, ha, hgr⟩ | ⟨hb, req, xs, hreq, hor, ha, hgr⟩⟩
        · simp at hsk
        · simp [Exec.assign] at ha; rw [← ha] at hgr ⊢
          obtain ⟨hkv, hvv⟩ := write_groups_isSome p hgr
          have hc1 : (g == Expr.const 1) = false := by
            cases hgc : g == Expr.const 1
            · rfl
            · have := eq_of_beq hgc; subst this
              simp [Expr.eval] at hg; subst hg
              have h1 : asBool (Fr.ofInt 1) = some true := rfl
              rw [h1] at hb; simp at hb
          refine ⟨Nat.zero_le 2, gv, false, hg, hb, ?_, fun h => by simp at h, fun _ => ?_⟩
          · intro k' hk' x hx; simp at hk'; subst hk'; exact hkv x hx
          · simp only [hc1, Bool.false_eq_true, if_false]
            rw [evalList_select p hg hb v.vals hvv]; simp
        · rw [request_write] at hreq
          cases hk : k.mapM (Expr.eval p s.env) with
          | none => simp [hk] at hreq
          | some k' =>
            cases hv : v.mapM (Expr.eval p s.env) with
            | none => simp [hk, hv] at hreq
            | some v' =>
              simp [hk, hv] at hreq; subst hreq
              cases xs with
              | cons => simp [Exec.assign] at ha
              | nil =>
              simp [Exec.assign] at ha; rw [← ha]
              simp only [oracles] at hor
              obtain ⟨vv, hvv⟩ := ledgerOracle_write_some hor
              have hrd := ledgerOracle_cellWrite_read hor v.align
              obtain ⟨hva, hvm⟩ := aligned_mapM_vals _ _ _ hv
              have hvl' : v'.vals.length = v.align.length := by rw [mapM_eval_length p hvm, hvl]
              have hfo : fieldsOf v.align vv.atoms = some v'.vals := by
                apply fieldsOf_ofFields v.align v'.vals vv _ (singleLimb_spec hsl) hvl'
                rw [← hva]; exact hvv
              rw [hvv, Option.bind_some, hfo] at hrd
              have hvev : Expr.evalList p s.env v.vals = some v'.vals := by rw [evalList_eq_mapM]; exact hvm
              have hall : ∀ e ∈ v.vals, (e.eval p s.env).isSome :=
                (evalList_isSome_iff p s.env v.vals).mp (by simp [hvev])
              refine ⟨Nat.zero_le 2, gv, true, hg, hb, ?_, fun _ => ⟨[k'], v'.vals, ?_, hrd, ?_⟩, fun h => by simp at h⟩
              · intro k₀ hk₀ x hx; simp at hk₀; subst hk₀
                have := (aligned_mapM_vals _ _ _ hk).2
                rw [← evalList_eq_mapM] at this
                exact (evalList_isSome_iff p s.env _).mp (by simp [this]) x hx
              · rw [List.mapM_cons, hk]; rfl
              · split
                · exact hvev
                · rw [evalList_select p hg hb v.vals hall]; simp [hvev]
      · exact hold f' hf'

theorem go_sound : ∀ (stmts : List Stmt) (fs : List LFact) (s t : Exec.State ω LedgerState),
    s.obs = t.obs → LInv p fs s.env s.ledger →
    (Exec.steps p (oracles H wit) (ledgerReuseGo fs stmts) t).map Exec.State.obs =
      (Exec.steps p (oracles H wit) stmts s).map Exec.State.obs
  | [], fs, s, t, hobs, _ => by simp [ledgerReuseGo, Exec.steps, hobs]
  | st :: rest, fs, s, t, hobs, hinv => by
    have ih := fun fs => go_sound rest fs
    cases st with
    | bind v hint e =>
      exact emit_case p _ _ rest _ _ s t hobs
        (fun r h => inv_quiet p _ hinv h (by intros; simp) (fun f hf => by
          obtain ⟨h1, h2⟩ := mem_forgetVars hf; exact ⟨h1, by simpa [Stmt.lrBinds] using h2⟩))
        (ih _)
    | assert c msg =>
      exact emit_case p _ _ rest _ _ s t hobs
        (fun r h => inv_quiet p _ hinv h (by intros; simp) (fun f hf => ⟨hf, by simp [Stmt.lrBinds]⟩)) (ih _)
    | constrain e rr =>
      exact emit_case p _ _ rest _ _ s t hobs
        (fun r h => inv_quiet p _ hinv h (by intros; simp) (fun f hf => ⟨hf, by simp [Stmt.lrBinds]⟩)) (ih _)
    | witness g name args outs sh =>
      exact emit_case p _ _ rest _ _ s t hobs
        (fun r h => inv_quiet p _ hinv h (by intros; simp) (fun f hf => by
          obtain ⟨h1, h2⟩ := mem_forgetVars hf; exact ⟨h1, by simpa [Stmt.lrBinds] using h2⟩))
        (ih _)
    | ledger g rs ops =>
      cases hpr : plainRead? rs ops with
      | some x =>
        obtain ⟨n, path, a⟩ := x
        cases hff : findFact g n path a rs fs with
        | some f =>
          have e : ledgerReuseGo fs (.ledger g rs ops :: rest) =
              bindReads rs f.vals ++ ledgerReuseGo (forgetVars rs fs) rest := by
            simp only [ledgerReuseGo, hpr, hff]
          rw [e]
          exact go_hit p H wit (ih) hpr hff hobs hinv
        | none =>
          have e : ledgerReuseGo fs (.ledger g rs ops :: rest) =
              .ledger g rs ops :: ledgerReuseGo (missFacts g rs n path a fs) rest := by
            simp only [ledgerReuseGo, hpr, hff]
          rw [e]
          exact emit_case p _ _ rest _ _ s t hobs (fun r h => go_miss_inv p H wit hpr hinv h) (ih _)
      | none =>
        have e : ledgerReuseGo fs (.ledger g rs ops :: rest) =
            .ledger g rs ops :: ledgerReuseGo (otherFacts g rs ops fs) rest := by
          simp only [ledgerReuseGo, hpr]
        rw [e]
        exact emit_case p _ _ rest _ _ s t hobs (fun r h => go_other_inv p H wit hinv h) (ih _)
termination_by stmts => stmts.length

end Scan

/-- `Circuit.ledgerReuse` is sound against the modelled ledger. -/
theorem Circuit.ledgerReuse_soundLedger : Pass.SoundLedger Circuit.ledgerReuse := by
  refine ⟨fun {ω} H p w c inputs pr σ hσ => ?_⟩
  simp only [Exec.run, Circuit.ledgerReuse, List.toList_toArray, Option.bind_eq_bind]
  cases hb : bindInputs (fun _ => 0) c.inputs inputs with
  | none => simp
  | some env =>
    simp only [Option.bind_some]
    have e := go_sound p H w c.body.toList [] ⟨env, [], [], [], pr, σ⟩ ⟨env, [], [], [], pr, σ⟩ rfl
      ⟨hσ, by simp⟩
    cases h1 : Exec.steps p (oracles H w) (ledgerReuseGo [] c.body.toList) ⟨env, [], [], [], pr, σ⟩ <;>
      cases h2 : Exec.steps p (oracles H w) c.body.toList ⟨env, [], [], [], pr, σ⟩ <;>
      rw [h1, h2] at e <;> simp at e ⊢
    rename_i r1 r2
    simp only [Exec.State.obs, Prod.mk.injEq] at e
    obtain ⟨he, hp, hw, hl⟩ := e
    rw [he]
    cases Expr.evalList p r2.env c.outputs <;> simp [Result.ledgerObservable, hp, hw, hl]

end Damp.IR
