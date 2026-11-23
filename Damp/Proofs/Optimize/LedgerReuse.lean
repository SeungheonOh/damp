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
leaves the ledger state as it was. A read through two `idx` is the plain read
along both paths (`ledgerOracle_read2`, `ReadOps`). A fact about the contract
state kept across another ledger statement stays true because the statement's
program leaves the part of the state at the fact's constant prefix as it was
(`frame_ledgerOracle`, `readSpec_frame`); the facts a cell write or a map
insert establish hold by `ledgerOracle_cellWrite_read` and
`ledgerOracle_mapInsert_read` (`write_holds`).

At a witness the facts survive what `WitnessesOK` allows it to do
(`inv_witness`): every witness but `createZswapOutput` keeps the ledger, and
`createZswapOutput` changes only call-context slot 1, so the facts the pass
keeps there (`keepsAcrossWitness`) are unaffected (`readSpec_ctx_frame`).
-/
import Damp.Proofs.Optimize.LedgerReuseBase
import Damp.Proofs.Ledger.Cell
import Damp.Proofs.Ledger.OptRead

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

theorem LFact.Holds.frame {f : LFact} {env : Env} {q q' : LedgerState} (h : f.Holds p env q) (hn : f.n = 0)
    (hw : svWalk q'.state (constPrefix maxFramePath f.path) = svWalk q.state (constPrefix maxFramePath f.path)) :
    f.Holds p env q' := by
  obtain ⟨hn2, gv, b, hg, hb, hpath, hon, hoff⟩ := h
  refine ⟨hn2, gv, b, hg, hb, hpath, fun hb1 => ?_, hoff⟩
  obtain ⟨path', xs, h1, h2, h3⟩ := hon hb1
  rw [hn] at h2 ⊢
  exact ⟨path', xs, h1, by rw [readSpec_frame maxFramePath h1 f.align hw]; exact h2, h3⟩

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

/-- The programs `plainRead?` recognizes. -/
def ReadOps (n : Nat) (path : List (Aligned Expr)) (a : List Zkir.AlignAtom) (rs : List Var)
    (ops : List (Op Expr)) : Prop :=
  (∃ ci c, ops = [.dup n, .idx ci false path, .popeq c a (rs.map Expr.var)] ∧ (ci = false ∨ 1 ≤ n)) ∨
  (n = 0 ∧ ∃ p₁ p₂ c, path = p₁ ++ p₂ ∧
    ops = [.dup 0, .idx false false p₁, .idx false false p₂, .popeq c a (rs.map Expr.var)])

theorem plainRead?_spec {rs : List Var} {ops : List (Op Expr)} {n : Nat} {path : List (Aligned Expr)}
    {a : List Zkir.AlignAtom} (h : plainRead? rs ops = some (n, path, a)) :
    ReadOps n path a rs ops ∧ n ≤ 2 ∧ rs ≠ [] ∧ rs.Nodup ∧ ∀ w ∈ pathVars path, w ∉ rs := by
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
      exact ⟨Or.inl ⟨ci, c, by rw [h3], by simpa using h0⟩, h1, h2, h4, fun w hw hr => h5 w hw (by simpa using hr)⟩
    · simp at h
  · rename_i p₁ p₂ c a' res
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff,
        beq_iff_eq, List.any_eq_false] at hc
      exact ⟨Or.inr ⟨rfl, p₁, p₂, c, rfl, by rw [hc.1.1.2]⟩, by omega, hc.1.1.1, hc.1.2,
        fun w hw hr => hc.2 w hw (by simpa using hr)⟩
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

theorem idx_encode_isSome (env : Env) (ci pp : Bool) (path : List (Aligned Expr)) :
    (Expr.evalList p env ((Op.idx ci pp path : Op Expr).encode Expr.const)).isSome ↔
      ∀ k ∈ path, ∀ x ∈ k.vals, (x.eval p env).isSome := by
  simp only [Op.encode, evalList_isSome_iff, List.mem_cons, List.mem_flatMap, forall_eq_or_imp]
  constructor
  · rintro ⟨_, h⟩ k hk x hx
    exact h x ⟨k, hk, by simp [Aligned.encode, hx]⟩
  · intro h
    refine ⟨rfl, ?_⟩
    rintro x ⟨k, hk, hx⟩
    exact (encode_aligned_isSome p env k).mpr (h k hk) |> fun hh =>
      (evalList_isSome_iff p env _).mp hh x hx

theorem ReadOps.groups {n : Nat} {path : List (Aligned Expr)} {a : List Zkir.AlignAtom} {rs : List Var}
    {ops : List (Op Expr)} (h : ReadOps n path a rs ops) (env : Env) (act : Bool) :
    (ledgerGroups p env act ops).isSome ↔ ∀ k ∈ path, ∀ x ∈ k.vals, (x.eval p env).isSome := by
  rcases h with ⟨ci, c, rfl, _⟩ | ⟨rfl, p₁, p₂, c, rfl, rfl⟩
  · exact plain_groups_isSome p env act n path ci c a rs
  · rw [ledgerGroups_isSome_iff]
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    have hdup : (Expr.evalList p env ((Op.dup 0 : Op Expr).encode Expr.const)).isSome := by
      simp [Op.encode, Expr.evalList, Expr.eval]
    have hpop : (Expr.evalList p env ((Op.popeq c a (rs.map Expr.var) : Op Expr).encode Expr.const)).isSome := by
      simp only [Op.encode, evalList_isSome_iff, List.mem_cons, List.mem_append, List.mem_map]
      rintro x ((rfl | rfl | ⟨_, _, rfl⟩) | ⟨v, _, rfl⟩) <;> rfl
    simp only [hdup, hpop, true_and, and_true, idx_encode_isSome, List.mem_append]
    constructor
    · rintro ⟨h1, h2⟩ k (hk | hk)
      · exact h1 k hk
      · exact h2 k hk
    · intro h; exact ⟨fun k hk => h k (Or.inl hk), fun k hk => h k (Or.inr hk)⟩

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
    (hst : ∀ g rs ops, st ≠ .ledger g rs ops)
    (hk : ∀ g n a o sh, st = .witness g n a o sh → KeepsLedger O.witness n)
    (hfs : ∀ f ∈ fs', f ∈ fs ∧ ∀ w ∈ f.vars, w ∉ st.lrBinds) :
    LInv p fs' r.env r.ledger := by
  have hl := step_ledger_same p O h hst hk
  have he := step_env_frame p O h
  refine ⟨hl ▸ hinv.1, fun f hf => ?_⟩
  obtain ⟨hf1, hf2⟩ := hfs f hf
  rw [hl]
  exact (hinv.2 f hf1).env p fun w hw => he w (hf2 w hw)

end

/-! ## The scan -/

section Scan
variable (p : Prims) (H : Hooks) {ω : Type} (wit : Damp.Exec.WitnessOracle ω LedgerState)


theorem request_plain2 (env : Env) (p₁ p₂ : List (Aligned Expr)) (c : Bool) (a : List Zkir.AlignAtom)
    (rs : List Var) :
    Exec.request p env [.dup 0, .idx false false p₁, .idx false false p₂, .popeq c a (rs.map Expr.var)] =
      (p₁.mapM (fun k : Aligned Expr => k.mapM (Expr.eval p env))).bind fun p₁' =>
        (p₂.mapM (fun k : Aligned Expr => k.mapM (Expr.eval p env))).map fun p₂' =>
          [.dup 0, .idx false false p₁', .idx false false p₂', .popeq c a []] := by
  have hr : (rs.map Expr.var).mapM (Expr.eval p env) = some (rs.map env) := by
    rw [← evalList_eq_mapM]; exact evalList_vars p env rs
  cases hp1 : p₁.mapM (fun k : Aligned Expr => k.mapM (Expr.eval p env)) <;>
    cases hp2 : p₂.mapM (fun k : Aligned Expr => k.mapM (Expr.eval p env)) <;>
    simp [Exec.request, Op.mapM, hp1, hp2, hr, Exec.blank]

/-- What the request of a read program does, on a well-formed state. -/
theorem ReadOps.read {n : Nat} {path : List (Aligned Expr)} {a : List Zkir.AlignAtom} {rs : List Var}
    {ops : List (Op Expr)} (h : ReadOps n path a rs ops) (hn : n ≤ 2) (env : Env) (q : LedgerState) (hwf : q.WF) :
    (Exec.request p env ops).map (fun req => ledgerOracle H req q) =
      (path.mapM (fun k : Aligned Expr => k.mapM (Expr.eval p env))).map fun path' =>
        (readSpec n path' a q).map fun ys => (ys, q) := by
  rcases h with ⟨ci, c, rfl, hci⟩ | ⟨rfl, p₁, p₂, c, rfl, rfl⟩
  · rw [request_plain]
    cases hp : path.mapM (fun k : Aligned Expr => k.mapM (Expr.eval p env)) with
    | none => rfl
    | some path' => simp [ledgerOracle_read H n hn path' ci c hci a q hwf]
  · rw [request_plain2, List.mapM_append]
    cases hp1 : p₁.mapM (fun k : Aligned Expr => k.mapM (Expr.eval p env)) with
    | none => rfl
    | some p₁' =>
      cases hp2 : p₂.mapM (fun k : Aligned Expr => k.mapM (Expr.eval p env)) with
      | none => rfl
      | some p₂' => simp [ledgerOracle_read2 H p₁' p₂' c a q hwf]

theorem ReadOps.read_some {n : Nat} {path : List (Aligned Expr)} {a : List Zkir.AlignAtom} {rs : List Var}
    {ops : List (Op Expr)} (h : ReadOps n path a rs ops) (hn : n ≤ 2) {env : Env} {q : LedgerState} (hwf : q.WF)
    {path' : List (Aligned Fr)} (hp : path.mapM (fun k : Aligned Expr => k.mapM (Expr.eval p env)) = some path') :
    ∃ req, Exec.request p env ops = some req ∧ ledgerOracle H req q = (readSpec n path' a q).map fun ys => (ys, q) := by
  have e := h.read p H hn env q hwf
  rw [hp] at e
  cases hr : Exec.request p env ops with
  | none => rw [hr] at e; simp at e
  | some req => rw [hr] at e; simp at e; exact ⟨req, rfl, e⟩

theorem ReadOps.read_of_req {n : Nat} {path : List (Aligned Expr)} {a : List Zkir.AlignAtom} {rs : List Var}
    {ops : List (Op Expr)} (h : ReadOps n path a rs ops) (hn : n ≤ 2) {env : Env} {q : LedgerState} (hwf : q.WF)
    {req : List (Op Fr)} (hr : Exec.request p env ops = some req) :
    ∃ path', path.mapM (fun k : Aligned Expr => k.mapM (Expr.eval p env)) = some path' ∧
      ledgerOracle H req q = (readSpec n path' a q).map fun ys => (ys, q) := by
  have e := h.read p H hn env q hwf
  rw [hr] at e
  cases hp : path.mapM (fun k : Aligned Expr => k.mapM (Expr.eval p env)) with
  | none => rw [hp] at e; simp at e
  | some path' => rw [hp] at e; simp at e; exact ⟨path', rfl, e⟩

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
  obtain ⟨hro, hn2, hne, hnd, hpv⟩ := plainRead?_spec hpr
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
  -- the environment after the read
  obtain ⟨env', ha⟩ := assign_plain s.env rs xs hxl
  have hframe := assign_frame ha
  have hpath' : ∀ k ∈ f.path, ∀ x ∈ k.vals, (x.eval p env').isSome := by
    intro k hk x hx
    rw [eval_congr_of (e₂ := s.env) (fun w hw => hframe w (by
      simpa using hpv w (by simp only [pathVars, List.mem_flatMap]; exact ⟨k, hk, mem_varsList hx hw⟩)))]
    exact hpath k hk x hx
  obtain ⟨gs, hgs⟩ := Option.isSome_iff_exists.mp ((hro.groups p env' b).mpr hpath')
  have hrs : (rs.isEmpty && ops.isEmpty) = false := by
    cases rs with
    | nil => exact absurd rfl hne
    | cons => rfl
  -- the original statement
  have hstep : Exec.step p (oracles H wit) s (.ledger f.guard rs ops) =
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
      obtain ⟨req, hreq, hor⟩ := hro.read_some p H hn2 hinv.1 hp'
      rw [hrd] at hor
      simp only [Exec.step, hg, hrs, hb, Option.bind_eq_bind, Option.bind_some, if_true, hreq,
        oracles, hor, Option.map_some]
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
theorem plain_step {g : Expr} {rs : List Var} {n : Nat} {path : List (Aligned Expr)} {ops : List (Op Expr)}
    {a : List Zkir.AlignAtom} {s r : Exec.State ω LedgerState} (hro : ReadOps n path a rs ops) (hn : n ≤ 2)
    (hne : rs ≠ []) (hwf : s.ledger.WF)
    (h : Exec.step p (oracles H wit) s (.ledger g rs ops) = some r) :
    r.ledger = s.ledger ∧ ∃ gv b, g.eval p s.env = some gv ∧ asBool gv = some b ∧
      (ledgerGroups p r.env b ops).isSome ∧
      ∃ xs, Exec.assign s.env (rs.map fun v => (v, none)) xs = some r.env ∧
        (b = true → ∃ path', path.mapM (fun k : Aligned Expr => k.mapM (Expr.eval p s.env)) = some path' ∧
          readSpec n path' a s.ledger = some xs) ∧ (b = false → xs = rs.map fun _ => 0) := by
  rcases step_ledger_cases p _ h with ⟨hsk, _⟩ | ⟨gv, hg, ⟨hb, hl, ha, hgr⟩ | ⟨hb, req, xs, hreq, hor, ha, hgr⟩⟩
  · cases rs with
    | nil => exact absurd rfl hne
    | cons => simp at hsk
  · exact ⟨hl, gv, false, hg, hb, hgr, _, ha, fun h => by simp at h, fun _ => rfl⟩
  · obtain ⟨path', hp, this⟩ := hro.read_of_req p H hn hwf hreq
    simp only [oracles] at hor
    rw [hor] at this
    cases hrs : readSpec n path' a s.ledger with
    | none => simp [hrs] at this
    | some ys =>
      simp [hrs] at this
      obtain ⟨rfl, hle⟩ := this
      exact ⟨hle, gv, true, hg, hb, hgr, xs, ha, fun _ => ⟨path', hp, hrs⟩, fun h => by simp at h⟩

/-- After a plain read the pass does not answer, its facts hold. -/
theorem go_miss_inv {g : Expr} {rs : List Var} {ops : List (Op Expr)} {fs : List LFact}
    {n : Nat} {path : List (Aligned Expr)} {a : List Zkir.AlignAtom} (hpr : plainRead? rs ops = some (n, path, a))
    {s r : Exec.State ω LedgerState} (hinv : LInv p fs s.env s.ledger)
    (h : Exec.step p (oracles H wit) s (.ledger g rs ops) = some r) :
    LInv p (missFacts g rs n path a fs) r.env r.ledger := by
  obtain ⟨hro, hn2, hne, hnd, hpv⟩ := plainRead?_spec hpr
  obtain ⟨hle, gv, b, hg, hb, hgr, xs, ha, hon, hoff⟩ := plain_step p H wit hro hn2 hne hinv.1 h
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
      have hpath := (hro.groups p r.env b).mp hgr
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

theorem writeFact_spec {g : Expr} {path : List (Aligned Expr)} {v : Aligned Expr} {f : LFact}
    (h : writeFact g path v = some f) :
    singleLimb v.align = true ∧ v.vals.length = v.align.length ∧
      f = { guard := g, n := 0, path, align := v.align,
            vals := if g == .const 1 then v.vals else v.vals.map fun e => .select g e (.const 0) } := by
  unfold writeFact at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact ⟨hc.1.1, hc.1.2, h.symm⟩
  · simp at h

theorem mapInsert?_spec {ops : List (Op Expr)} {k₁ k₂ v : Aligned Expr} (h : mapInsert? ops = some (k₁, k₂, v)) :
    ops = [.idx false true [k₁], .push false k₂, .push true v, .ins false 1, .ins true 1] := by
  unfold mapInsert? at h
  split at h
  · simp at h; obtain ⟨rfl, rfl, rfl⟩ := h; rfl
  · simp at h

theorem mapIns_groups_isSome {env : Env} {act : Bool} {k₁ k₂ v : Aligned Expr}
    (h : (ledgerGroups p env act [.idx false true [k₁], .push false k₂, .push true v, .ins false 1, .ins true 1]).isSome) :
    (∀ k ∈ [k₁, k₂], ∀ x ∈ k.vals, (x.eval p env).isSome) ∧ (∀ x ∈ v.vals, (x.eval p env).isSome) := by
  rw [ledgerGroups_isSome_iff] at h
  have hi := (idx_encode_isSome p env false true [k₁]).mp (h _ (List.mem_cons_self ..))
  have hk := h (.push false k₂) (by simp)
  have hv := h (.push true v) (by simp)
  simp only [Op.encode, evalList_isSome_iff, List.mem_cons] at hk hv
  refine ⟨fun k hk' x hx => ?_, fun x hx => hv x (Or.inr (Or.inr ?_))⟩
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk'
    rcases hk' with rfl | rfl
    · exact hi _ (by simp) x hx
    · exact hk x (Or.inr (Or.inr (by simp [Aligned.encode, hx])))
  · simp [Aligned.encode, hx]

theorem request_mapIns (env : Env) (k₁ k₂ v : Aligned Expr) :
    Exec.request p env [.idx false true [k₁], .push false k₂, .push true v, .ins false 1, .ins true 1] =
      (k₁.mapM (Expr.eval p env)).bind fun k₁' => (k₂.mapM (Expr.eval p env)).bind fun k₂' =>
        (v.mapM (Expr.eval p env)).map fun v' => mapInsOps k₁' k₂' v' := by
  cases h1 : k₁.mapM (Expr.eval p env) <;> cases h2 : k₂.mapM (Expr.eval p env) <;>
    cases h3 : v.mapM (Expr.eval p env) <;> simp [Exec.request, Op.mapM, h1, h2, h3, Exec.blank, mapInsOps]

theorem ledgerOracle_mapIns_some {H : Hooks} {k₁ k₂ v : Aligned Fr} {q q' : LedgerState} {xs : List Fr}
    (h : ledgerOracle H (mapInsOps k₁ k₂ v) q = some (xs, q')) : ∃ vv, AV.ofAligned v = some vv := by
  cases hv : AV.ofAligned v with
  | some vv => exact ⟨vv, rfl⟩
  | none =>
    unfold ledgerOracle at h
    cases h1 : AV.ofAligned k₁ <;> cases h2 : AV.ofAligned k₂ <;> simp [mapInsOps, Op.toR, h1, h2, hv] at h

theorem mapM_eval_length {env : Env} {xs : List Expr} {ys : List Fr} (h : xs.mapM (Expr.eval p env) = some ys) :
    ys.length = xs.length := by
  rw [← evalList_eq_mapM] at h; exact evalList_length h

/-- A write of `v` at `path` establishes the fact `writeFact g path v`, given
    that its public inputs need the operands evaluated and that each successful
    request of it leaves a state where the read along the evaluated path
    answers `v`'s field elements. -/
theorem write_holds {g : Expr} {ops : List (Op Expr)} {path : List (Aligned Expr)} {v : Aligned Expr} {f : LFact}
    (hwf : writeFact g path v = some f) (hops : ops ≠ [])
    (hgr : ∀ env act, (ledgerGroups p env act ops).isSome →
      (∀ k ∈ path, ∀ x ∈ k.vals, (x.eval p env).isSome) ∧ ∀ x ∈ v.vals, (x.eval p env).isSome)
    (hrd : ∀ env req q q' xs, Exec.request p env ops = some req → ledgerOracle H req q = some (xs, q') →
      ∃ path' v' vv, path.mapM (fun k : Aligned Expr => k.mapM (Expr.eval p env)) = some path' ∧
        v.mapM (Expr.eval p env) = some v' ∧ AV.ofAligned v' = some vv ∧
        readSpec 0 path' v.align q' = fieldsOf v.align vv.atoms)
    {s r : Exec.State ω LedgerState} (h : Exec.step p (oracles H wit) s (.ledger g [] ops) = some r) :
    f.Holds p r.env r.ledger := by
  obtain ⟨hsl, hvl, rfl⟩ := writeFact_spec hwf
  rcases step_ledger_cases p _ h with ⟨hsk, _⟩ | ⟨gv, hg, ⟨hb, hl, ha, hgr'⟩ | ⟨hb, req, xs, hreq, hor, ha, hgr'⟩⟩
  · cases ops with
    | nil => exact absurd rfl hops
    | cons => simp at hsk
  · simp [Exec.assign] at ha; rw [← ha] at hgr' ⊢
    obtain ⟨hkv, hvv⟩ := hgr s.env false hgr'
    have hc1 : (g == Expr.const 1) = false := by
      cases hgc : g == Expr.const 1
      · rfl
      · have := eq_of_beq hgc; subst this
        simp [Expr.eval] at hg; subst hg
        have h1 : asBool (Fr.ofInt 1) = some true := rfl
        rw [h1] at hb; simp at hb
    refine ⟨Nat.zero_le 2, gv, false, hg, hb, hkv, fun h => by simp at h, fun _ => ?_⟩
    simp only [hc1, Bool.false_eq_true, if_false]
    rw [evalList_select p hg hb v.vals hvv]; simp
  · cases xs with
    | cons => simp [Exec.assign] at ha
    | nil =>
    simp [Exec.assign] at ha; rw [← ha]
    simp only [oracles] at hor
    obtain ⟨path', v', vv, hp', hv, hvv, hrd'⟩ := hrd s.env req _ _ _ hreq hor
    obtain ⟨hva, hvm⟩ := aligned_mapM_vals _ _ _ hv
    have hvl' : v'.vals.length = v.align.length := by rw [mapM_eval_length p hvm, hvl]
    have hfo : fieldsOf v.align vv.atoms = some v'.vals := by
      apply fieldsOf_ofFields v.align v'.vals vv _ (singleLimb_spec hsl) hvl'
      rw [← hva]; exact hvv
    rw [hfo] at hrd'
    have hvev : Expr.evalList p s.env v.vals = some v'.vals := by rw [evalList_eq_mapM]; exact hvm
    have hall : ∀ e ∈ v.vals, (e.eval p s.env).isSome :=
      (evalList_isSome_iff p s.env v.vals).mp (by simp [hvev])
    refine ⟨Nat.zero_le 2, gv, true, hg, hb, pathMapM_isSome p hp', fun _ => ⟨path', v'.vals, hp', hrd', ?_⟩,
      fun h => by simp at h⟩
    split
    · exact hvev
    · rw [evalList_select p hg hb v.vals hall]; simp [hvev]

/-- After any other ledger statement, the facts the pass keeps hold. -/
theorem go_other_inv {g : Expr} {rs : List Var} {ops : List (Op Expr)} {fs : List LFact}
    {s r : Exec.State ω LedgerState} (hinv : LInv p fs s.env s.ledger)
    (h : Exec.step p (oracles H wit) s (.ledger g rs ops) = some r) :
    LInv p (otherFacts g rs ops fs) r.env r.ledger := by
  have hframe := step_env_frame p _ h
  -- the ledger state after: well formed, same call context, and every part `frameKeeps` protects
  have hq : r.ledger.WF ∧ r.ledger.context = s.ledger.context ∧
      ∀ π, frameKeeps π ops = true → svWalk r.ledger.state π = svWalk s.ledger.state π := by
    rcases step_ledger_cases p _ h with ⟨_, rfl⟩ | ⟨gv, _, ⟨_, hl, _⟩ | ⟨_, req, xs, hreq, hor, _⟩⟩
    · exact ⟨hinv.1, rfl, fun _ _ => rfl⟩
    · rw [hl]; exact ⟨hinv.1, rfl, fun _ _ => rfl⟩
    · exact ⟨ledgerOracle_wf hor, ledgerOracle_context hor, fun π hk => frame_ledgerOracle H hk hreq hor⟩
  have hold : ∀ f ∈ forgetVars rs (fs.filter (keepsFact ops)), f.Holds p r.env r.ledger := fun f hf => by
    obtain ⟨hf1, hf2⟩ := mem_forgetVars hf
    obtain ⟨hf1, hk⟩ := List.mem_filter.mp hf1
    have hfe := (hinv.2 f hf1).env p fun w hw => hframe w (by simpa [Stmt.lrBinds] using hf2 w hw)
    simp only [keepsFact, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at hk
    rcases hk with hn | ⟨hn, hk⟩
    · exact hfe.ledger p (by rw [hn]; exact hq.2.1)
    · exact hfe.frame p hn (hq.2.2 _ hk)
  refine ⟨hq.1, ?_⟩
  unfold otherFacts
  cases hrs : rs with
  | cons r₀ rs₀ => simp only; exact hrs ▸ hold
  | nil =>
  subst hrs
  cases hcw : cellWrite? ops with
  | some kv =>
    obtain ⟨k, v⟩ := kv
    have hops := cellWrite?_spec hcw
    cases hwf : writeFact g [k] v with
    | none => simp only [hwf]; exact hold
    | some f =>
      simp only [hwf]
      intro f' hf'
      rcases mem_addFact hf' with rfl | hf'
      · subst hops
        refine write_holds p H wit hwf (by simp) (fun env act hg => ?_) (fun env req q q' xs hreq hor => ?_) h
        · obtain ⟨h1, h2⟩ := write_groups_isSome p hg
          exact ⟨fun k' hk' x hx => by simp at hk'; subst hk'; exact h1 x hx, h2⟩
        · rw [request_write] at hreq
          cases hk : k.mapM (Expr.eval p env) with
          | none => simp [hk] at hreq
          | some k' =>
            cases hv : v.mapM (Expr.eval p env) with
            | none => simp [hk, hv] at hreq
            | some v' =>
              simp [hk, hv] at hreq; subst hreq
              obtain ⟨vv, hvv⟩ := ledgerOracle_write_some hor
              have hrd := ledgerOracle_cellWrite_read hor v.align
              rw [hvv, Option.bind_some] at hrd
              exact ⟨[k'], v', vv, by rw [List.mapM_cons, hk]; rfl, rfl, hvv, hrd⟩
      · exact hold f' hf'
  | none =>
  cases hmi : mapInsert? ops with
  | none => simp only; exact hold
  | some kkv =>
    obtain ⟨k₁, k₂, v⟩ := kkv
    have hops := mapInsert?_spec hmi
    cases hwf : writeFact g [k₁, k₂] v with
    | none => simp only [hwf]; exact hold
    | some f =>
      simp only [hwf]
      intro f' hf'
      rcases mem_addFact hf' with rfl | hf'
      · subst hops
        refine write_holds p H wit hwf (by simp) (fun env act hg => mapIns_groups_isSome p hg)
          (fun env req q q' xs hreq hor => ?_) h
        rw [request_mapIns] at hreq
        cases h1 : k₁.mapM (Expr.eval p env) with
        | none => simp [h1] at hreq
        | some k₁' =>
          cases h2 : k₂.mapM (Expr.eval p env) with
          | none => simp [h1, h2] at hreq
          | some k₂' =>
            cases hv : v.mapM (Expr.eval p env) with
            | none => simp [h1, h2, hv] at hreq
            | some v' =>
              simp [h1, h2, hv] at hreq; subst hreq
              obtain ⟨vv, hvv⟩ := ledgerOracle_mapIns_some hor
              have hrd := ledgerOracle_mapInsert_read hor v.align
              rw [hvv, Option.bind_some] at hrd
              exact ⟨[k₁', k₂'], v', vv, by simp [List.mapM_cons, h1, h2], rfl, hvv, hrd⟩
      · exact hold f' hf'

/-- **The facts survive a witness**: every witness but `createZswapOutput`
    keeps the ledger (`WitnessesOK.keepsLedger`); `createZswapOutput` changes
    only call-context slot 1, and the facts kept across it
    (`keepsAcrossWitness`) are about the contract state, the effects, or a
    constant context slot other than 1 (`readSpec_ctx_frame`). Without the
    filter at `ctxWitness`, a fact about slot 1 would have to survive a change
    of slot 1: `readSpec 2 path' a q' = readSpec 2 path' a q` with `q'.context`
    differing from `q.context` at slot 1 is not provable (and false of the
    runtime: `com_indices` gains the commitment). -/
theorem inv_witness (hW : WitnessesOK wit) {g : Expr} {name : String} {args : List Expr}
    {outs : List (Var × Option Range)} {sh : Shape} {s r : Exec.State ω LedgerState} {fs : List LFact}
    (hinv : LInv p fs s.env s.ledger) (h : Exec.step p (oracles H wit) s (.witness g name args outs sh) = some r) :
    LInv p (forgetVars (outs.map Prod.fst) (if ctxWitness name then fs.filter keepsAcrossWitness else fs))
      r.env r.ledger := by
  have he := step_env_frame p _ h
  have henv : ∀ f ∈ forgetVars (outs.map Prod.fst) (if ctxWitness name then fs.filter keepsAcrossWitness else fs),
      ∀ w ∈ f.vars, r.env w = s.env w := fun f hf w hw => he w (by
        have := (mem_forgetVars hf).2 w hw; simpa [Stmt.lrBinds] using this)
  have hmem : ∀ f ∈ forgetVars (outs.map Prod.fst) (if ctxWitness name then fs.filter keepsAcrossWitness else fs),
      f ∈ fs ∧ (ctxWitness name = true → keepsAcrossWitness f = true) := fun f hf => by
    have h1 := (mem_forgetVars hf).1
    by_cases hc : ctxWitness name = true
    · rw [if_pos hc] at h1; exact ⟨(List.mem_filter.mp h1).1, fun _ => (List.mem_filter.mp h1).2⟩
    · rw [if_neg hc] at h1; exact ⟨h1, fun h' => absurd h' hc⟩
  by_cases hz : witnessClass name = .zswapOutput
  · have hc : ctxWitness name = true := by simp [ctxWitness, hz]
    have hstep := step_witness_ctx p (hW.zswapOutput hz) h
    refine ⟨hstep.wf hinv.1, fun f hf => ?_⟩
    obtain ⟨hf1, hf2⟩ := hmem f hf
    have hold := (hinv.2 f hf1).env p fun w hw => henv f hf w hw
    have hkeep := hf2 hc
    unfold keepsAcrossWitness at hkeep
    by_cases hn : f.n = 2
    · simp only [hn, bne_self_eq_false, Bool.false_or] at hkeep
      split at hkeep
      · rename_i kv hkv
        have hk1 : kv.atoms ≠ [1] := by simpa using hkeep
        obtain ⟨hn2, gv, b, hg, hb, hpath, hon, hoff⟩ := hold
        refine ⟨hn2, gv, b, hg, hb, hpath, fun hb1 => ?_, hoff⟩
        obtain ⟨path', xs, h1, h2, h3⟩ := hon hb1
        refine ⟨path', xs, h1, ?_, h3⟩
        rw [hn] at h2 ⊢
        rw [readSpec_ctx_frame h1 f.align hkv hk1 hstep.2.2]; exact h2
      · simp at hkeep
    · apply hold.ledger
      have hle := hold.1
      have : f.n = 0 ∨ f.n = 1 := by omega
      rcases this with h0 | h0 <;> rw [h0] <;> simp [LedgerState.comp, hstep.1, hstep.2.1]
  · have hk := hW.keepsLedger hz
    have hl := step_witness_keeps p _ hk h
    refine ⟨hl ▸ hinv.1, fun f hf => ?_⟩
    rw [hl]
    exact (hinv.2 f (hmem f hf).1).env p fun w hw => henv f hf w hw

theorem go_sound (hW : WitnessesOK wit) : ∀ (stmts : List Stmt) (fs : List LFact) (s t : Exec.State ω LedgerState),
    s.obs = t.obs → LInv p fs s.env s.ledger →
    (Exec.steps p (oracles H wit) (ledgerReuseGo fs stmts) t).map Exec.State.obs =
      (Exec.steps p (oracles H wit) stmts s).map Exec.State.obs
  | [], fs, s, t, hobs, _ => by simp [ledgerReuseGo, Exec.steps, hobs]
  | st :: rest, fs, s, t, hobs, hinv => by
    have ih := fun fs => go_sound hW rest fs
    cases st with
    | bind v hint e =>
      exact emit_case p _ _ rest _ _ s t hobs
        (fun r h => inv_quiet p _ hinv h (by intros; simp) (by intros; simp_all) (fun f hf => by
          obtain ⟨h1, h2⟩ := mem_forgetVars hf; exact ⟨h1, by simpa [Stmt.lrBinds] using h2⟩))
        (ih _)
    | assert c msg =>
      exact emit_case p _ _ rest _ _ s t hobs
        (fun r h => inv_quiet p _ hinv h (by intros; simp) (by intros; simp_all) (fun f hf => ⟨hf, by simp [Stmt.lrBinds]⟩)) (ih _)
    | constrain e rr =>
      exact emit_case p _ _ rest _ _ s t hobs
        (fun r h => inv_quiet p _ hinv h (by intros; simp) (by intros; simp_all) (fun f hf => ⟨hf, by simp [Stmt.lrBinds]⟩)) (ih _)
    | witness g name args outs sh =>
      exact emit_case p _ _ rest _ _ s t hobs (fun r h => inv_witness p H wit hW hinv h) (ih _)
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
  refine ⟨fun {ω} H p w hW c inputs pr σ hσ => ?_⟩
  simp only [Exec.run, Circuit.ledgerReuse, List.toList_toArray, Option.bind_eq_bind]
  cases hb : bindInputs (fun _ => 0) c.inputs inputs with
  | none => simp
  | some env =>
    simp only [Option.bind_some]
    have e := go_sound p H w hW c.body.toList [] ⟨env, [], [], [], pr, σ⟩ ⟨env, [], [], [], pr, σ⟩ rfl
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
