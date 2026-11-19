/-
The optimizer keeps ledger statements well formed (`Circuit.checkLedger`).

The build checks `checkLedger` on the optimized circuit; this file proves the
check cannot be failed by optimizing a circuit that passes it:
`Circuit.optimize_checkLedger`, `Circuit.optimizeFull_checkLedger`,
`Circuit.optimizeMaxWith_checkLedger`.

The only pass that changes a ledger statement's operands non-uniformly is
`Circuit.simplify`. It rewrites them with `f'.rw`, where `f' = f.forget reads`.
Three things keep the statement well formed:

* a read variable has no entry in `f'.known`, and `simp`/`boolSimp` leave a
  variable alone, so each `popeq` result `var v` stays `var v`;
* substitution introduces only variables mentioned by entries of `f'.known`,
  that is, entries `(u, e)` with `u` not read; the pass gives up when such an
  `e` mentions a read variable (`Facts.clash`), so none does;
* `simp` and `boolSimp` never introduce a variable.
-/
import Damp.Proofs.Optimize.Pipeline
import Damp.IR.LedgerCheck

namespace Damp.IR
open Impact

namespace LedgerWF

/-! ## Variables of rewritten expressions -/

section Vars

theorem mkAdd_vars (a b : Expr) : ∀ w ∈ (mkAdd a b).vars, w ∈ a.vars ∨ w ∈ b.vars := by
  intro w hw
  unfold mkAdd at hw
  split at hw <;> simp_all [Expr.vars, canon]

theorem mkMul_vars (a b : Expr) : ∀ w ∈ (mkMul a b).vars, w ∈ a.vars ∨ w ∈ b.vars := by
  intro w hw
  unfold mkMul at hw
  split at hw <;> (try split at hw) <;> simp_all [Expr.vars, canon]

theorem mkNeg_vars (a : Expr) : ∀ w ∈ (mkNeg a).vars, w ∈ a.vars := by
  intro w hw
  unfold mkNeg at hw
  split at hw <;> simp_all [Expr.vars, canon]

theorem mkLt_vars (bits : Nat) (a b : Expr) : ∀ w ∈ (mkLt bits a b).vars, w ∈ a.vars ∨ w ∈ b.vars := by
  intro w hw
  unfold mkLt at hw
  split at hw <;> (try split at hw) <;> simp_all [Expr.vars, canon]

theorem mkEq_vars (a b : Expr) : ∀ w ∈ (mkEq a b).vars, w ∈ a.vars ∨ w ∈ b.vars := by
  intro w hw
  unfold mkEq at hw
  split at hw <;> (try split at hw) <;> simp_all [Expr.vars, canon]

theorem mkSelectDistinct_vars (c a b : Expr) :
    ∀ w ∈ (mkSelectDistinct c a b).vars, w ∈ c.vars ∨ w ∈ a.vars ∨ w ∈ b.vars := by
  intro w hw
  unfold mkSelectDistinct at hw
  split at hw
  · split at hw
    · exact Or.inr (Or.inl hw)
    · split at hw
      · exact Or.inr (Or.inr hw)
      · simp_all [Expr.vars]
  · simp only [Expr.vars, List.mem_append, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  · simp only [Expr.vars, List.mem_append] at hw
    rcases hw with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

theorem mkSelect_vars (c a b : Expr) :
    ∀ w ∈ (mkSelect c a b).vars, w ∈ c.vars ∨ w ∈ a.vars ∨ w ∈ b.vars := by
  intro w hw
  unfold mkSelect at hw
  split at hw
  · exact Or.inr (Or.inl hw)
  · exact mkSelectDistinct_vars c a b w hw

mutual
/-- Simplifying an expression introduces no variable. -/
theorem Expr.simp_vars : ∀ e : Expr, ∀ w ∈ e.simp.vars, w ∈ e.vars
  | .add a b => by
      intro w hw
      simp only [Expr.simp] at hw
      simp only [Expr.vars, List.mem_append]
      rcases mkAdd_vars _ _ w hw with h | h
      · exact Or.inl (Expr.simp_vars a w h)
      · exact Or.inr (Expr.simp_vars b w h)
  | .mul a b => by
      intro w hw
      simp only [Expr.simp] at hw
      simp only [Expr.vars, List.mem_append]
      rcases mkMul_vars _ _ w hw with h | h
      · exact Or.inl (Expr.simp_vars a w h)
      · exact Or.inr (Expr.simp_vars b w h)
  | .neg a => by
      intro w hw
      simp only [Expr.simp] at hw
      simp only [Expr.vars]
      exact Expr.simp_vars a w (mkNeg_vars _ w hw)
  | .lt bits a b => by
      intro w hw
      simp only [Expr.simp] at hw
      simp only [Expr.vars, List.mem_append]
      rcases mkLt_vars _ _ _ w hw with h | h
      · exact Or.inl (Expr.simp_vars a w h)
      · exact Or.inr (Expr.simp_vars b w h)
  | .eq a b => by
      intro w hw
      simp only [Expr.simp] at hw
      simp only [Expr.vars, List.mem_append]
      rcases mkEq_vars _ _ w hw with h | h
      · exact Or.inl (Expr.simp_vars a w h)
      · exact Or.inr (Expr.simp_vars b w h)
  | .select c a b => by
      intro w hw
      simp only [Expr.simp] at hw
      simp only [Expr.vars, List.mem_append]
      rcases mkSelect_vars _ _ _ w hw with h | h | h
      · exact Or.inl (Or.inl (Expr.simp_vars c w h))
      · exact Or.inl (Or.inr (Expr.simp_vars a w h))
      · exact Or.inr (Expr.simp_vars b w h)
  | .divmod q bits a => by
      intro w hw
      simp only [Expr.simp, Expr.vars] at hw ⊢
      exact Expr.simp_vars a w hw
  | .hash xs => by
      intro w hw
      simp only [Expr.simp, Expr.vars] at hw ⊢
      exact Expr.simpList_vars xs w hw
  | .phash high align xs => by
      intro w hw
      simp only [Expr.simp, Expr.vars] at hw ⊢
      exact Expr.simpList_vars xs w hw
  | .var v => fun w hw => hw
  | .const c => fun w hw => hw
  | .invalid m => fun w hw => hw
  | .disclose e => by
      intro w hw
      simp only [Expr.simp, Expr.vars] at hw ⊢
      exact Expr.simp_vars e w hw
theorem Expr.simpList_vars : ∀ xs : List Expr, ∀ w ∈ Expr.varsList (Expr.simpList xs), w ∈ Expr.varsList xs
  | [] => fun w hw => hw
  | x :: xs => by
      intro w hw
      simp only [Expr.simpList, Expr.varsList, List.mem_append] at hw ⊢
      rcases hw with h | h
      · exact Or.inl (Expr.simp_vars x w h)
      · exact Or.inr (Expr.simpList_vars xs w h)
end

mutual
/-- The boolean rewrites introduce no variable. -/
theorem Expr.boolSimp_vars (bools : List Var) : ∀ e : Expr, ∀ w ∈ (e.boolSimp bools).vars, w ∈ e.vars
  | .select c a b => by
      intro w hw
      have hc := Expr.boolSimp_vars bools c w
      have ha := Expr.boolSimp_vars bools a w
      have hb := Expr.boolSimp_vars bools b w
      simp only [Expr.boolSimp] at hw
      simp only [Expr.vars, List.mem_append]
      split at hw
      · exact Or.inl (Or.inr (ha hw))
      · split at hw
        · split at hw
          · exact Or.inl (Or.inl (hc hw))
          · simp only [Expr.vars, List.mem_append] at hw
            rcases hw with (h | h) | h
            · exact Or.inl (Or.inl (hc h))
            · exact Or.inl (Or.inr (ha h))
            · exact Or.inr (hb h)
        · simp only [Expr.vars, List.mem_append] at hw
          rcases hw with (h | h) | h
          · exact Or.inl (Or.inl (hc h))
          · exact Or.inl (Or.inr (ha h))
          · exact Or.inr (hb h)
  | .add a b | .mul a b | .eq a b | .lt _ a b => by
      intro w hw
      simp only [Expr.boolSimp, Expr.vars, List.mem_append] at hw ⊢
      rcases hw with h | h
      · exact Or.inl (Expr.boolSimp_vars bools a w h)
      · exact Or.inr (Expr.boolSimp_vars bools b w h)
  | .neg a | .divmod _ _ a | .disclose a => by
      intro w hw
      simp only [Expr.boolSimp, Expr.vars] at hw ⊢
      exact Expr.boolSimp_vars bools a w hw
  | .hash xs | .phash _ _ xs => by
      intro w hw
      simp only [Expr.boolSimp, Expr.vars] at hw ⊢
      exact Expr.boolSimpList_vars bools xs w hw
  | .var _ | .const _ | .invalid _ => fun w hw => hw
theorem Expr.boolSimpList_vars (bools : List Var) :
    ∀ xs : List Expr, ∀ w ∈ Expr.varsList (Expr.boolSimpList bools xs), w ∈ Expr.varsList xs
  | [] => fun w hw => hw
  | x :: xs => by
      intro w hw
      simp only [Expr.boolSimpList, Expr.varsList, List.mem_append] at hw ⊢
      rcases hw with h | h
      · exact Or.inl (Expr.boolSimp_vars bools x w h)
      · exact Or.inr (Expr.boolSimpList_vars bools xs w h)
end

mutual
/-- A variable of a substituted expression is a variable of the expression or
    of a substituted value. -/
theorem Expr.subst_vars (σ : List (Var × Expr)) :
    ∀ e : Expr, ∀ w ∈ (e.subst σ).vars, w ∈ e.vars ∨ ∃ q ∈ σ, w ∈ q.2.vars
  | .var v => by
      intro w hw
      simp only [Expr.subst] at hw
      cases hl : σ.lookup v with
      | none => rw [hl] at hw; exact Or.inl hw
      | some e => rw [hl] at hw; exact Or.inr ⟨(v, e), lookup_mem hl, hw⟩
  | .const _ | .invalid _ => fun w hw => Or.inl hw
  | .add a b | .mul a b | .eq a b | .lt _ a b => by
      intro w hw
      simp only [Expr.subst, Expr.vars, List.mem_append] at hw ⊢
      rcases hw with h | h
      · rcases Expr.subst_vars σ a w h with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rcases Expr.subst_vars σ b w h with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
  | .neg a | .divmod _ _ a | .disclose a => by
      intro w hw
      simp only [Expr.subst, Expr.vars] at hw ⊢
      exact Expr.subst_vars σ a w hw
  | .select c a b => by
      intro w hw
      simp only [Expr.subst, Expr.vars, List.mem_append] at hw ⊢
      rcases hw with (h | h) | h
      · rcases Expr.subst_vars σ c w h with h | h
        · exact Or.inl (Or.inl (Or.inl h))
        · exact Or.inr h
      · rcases Expr.subst_vars σ a w h with h | h
        · exact Or.inl (Or.inl (Or.inr h))
        · exact Or.inr h
      · rcases Expr.subst_vars σ b w h with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
  | .hash xs | .phash _ _ xs => by
      intro w hw
      simp only [Expr.subst, Expr.vars] at hw ⊢
      exact Expr.substList_vars σ xs w hw
theorem Expr.substList_vars (σ : List (Var × Expr)) :
    ∀ xs : List Expr, ∀ w ∈ Expr.varsList (Expr.substList σ xs), w ∈ Expr.varsList xs ∨ ∃ q ∈ σ, w ∈ q.2.vars
  | [] => fun w hw => Or.inl hw
  | x :: xs => by
      intro w hw
      simp only [Expr.substList, Expr.varsList, List.mem_append] at hw ⊢
      rcases hw with h | h
      · rcases Expr.subst_vars σ x w h with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rcases Expr.substList_vars σ xs w h with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
end

/-- A variable of a rewritten expression is a variable of the expression or of
    a known value. -/
theorem Facts.rw_vars (f : Facts) (e : Expr) :
    ∀ w ∈ (f.rw e).vars, w ∈ e.vars ∨ ∃ q ∈ f.known, w ∈ q.2.vars := by
  intro w hw
  exact Expr.subst_vars f.known e w (Expr.simp_vars _ w (Expr.boolSimp_vars f.bools _ w hw))

/-- The variables of a mapped list of expressions. -/
theorem varsList_map_rw (f : Facts) : ∀ xs : List Expr,
    ∀ w ∈ Expr.varsList (xs.map f.rw), w ∈ Expr.varsList xs ∨ ∃ q ∈ f.known, w ∈ q.2.vars
  | [] => fun w hw => Or.inl hw
  | x :: xs => by
      intro w hw
      simp only [List.map_cons, Expr.varsList, List.mem_append] at hw ⊢
      rcases hw with h | h
      · rcases Facts.rw_vars f x w h with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rcases varsList_map_rw f xs w h with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h

theorem varsList_append (xs ys : List Expr) :
    Expr.varsList (xs ++ ys) = Expr.varsList xs ++ Expr.varsList ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Expr.varsList, ih]

end Vars

/-! ## Instructions under a rewrite of their operands -/

theorem Op.results_map {α β : Type} (g : α → β) (op : Op α) : (op.map g).results = op.results.map g := by
  cases op <;> simp [Op.map, Op.mapM, Op.results, List.mapM_pure]

theorem Op.blank_map {α β : Type} (g : α → β) (op : Op α) : (op.map g).blank = op.blank.map g := by
  cases op <;> simp [Op.map, Op.mapM, Op.blank, List.mapM_pure]

theorem allResults_map {α β : Type} (g : α → β) (ops : List (Op α)) :
    allResults (ops.map (·.map g)) = (allResults ops).map g := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
      simp only [allResults, List.map_cons, List.flatMap_cons] at ih ⊢
      rw [ih, Op.results_map, List.map_append]

/-- The operands other than `popeq` results, rewritten. -/
theorem blankOperands_map (f : Facts) (ops : List (Op Expr)) :
    ((ops.map (·.map f.rw)).flatMap fun op => op.blank.encode Expr.const) =
      (ops.flatMap fun op => op.blank.encode Expr.const).map f.rw := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
      simp only [List.map_cons, List.flatMap_cons, List.map_append] at ih ⊢
      rw [ih, Op.blank_map, Op.encode_map f.rw (Facts.rw_const f)]

theorem varsList_flatMap (ops : List (Op Expr)) :
    (ops.flatMap fun op => Expr.varsList (op.blank.encode Expr.const)) =
      Expr.varsList (ops.flatMap fun op => op.blank.encode Expr.const) := by
  induction ops with
  | nil => rfl
  | cons op ops ih => simp only [List.flatMap_cons, varsList_append, ih]

/-- `ledgerProblem`, spelled out. -/
theorem ledgerProblem_none_iff (reads : List Var) (ops : List (Op Expr)) :
    ledgerProblem reads ops = none ↔
      allResults ops = reads.map Expr.var ∧ reads.Nodup ∧
        ∀ w ∈ Expr.varsList (ops.flatMap fun op => op.blank.encode Expr.const), w ∉ reads := by
  unfold ledgerProblem
  rw [← varsList_flatMap]
  by_cases h1 : allResults ops = reads.map Expr.var
  · by_cases h2 : reads.Nodup
    · simp only [h1, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ite_false, h2,
        decide_true, true_and]
      constructor
      · intro h w hw hr
        have : ((ops.flatMap fun op => Expr.varsList (op.blank.encode Expr.const)).find?
            reads.contains).isSome := by
          rw [List.find?_isSome]; exact ⟨w, hw, by simp [hr]⟩
        split at h
        · cases h
        · rename_i hn; rw [hn] at this; cases this
      · intro h
        split
        · rename_i v hv
          have hm := List.mem_of_find?_eq_some hv
          have hc := List.find?_some hv
          exact absurd (by simpa using hc) (h v hm)
        · rfl
    · simp [h1, h2]
  · have : (allResults ops == reads.map Expr.var) = false := by simpa using h1
    simp [this, h1]

/-! ## The statement step -/

/-- The variables of `f.forget vs`'s known values, when there is no clash. -/
theorem forget_known_vars {f : Facts} {vs : List Var} (hc : f.clash vs = false) :
    ∀ q ∈ (f.forget vs).known, ∀ w ∈ q.2.vars, w ∉ vs := by
  intro ⟨u, e⟩ hq w hw
  simp only [Facts.forget, List.mem_filter, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at hq
  exact Facts.not_clash hc u e hq.1 hq.2 w hw

/-- A read variable, forgotten, is rewritten to itself. -/
theorem forget_rw_var (f : Facts) {vs : List Var} {v : Var} (hv : v ∈ vs) :
    (f.forget vs).rw (.var v) = .var v := by
  have hl : (f.forget vs).known.lookup v = none := by
    simp only [Facts.forget]
    rw [lookup_filter]; simp [hv]
  simp only [Facts.rw, Expr.subst, hl, Option.getD_none]
  rfl

/-- The ledger statement `simplify` emits is well formed when the original is. -/
theorem ledger_rw_wellFormed (f : Facts) (reads : List Var) (ops : List (Op Expr))
    (hc : f.clash reads = false) (h : ledgerProblem reads ops = none) :
    ledgerProblem reads (ops.map (·.map (f.forget reads).rw)) = none := by
  rw [ledgerProblem_none_iff] at h ⊢
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, h2, ?_⟩
  · rw [allResults_map, h1, List.map_map]
    apply List.map_congr_left
    intro v hv
    exact forget_rw_var f hv
  · rw [blankOperands_map]
    intro w hw
    rcases varsList_map_rw _ _ w hw with h | ⟨q, hq, hw⟩
    · exact h3 w h
    · exact forget_known_vars hc q hq w hw

theorem Stmt.optimize_ledgerProblem {f f' : Facts} {s : Stmt} {out : List Stmt}
    (h : s.optimize f = some (out, f')) (hs : s.ledgerProblem = none) :
    ∀ t ∈ out, t.ledgerProblem = none := by
  intro t ht
  cases s with
  | bind v hint e =>
      simp only [Stmt.optimize] at h
      split at h
      · simp at h; obtain ⟨rfl, _⟩ := h; cases ht
      · simp at h; obtain ⟨rfl, _⟩ := h; cases ht
      · split at h
        · cases h
        · simp at h; obtain ⟨rfl, _⟩ := h
          simp at ht; subst ht; rfl
  | assert c msg =>
      simp only [Stmt.optimize] at h
      split at h
      · simp at h; obtain ⟨rfl, _⟩ := h; cases ht
      · simp at h; obtain ⟨rfl, _⟩ := h
        simp at ht; subst ht; rfl
  | constrain e r =>
      simp only [Stmt.optimize] at h
      split at h
      · simp at h; obtain ⟨rfl, _⟩ := h; cases ht
      · simp at h; obtain ⟨rfl, _⟩ := h
        simp at ht; subst ht; rfl
  | witness g name args outs shape =>
      simp only [Stmt.optimize] at h
      split at h
      · simp at h; obtain ⟨rfl, _⟩ := h; cases ht
      · split at h
        · cases h
        · simp at h; obtain ⟨rfl, _⟩ := h
          simp at ht; subst ht; rfl
  | ledger g reads ops =>
      simp only [Stmt.optimize] at h
      split at h
      · simp at h; obtain ⟨rfl, _⟩ := h; cases ht
      · split at h
        · cases h
        · rename_i hc
          split at h
          · cases h
          · simp at h; obtain ⟨rfl, _⟩ := h
            simp at ht; subst ht
            simp only [Stmt.ledgerProblem] at hs ⊢
            exact ledger_rw_wellFormed f reads ops (by simpa using hc) hs

theorem Stmt.optimizeAll_ledgerProblem : ∀ {f f' : Facts} {stmts out : List Stmt},
    Stmt.optimizeAll f stmts = some (out, f') → (∀ s ∈ stmts, s.ledgerProblem = none) →
    ∀ t ∈ out, t.ledgerProblem = none
  | f, f', [], out, h, _ => by
      simp [Stmt.optimizeAll] at h; obtain ⟨rfl, _⟩ := h; simp
  | f, f', s :: rest, out, h, hs => by
      simp only [Stmt.optimizeAll] at h
      cases h1 : s.optimize f with
      | none => simp [h1] at h
      | some r =>
          obtain ⟨a, f1⟩ := r
          cases h2 : Stmt.optimizeAll f1 rest with
          | none => simp [h1, h2, Option.bind] at h
          | some r2 =>
              obtain ⟨b, f2⟩ := r2
              simp [h1, h2, Option.bind, pure] at h
              obtain ⟨rfl, _⟩ := h
              intro t ht
              rcases List.mem_append.mp ht with ht | ht
              · exact Stmt.optimize_ledgerProblem h1 (hs s (by simp)) t ht
              · exact Stmt.optimizeAll_ledgerProblem h2 (fun s' hs' => hs s' (by simp [hs'])) t ht

/-- `checkLedger`, spelled out. -/
theorem checkLedgerFrom_ok_iff (name : String) : ∀ (i : Nat) (l : List Stmt),
    checkLedgerFrom name i l = .ok () ↔ ∀ s ∈ l, s.ledgerProblem = none
  | _, [] => by simp [checkLedgerFrom]
  | i, s :: l => by
      simp only [checkLedgerFrom, List.mem_cons, forall_eq_or_imp]
      cases s.ledgerProblem with
      | some why => simp
      | none => simp only [true_and]; exact checkLedgerFrom_ok_iff name (i + 1) l

theorem Circuit.checkLedger_ok_iff (c : Circuit) :
    c.checkLedger = .ok () ↔ ∀ s ∈ c.body.toList, s.ledgerProblem = none :=
  checkLedgerFrom_ok_iff c.name 0 _

end LedgerWF
open LedgerWF

/-! ## The passes -/

/-- `Circuit.simplify` keeps a circuit's ledger statements well formed. -/
theorem Circuit.simplify_checkLedger (c : Circuit) (h : c.checkLedger = .ok ()) :
    c.simplify.checkLedger = .ok () := by
  unfold Circuit.simplify
  split
  · rename_i body f hopt
    rw [Circuit.checkLedger_ok_iff] at h ⊢
    simpa using Stmt.optimizeAll_ledgerProblem hopt h
  · exact h

/-- A pass that keeps ledger statements well formed. -/
def Pass.KeepsLedger (f : Pass) : Prop := ∀ c : Circuit, c.checkLedger = .ok () → (f c).checkLedger = .ok ()

/-- Passes that each keep ledger statements well formed, run in order, do too. -/
theorem runPasses_keepsLedger : ∀ (ps : List Pass), (∀ f ∈ ps, Pass.KeepsLedger f) →
    Pass.KeepsLedger (runPasses ps)
  | [], _ => fun c h => by simpa [runPasses] using h
  | f :: ps, hps => fun c h => by
      have hf := hps f (by simp)
      have ih := runPasses_keepsLedger ps (fun g hg => hps g (by simp [hg]))
      simpa [runPasses, List.foldl_cons] using ih (f c) (hf c h)

/-- Choosing between the results of two passes that keep ledger statements
    well formed keeps them well formed. -/
theorem Pass.KeepsLedger.choose {f g : Pass} (hf : Pass.KeepsLedger f) (hg : Pass.KeepsLedger g)
    (better : Circuit → Circuit → Bool) : Pass.KeepsLedger (Pass.choose f g better) := fun c h => by
  simp only [Pass.choose]
  split
  · exact hf c h
  · exact hg c h

/-- `forwardOpt` keeps a circuit's ledger statements well formed. -/
theorem Circuit.forwardOpt_checkLedger : Pass.KeepsLedger Circuit.forwardOpt :=
  Pass.KeepsLedger.choose
    (fun c h => Circuit.simplify_checkLedger _
      (Circuit.algebra_checkLedger _ (Circuit.forward_checkLedger c h)))
    (fun _ h => h) _

/-- `forwardAllOpt` keeps a circuit's ledger statements well formed. -/
theorem Circuit.forwardAllOpt_checkLedger : Pass.KeepsLedger Circuit.forwardAllOpt :=
  Pass.KeepsLedger.choose
    (fun c h => Circuit.simplify_checkLedger _
      (Circuit.algebra_checkLedger _ (Circuit.forwardWith_checkLedger _ c h)))
    (fun _ h => h) _

theorem defaultPasses_keepsLedger : ∀ f ∈ defaultPasses, Pass.KeepsLedger f := by
  intro f hf
  simp only [defaultPasses, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with h | h | h | h | h | h <;> subst h
  · exact Circuit.simplify_checkLedger
  · exact Circuit.foldDivmod_checkLedger
  · exact Circuit.bounds2_checkLedger
  · exact Circuit.simplify_checkLedger
  · exact Circuit.algebra_checkLedger
  · exact Circuit.commuteOpt_checkLedger

theorem fullPasses_keepsLedger : ∀ f ∈ fullPasses, Pass.KeepsLedger f := by
  intro f hf
  simp only [fullPasses, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with h | h | h | h | h | h | h | h | h | h | h <;> subst h
  · exact Circuit.simplify_checkLedger
  · exact Circuit.foldDivmod_checkLedger
  · exact Circuit.assertEq_checkLedger
  · exact Circuit.asserts_checkLedger
  · exact Circuit.simplify_checkLedger
  · exact Circuit.bounds2_checkLedger
  · exact Circuit.simplify_checkLedger
  · exact Circuit.algebra_checkLedger
  · exact Circuit.forwardOpt_checkLedger
  · exact Circuit.forwardAllOpt_checkLedger
  · exact Circuit.commuteOpt_checkLedger

/-- The default optimizer keeps a circuit's ledger statements well formed. -/
theorem Circuit.optimize_checkLedger (c : Circuit) (h : c.checkLedger = .ok ()) :
    c.optimize.checkLedger = .ok () :=
  runPasses_keepsLedger _ defaultPasses_keepsLedger c h

/-- The full optimizer (`--O2`) keeps a circuit's ledger statements well formed. -/
theorem Circuit.optimizeFull_checkLedger (c : Circuit) (h : c.checkLedger = .ok ()) :
    c.optimizeFull.checkLedger = .ok () :=
  runPasses_keepsLedger _ fullPasses_keepsLedger c h

/-- `--O3` keeps a circuit's ledger statements well formed, whatever hash
    functions it folds with. -/
theorem Circuit.optimizeMaxWith_checkLedger (p : Zkir.Prims) (c : Circuit) (h : c.checkLedger = .ok ()) :
    (c.optimizeMaxWith p).checkLedger = .ok () := by
  refine runPasses_keepsLedger _ ?_ c h
  intro f hf
  simp only [maxPassesWith, List.mem_cons] at hf
  rcases hf with h | h | h
  · subst h; exact Circuit.simplify_checkLedger
  · subst h; exact Circuit.foldHashes_checkLedger p
  · exact fullPasses_keepsLedger f h

theorem Circuit.optimizeMax_checkLedger (c : Circuit) (h : c.checkLedger = .ok ()) :
    c.optimizeMax.checkLedger = .ok () :=
  Circuit.optimizeMaxWith_checkLedger _ c h

end Damp.IR
