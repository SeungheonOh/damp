/-
`Circuit.ledgerDeadStore` (`Damp/Optimize/LedgerDeadStore.lean`) is sound
against the modelled ledger: `Circuit.ledgerDeadStore_soundLedger`.

The dropped write `W₁` and the overwriting write `W₂` are separated only by
statements that do not touch the ledger, and the executor runs those the same
whatever the ledger state is (`step_ledger_indep`). On the VM model a cell
write followed by a cell write of the same key is the second write alone, and
if the first fails the second fails on the same state
(`ledgerOracle_cellWrite_twice`); the first write's operands cannot fail
(`Expr.total`, constant keys, constant guard).
-/
import Damp.Proofs.Optimize.LedgerReuse
import Damp.Optimize.LedgerDeadStore

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Damp.IR
open Damp.Impact Damp.Exec Damp.Ledger
open Damp.Zkir (Prims Group)

theorem total_nil_eval (p : Prims) (env : Env) (e : Expr) (h : e.total [] = true) : ∃ x, e.eval p env = some x :=
  Expr.total_eval (p := p) (env := env) (bools := []) (fun v hv => by simp at hv) e h

theorem const_vals_eval (p : Prims) (env env' : Env) :
    ∀ xs : List Expr, xs.all Expr.isConst = true → xs.mapM (Expr.eval p env) = xs.mapM (Expr.eval p env')
  | [], _ => rfl
  | x :: xs, h => by
      rw [List.all_cons, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      cases x <;> simp [Expr.isConst] at h1
      simp [List.mapM_cons, Expr.eval, const_vals_eval p env env' xs h2]

section
variable {ω σ : Type} (p : Prims) (O : Exec.Oracles ω σ)

/-- A statement that is not a ledger statement runs the same on any ledger state, and keeps it. -/
theorem step_ledger_indep (s : Exec.State ω σ) (l : σ) (st : Stmt) (hst : ∀ g rs ops, st ≠ .ledger g rs ops) :
    Exec.step p O { s with ledger := l } st = (Exec.step p O s st).map fun r => { r with ledger := l } := by
  obtain ⟨env, priv, pub, groups, private_, ledger⟩ := s
  cases st with
  | bind v _ e =>
    simp only [Exec.step]
    cases e.eval p env <;> simp
  | assert c _ =>
    simp only [Exec.step]
    cases hc : c.eval p env with
    | none => simp
    | some x =>
      cases hb : asBool x with
      | none => simp [hb]
      | some b => cases b <;> simp [hb]
  | constrain e r =>
    simp only [Exec.step]
    cases he : e.eval p env with
    | none => simp
    | some x => by_cases hr : r.holds x <;> simp [hr]
  | witness g name args outs sh =>
    simp only [Exec.step]
    cases hg : g.eval p env with
    | none => simp
    | some gv =>
      simp only [Option.bind_some, Option.bind_eq_bind]
      by_cases ho : outs.isEmpty
      · simp only [ho, ite_true]
        by_cases h1 : gv = 1
        · simp only [h1, ite_true]
          cases ha : Expr.evalList p env args with
          | none => simp
          | some xs =>
            cases hw : O.witness name xs private_ with
            | none => simp [hw]
            | some res => by_cases he : res.1 = [] <;> simp [hw, he]
        · simp [h1]
      · simp only [ho]
        cases hb : asBool gv with
        | none => simp
        | some b =>
          cases b
          · simp
            cases Exec.assign env outs (outs.map fun _ => 0) <;> simp
          · simp
            cases ha : Expr.evalList p env args with
            | none => simp
            | some xs =>
              cases hw : O.witness name xs private_ with
              | none => simp [hw]
              | some res => simp [hw]; cases Exec.assign env outs res.1 <;> simp
  | ledger g rs ops => exact absurd rfl (hst g rs ops)

theorem steps_ledger_indep : ∀ (P : List Stmt) (s : Exec.State ω σ) (l : σ),
    (∀ st ∈ P, ∀ g rs ops, st ≠ .ledger g rs ops) →
    Exec.steps p O P { s with ledger := l } = (Exec.steps p O P s).map fun r => { r with ledger := l }
  | [], s, l, _ => rfl
  | st :: P, s, l, h => by
      have hst := h st (List.mem_cons_self ..)
      simp only [Exec.steps, step_ledger_indep p O s l st hst, Option.bind_eq_bind]
      cases hs : Exec.step p O s st with
      | none => rfl
      | some r =>
        simp only [Option.map_some, Option.bind_some]
        exact steps_ledger_indep P r l (fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem steps_quiet_ledger : ∀ (P : List Stmt) (s r : Exec.State ω σ),
    (∀ st ∈ P, ∀ g rs ops, st ≠ .ledger g rs ops) → Exec.steps p O P s = some r → r.ledger = s.ledger
  | [], s, r, _, h => by simp [Exec.steps] at h; subst h; rfl
  | st :: P, s, r, hq, h => by
      simp only [Exec.steps, Option.bind_eq_bind] at h
      cases hs : Exec.step p O s st with
      | none => simp [hs] at h
      | some r₁ =>
        simp only [hs, Option.bind_some] at h
        rw [steps_quiet_ledger P r₁ r (fun x hx => hq x (List.mem_cons_of_mem _ hx)) h]
        exact step_ledger_same p O hs (hq st (List.mem_cons_self ..))

end

/-! ## Recognizing the pattern -/

theorem droppableWrite?_spec {s : Stmt} {k : Aligned Expr} (h : droppableWrite? s = some k) :
    ∃ e, s = .ledger (.const 1) [] [.push false k, .push true ⟨[.field], [e]⟩, .ins false 1] ∧
      k.vals.all Expr.isConst = true ∧ e.total [] = true := by
  unfold droppableWrite? at h
  split at h
  · rename_i k' e
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h; subst h
      simp only [Bool.and_eq_true] at hc
      exact ⟨e, rfl, hc.1, hc.2⟩
    · simp at h
  · simp at h

theorem overwrites_spec {k : Aligned Expr} : ∀ {n : Nat} {rest : List Stmt}, overwrites k n rest = true →
    ∃ P v₂ R, rest = P ++ .ledger (.const 1) [] [.push false k, .push true v₂, .ins false 1] :: R ∧
      ∀ st ∈ P, ∀ g rs ops, st ≠ .ledger g rs ops
  | 0, _, h => by simp [overwrites] at h
  | _ + 1, [], h => by simp [overwrites] at h
  | n + 1, s :: rest, h => by
      have quiet : (∀ g rs ops, s ≠ .ledger g rs ops) → overwrites k n rest = true → ∃ P v₂ R,
          s :: rest = P ++ .ledger (.const 1) [] [.push false k, .push true v₂, .ins false 1] :: R ∧
            ∀ st ∈ P, ∀ g rs ops, st ≠ .ledger g rs ops := fun hs h' => by
        obtain ⟨P, v₂, R, hr, hP⟩ := overwrites_spec h'
        refine ⟨s :: P, v₂, R, by simp [hr], ?_⟩
        intro st hst
        rcases List.mem_cons.mp hst with rfl | hst
        · exact hs
        · exact hP st hst
      cases s with
      | ledger g rs ops =>
        unfold overwrites at h
        split at h
        · rename_i k' v₂ heq
          simp only [Stmt.ledger.injEq] at heq
          obtain ⟨rfl, rfl, rfl⟩ := heq
          have := alignedSame_eq h; subst this
          exact ⟨[], v₂, rest, rfl, by simp⟩
        · simp at h
        · rename_i h1 h2 _
          exfalso
          first | exact h2 g rs ops rfl | exact h1 g rs ops rfl | exact absurd rfl (h2 g rs ops) | simp_all
      | bind v hint e => exact quiet (by intros; simp) (by simpa [overwrites] using h)
      | assert c m => exact quiet (by intros; simp) (by simpa [overwrites] using h)
      | constrain e r => exact quiet (by intros; simp) (by simpa [overwrites] using h)
      | witness g name args outs sh => exact quiet (by intros; simp) (by simpa [overwrites] using h)

/-! ## The window -/

section Window
variable (p : Prims) (H : Hooks) {ω : Type} (wit : String → List Fr → ω → Option (List Fr × ω))

theorem const_aligned_eval (p : Prims) {k : Aligned Expr} (hk : k.vals.all Expr.isConst = true) :
    ∃ k', ∀ env : Env, k.mapM (Expr.eval p env) = some k' := by
  have h0 : ∀ env : Env, k.vals.mapM (Expr.eval p env) = k.vals.mapM (Expr.eval p (fun _ => 0)) :=
    fun env => const_vals_eval p env _ k.vals hk
  have hs : (k.vals.mapM (Expr.eval p (fun _ => 0))).isSome := by
    rw [← evalList_eq_mapM, evalList_isSome_iff]
    intro x hx
    have := List.all_eq_true.mp hk x hx
    cases x <;> simp [Expr.isConst] at this
    rfl
  obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp hs
  exact ⟨⟨k.align, vs⟩, fun env => by simp [Aligned.mapM, h0 env, hvs]⟩

/-- The overwriting write runs the same on the state the dropped write left
    and on the state before it. -/
theorem step_W2_eq {k : Aligned Expr} {k' : Aligned Fr} (hk : ∀ env : Env, k.mapM (Expr.eval p env) = some k')
    (v₂ : Aligned Expr) (sP : Exec.State ω LedgerState) (σ₁ : LedgerState)
    (heq : ∀ w : Aligned Fr, ledgerOracle H (writeOps k' w) σ₁ = ledgerOracle H (writeOps k' w) sP.ledger) :
    Exec.step p (oracles H wit) { sP with ledger := σ₁ }
        (.ledger (.const 1) [] [.push false k, .push true v₂, .ins false 1]) =
      Exec.step p (oracles H wit) sP (.ledger (.const 1) [] [.push false k, .push true v₂, .ins false 1]) := by
  have h1 : asBool (Fr.ofInt 1) = some true := rfl
  simp only [Exec.step, Expr.eval, Option.bind_eq_bind, Option.bind_some, h1, request_write, hk]
  simp only [List.isEmpty_nil, List.isEmpty_cons, Bool.and_false, Bool.false_eq_true, if_false, ite_false,
    if_true, ite_true]
  cases hv : v₂.mapM (Expr.eval p sP.env) with
  | none => rfl
  | some w => simp only [Option.map_some, Option.bind_some, oracles, heq w]

theorem window {k : Aligned Expr} {e : Expr} (hk : k.vals.all Expr.isConst = true) (he : e.total [] = true)
    {P R : List Stmt} {v₂ : Aligned Expr} (hP : ∀ st ∈ P, ∀ g rs ops, st ≠ .ledger g rs ops)
    (s : Exec.State ω LedgerState) :
    (Exec.steps p (oracles H wit)
        (.ledger (.const 1) [] [.push false k, .push true ⟨[.field], [e]⟩, .ins false 1] ::
          (P ++ .ledger (.const 1) [] [.push false k, .push true v₂, .ins false 1] :: R)) s).map Exec.State.obs =
      (Exec.steps p (oracles H wit)
        (P ++ .ledger (.const 1) [] [.push false k, .push true v₂, .ins false 1] :: R) s).map Exec.State.obs := by
  obtain ⟨k', hk'⟩ := const_aligned_eval p hk
  obtain ⟨x, hx⟩ := total_nil_eval p s.env e he
  have hv1 : (⟨[.field], [e]⟩ : Aligned Expr).mapM (Expr.eval p s.env) = some ⟨[.field], [x]⟩ := by
    simp [Aligned.mapM, hx]
  -- the dropped value is one field element: it fits, and it is hashable
  have hof : AV.ofAligned ⟨[.field], [x]⟩ = some ⟨[.field], [x.val]⟩ := by
    have hb : byteLen x.val ≤ 64 := by
      unfold byteLen
      split
      · omega
      · have h1 : x.val < 2 ^ 256 := Nat.lt_trans x.isLt (by decide)
        have h2 : x.val.log2 < 256 := (Nat.log2_lt (by omega)).mpr h1
        omega
    simp [AV.ofAligned, AV.ofFields, atomWidth, atomOfFields, atomFits, hb]
  have hhash : (AV.mk [.field] [x.val]).toHash.isSome := by
    have hlt : x.val < 2 ^ 256 := Nat.lt_trans x.isLt (by decide)
    simp [AV.toHash, hlt]
  have htwice := fun w => ledgerOracle_cellWrite_twice H k' ⟨[.field], [x]⟩ w _ s.ledger hof hhash
  -- the groups of the dropped write
  have hgr : (ledgerGroups p s.env true
      [.push false k, .push true ⟨[.field], [e]⟩, .ins false 1]).isSome := by
    rw [ledgerGroups_isSome_iff]
    have hkv : ∀ y ∈ k.vals, (y.eval p s.env).isSome := fun y hy => by
      have := List.all_eq_true.mp hk y hy
      cases y <;> simp [Expr.isConst] at this
      rfl
    intro op hop
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hop
    rcases hop with rfl | rfl | rfl
    · simp only [Op.encode, Aligned.encode, evalList_isSome_iff, List.mem_cons, List.mem_append, List.mem_map]
      rintro y (rfl | rfl | (rfl | ⟨_, _, rfl⟩) | hy)
      all_goals first | rfl | exact hkv y hy
    · simp only [Op.encode, Aligned.encode, evalList_isSome_iff, List.mem_cons, List.mem_append, List.mem_map]
      rintro y (rfl | rfl | (rfl | ⟨_, _, rfl⟩) | hy)
      all_goals first | rfl | (simp at hy; subst hy; simp [hx])
    · simp [Op.encode, Expr.evalList, Expr.eval]
  obtain ⟨gs, hgs⟩ := Option.isSome_iff_exists.mp hgr
  have h1 : asBool (Fr.ofInt 1) = some true := rfl
  have hstep : Exec.step p (oracles H wit) s
      (.ledger (.const 1) [] [.push false k, .push true ⟨[.field], [e]⟩, .ins false 1]) =
      (ledgerOracle H (writeOps k' ⟨[.field], [x]⟩) s.ledger).bind fun r =>
        (Exec.assign s.env [] r.1).bind fun env =>
          (ledgerGroups p env true [.push false k, .push true ⟨[.field], [e]⟩, .ins false 1]).bind fun gs =>
            some { s with env, ledger := r.2, pub := s.pub ++ r.1, groups := s.groups ++ gs } := by
    simp only [Exec.step, Expr.eval, Option.bind_eq_bind, Option.bind_some, h1, request_write, hk', hv1]
    simp [oracles]
  rw [Exec.steps_append p (oracles H wit)]
  cases ho : ledgerOracle H (writeOps k' ⟨[.field], [x]⟩) s.ledger with
  | none =>
    simp only [Exec.steps, hstep, ho, Option.bind_eq_bind, Option.bind_none, Option.map_none]
    cases hPs : Exec.steps p (oracles H wit) P s with
    | none => rfl
    | some sP =>
      have hl := steps_quiet_ledger p _ P s sP hP hPs
      have hW2 : ∀ w, ledgerOracle H (writeOps k' w) sP.ledger = none := fun w => by
        rw [hl, ← htwice w, ho]; rfl
      simp only [Option.bind_some]
      have : Exec.step p (oracles H wit) sP
          (.ledger (.const 1) [] [.push false k, .push true v₂, .ins false 1]) = none := by
        simp only [Exec.step, Expr.eval, Option.bind_eq_bind, Option.bind_some, h1, request_write, hk']
        simp only [List.isEmpty_nil, List.isEmpty_cons, Bool.and_false, Bool.false_eq_true, if_false, ite_false,
          if_true, ite_true]
        cases hv : v₂.mapM (Expr.eval p sP.env) with
        | none => rfl
        | some w => simp only [Option.map_some, Option.bind_some, oracles, hW2 w, Option.bind_none]
      simp [this]
  | some r =>
    obtain ⟨vals, σ₁⟩ := r
    have hvals : vals = [] := by
      rw [ledgerOracle_cellWrite] at ho
      simp only [Option.bind_eq_bind] at ho
      cases h1 : AV.ofAligned k' <;> simp [h1] at ho
      cases h2 : AV.ofAligned (⟨[.field], [x]⟩ : Aligned Fr) <;> simp [h2] at ho
      rename_i a b
      cases h3 : setCell s.ledger.state a b <;> simp [h3] at ho
      cases h4 : decodeEffects s.ledger.effects <;> simp [h4] at ho
      exact ho.1
    subst hvals
    have hL : Exec.steps p (oracles H wit)
        (.ledger (.const 1) [] [.push false k, .push true ⟨[.field], [e]⟩, .ins false 1] ::
          (P ++ .ledger (.const 1) [] [.push false k, .push true v₂, .ins false 1] :: R)) s =
        Exec.steps p (oracles H wit) (P ++ .ledger (.const 1) [] [.push false k, .push true v₂, .ins false 1] :: R)
          { s with ledger := σ₁, pub := s.pub ++ [], groups := s.groups ++ gs } := by
      simp only [Exec.steps, hstep, ho, Option.bind_eq_bind, Option.bind_some, Exec.assign, hgs]
    -- the state after the dropped write differs from `s` only in the ledger (and the transcript)
    have hobs : Exec.State.obs { s with ledger := σ₁, pub := s.pub ++ [], groups := s.groups ++ gs } =
        Exec.State.obs { s with ledger := σ₁ } := rfl
    rw [hL, steps_obs p _ _ hobs, Exec.steps_append p (oracles H wit), steps_ledger_indep p _ P s σ₁ hP]
    cases hPs : Exec.steps p (oracles H wit) P s with
    | none => rfl
    | some sP =>
      have hl := steps_quiet_ledger p _ P s sP hP hPs
      have heq : ∀ w, ledgerOracle H (writeOps k' w) σ₁ = ledgerOracle H (writeOps k' w) sP.ledger := fun w => by
        rw [hl, ← htwice w, ho]; rfl
      simp only [Option.map_some, Option.bind_some, Exec.steps, step_W2_eq p H wit hk' v₂ sP σ₁ heq]

theorem deadStore_go : ∀ (stmts : List Stmt) (s t : Exec.State ω LedgerState), s.obs = t.obs →
    (Exec.steps p (oracles H wit) (deadStoreGo stmts) t).map Exec.State.obs =
      (Exec.steps p (oracles H wit) stmts s).map Exec.State.obs
  | [], s, t, hobs => by simp [deadStoreGo, Exec.steps, hobs]
  | st :: rest, s, t, hobs => by
      have keep : (Exec.steps p (oracles H wit) (st :: deadStoreGo rest) t).map Exec.State.obs =
          (Exec.steps p (oracles H wit) (st :: rest) s).map Exec.State.obs := by
        have e := step_obs p (oracles H wit) hobs st
        simp only [Exec.steps, Option.bind_eq_bind]
        cases h1 : Exec.step p (oracles H wit) s st <;> cases h2 : Exec.step p (oracles H wit) t st <;>
          rw [h1, h2] at e <;> simp at e ⊢
        rename_i r1 r2
        exact deadStore_go rest r1 r2 e
      cases hd : droppableWrite? st with
      | none =>
        simp only [deadStoreGo, hd]; exact keep
      | some k =>
        by_cases ho : overwrites k deadStoreWindow rest = true
        · simp only [deadStoreGo, hd, ho, ite_true]
          obtain ⟨e, rfl, hk, he⟩ := droppableWrite?_spec hd
          obtain ⟨P, v₂, R, rfl, hP⟩ := overwrites_spec ho
          rw [deadStore_go _ s t hobs, window p H wit hk he hP s]
        · simp only [deadStoreGo, hd, ho, Bool.false_eq_true, ite_false]; exact keep

end Window

/-- `Circuit.ledgerDeadStore` is sound against the modelled ledger (for any
    ledger state, well formed or not). -/
theorem Circuit.ledgerDeadStore_soundLedger : Pass.SoundLedger Circuit.ledgerDeadStore := by
  refine ⟨fun {ω} H p w c inputs pr σ _ => ?_⟩
  simp only [Exec.run, Circuit.ledgerDeadStore, List.toList_toArray, Option.bind_eq_bind]
  cases hb : bindInputs (fun _ => 0) c.inputs inputs with
  | none => simp
  | some env =>
    simp only [Option.bind_some]
    have e := deadStore_go p H w c.body.toList ⟨env, [], [], [], pr, σ⟩ ⟨env, [], [], [], pr, σ⟩ rfl
    cases h1 : Exec.steps p (oracles H w) (deadStoreGo c.body.toList) ⟨env, [], [], [], pr, σ⟩ <;>
      cases h2 : Exec.steps p (oracles H w) c.body.toList ⟨env, [], [], [], pr, σ⟩ <;>
      rw [h1, h2] at e <;> simp at e ⊢
    rename_i r1 r2
    simp only [Exec.State.obs, Prod.mk.injEq] at e
    obtain ⟨he, hp, hw, hl⟩ := e
    rw [he]
    cases Expr.evalList p r2.env c.outputs <;> simp [Result.ledgerObservable, hp, hw, hl]

end Damp.IR
