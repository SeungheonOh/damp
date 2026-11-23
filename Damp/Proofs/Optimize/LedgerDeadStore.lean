/-
`Circuit.ledgerDeadStore` (`Damp/Optimize/LedgerDeadStore.lean`) is sound
against the modelled ledger: `Circuit.ledgerDeadStore_soundLedger`.

The dropped write `W₁` and the overwriting write `W₂` are separated only by
statements that are not ledger statements and not a user's witness. Under
`WitnessesOK` every witness among them sees and changes only the call context
(`CtxOnly`: isolated witnesses, and `createZswapOutput`), which `W₁` does not
touch, so the executor runs them the same from the state `W₁` leaves and from
the state before it, up to the contract state and effects, which they keep
(`steps_ctxmap`, `steps_quiet_frame`). A user's witness may read the contract
state, so it would see the value `W₁` writes: the pass stops there
(`stateWitness`). Without that barrier `steps_ctxmap` fails at the witness: its
hypothesis `CtxOnly wit name` is exactly what `ReadsLedger` (which lets the
answer depend on `l.state`) does not give (see `Examples/WitnessBarrier.lean`). On the VM model a cell
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

/-- A statement that is neither a ledger statement nor a witness runs the same on any ledger state, and keeps it. -/
theorem step_ledger_indep (s : Exec.State ω σ) (l : σ) (st : Stmt) (hst : ∀ g rs ops, st ≠ .ledger g rs ops)
    (hw : ∀ g n a o sh, st ≠ .witness g n a o sh) :
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
  | witness g name args outs sh => exact absurd rfl (hw g name args outs sh)
  | ledger g rs ops => exact absurd rfl (hst g rs ops)

end

/-- The statements a dead store looks past: no ledger statement, no user's witness. -/
def DSQuiet (st : Stmt) : Prop :=
  (∀ g rs ops, st ≠ .ledger g rs ops) ∧ ∀ g n a o sh, st = .witness g n a o sh → witnessClass n ≠ .user

section
variable {ω : Type} (p : Prims) (H : Hooks) (wit : WitnessOracle ω LedgerState)

/-- **Such a statement run on a ledger state with the same call context** is
    the statement run on the original, the ledger state then being the given
    one with the call context the original run leaves. -/
theorem step_ctxmap (hW : WitnessesOK wit) (st : Stmt) (hst : DSQuiet st) (s : Exec.State ω LedgerState)
    (l : LedgerState) (hl : l.context = s.ledger.context) :
    Exec.step p (oracles H wit) { s with ledger := l } st =
      (Exec.step p (oracles H wit) s st).map fun r => { r with ledger := { l with context := r.ledger.context } } := by
  have hll : ({ l with context := s.ledger.context } : LedgerState) = l := by rw [← hl]
  cases st with
  | witness g name args outs sh =>
    have hc := hW.ctxOnly (hst.2 g name args outs sh rfl)
    exact step_witness_map p (oracles H wit) (fun l' => { l with context := l'.context }) s l hll
      (fun a x => hc.map s.ledger l hl a x) g args outs sh
  | ledger g rs ops => exact absurd rfl (hst.1 g rs ops)
  | _ =>
    rw [step_ledger_indep p _ s l _ hst.1 (by intros; simp)]
    cases h : Exec.step p (oracles H wit) s _ with
    | none => rfl
    | some r =>
      have hr := step_ledger_same p _ h hst.1 (by intros; simp_all)
      simp [hr, hll]

theorem steps_ctxmap (hW : WitnessesOK wit) : ∀ (P : List Stmt) (s : Exec.State ω LedgerState) (l : LedgerState),
    (∀ st ∈ P, DSQuiet st) → l.context = s.ledger.context →
    Exec.steps p (oracles H wit) P { s with ledger := l } =
      (Exec.steps p (oracles H wit) P s).map fun r => { r with ledger := { l with context := r.ledger.context } }
  | [], s, l, _, hl => by
      simp only [Exec.steps, Option.map_some]
      have : ({ l with context := s.ledger.context } : LedgerState) = l := by rw [← hl]
      rw [this]
  | st :: P, s, l, h, hl => by
      simp only [Exec.steps, step_ctxmap p H wit hW st (h st (List.mem_cons_self ..)) s l hl, Option.bind_eq_bind]
      cases hs : Exec.step p (oracles H wit) s st with
      | none => rfl
      | some r =>
        simp only [Option.map_some, Option.bind_some]
        rw [steps_ctxmap hW P r { l with context := r.ledger.context } (fun x hx => h x (List.mem_cons_of_mem _ hx)) rfl]

theorem steps_quiet_frame (hW : WitnessesOK wit) : ∀ (P : List Stmt) (s r : Exec.State ω LedgerState),
    (∀ st ∈ P, DSQuiet st) → Exec.steps p (oracles H wit) P s = some r →
      r.ledger.state = s.ledger.state ∧ r.ledger.effects = s.ledger.effects
  | [], s, r, _, h => by simp [Exec.steps] at h; subst h; exact ⟨rfl, rfl⟩
  | st :: P, s, r, hq, h => by
      simp only [Exec.steps, Option.bind_eq_bind] at h
      cases hs : Exec.step p (oracles H wit) s st with
      | none => simp [hs] at h
      | some r₁ =>
        simp only [hs, Option.bind_some] at h
        obtain ⟨h1, h2⟩ := steps_quiet_frame hW P r₁ r (fun x hx => hq x (List.mem_cons_of_mem _ hx)) h
        have hst := hq st (List.mem_cons_self ..)
        have e : r₁.ledger.state = s.ledger.state ∧ r₁.ledger.effects = s.ledger.effects := by
          cases st with
          | witness g name args outs sh =>
            exact step_witness_rel p (oracles H wit) (fun l l' => l'.state = l.state ∧ l'.effects = l.effects)
              (fun _ => ⟨rfl, rfl⟩) ((hW.ctxOnly (hst.2 g name args outs sh rfl)).step) hs
          | ledger g rs ops => exact absurd rfl (hst.1 g rs ops)
          | _ => rw [step_ledger_same p _ hs hst.1 (by intros; simp_all)]; exact ⟨rfl, rfl⟩
        exact ⟨h1.trans e.1, h2.trans e.2⟩

end

/-! ## Recognizing the pattern -/

theorem droppableWrite?_spec {s : Stmt} {k : Aligned Expr} (h : droppableWrite? s = some k) :
    ∃ v, s = .ledger (.const 1) [] [.push false k, .push true v, .ins false 1] ∧
      k.vals.all Expr.isConst = true ∧ droppableValue v = true := by
  unfold droppableWrite? at h
  split at h
  · rename_i k' v
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h; subst h
      simp only [Bool.and_eq_true] at hc
      exact ⟨v, rfl, hc.1, hc.2⟩
    · simp at h
  · simp at h

/-- A value the pass may drop always evaluates, fits its alignment and is hashable. -/
theorem droppableValue_spec (p : Prims) {v : Aligned Expr} (h : droppableValue v = true) (env : Env) :
    ∃ v' vv, v.mapM (Expr.eval p env) = some v' ∧ AV.ofAligned v' = some vv ∧ vv.toHash.isSome = true := by
  unfold droppableValue at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    · rename_i e
      obtain ⟨x, hx⟩ := total_nil_eval p env e h
      have hb : byteLen x.val ≤ 64 := by
        unfold byteLen
        split
        · omega
        · have h1 : x.val < 2 ^ 256 := Nat.lt_trans x.isLt (by decide)
          have h2 : x.val.log2 < 256 := (Nat.log2_lt (by omega)).mpr h1
          omega
      have hlt : x.val < 2 ^ 256 := Nat.lt_trans x.isLt (by decide)
      exact ⟨⟨[.field], [x]⟩, ⟨[.field], [x.val]⟩, by simp [Aligned.mapM, hx],
        by simp [AV.ofAligned, AV.ofFields, atomWidth, atomOfFields, atomFits, hb], by simp [AV.toHash, hlt]⟩
    · simp at h
  · split at h
    · rename_i vv hc
      unfold constAV at hc
      simp only [Option.bind_eq_bind] at hc
      obtain ⟨vs, hvs, hc⟩ := bind_some_elim hc
      exact ⟨⟨v.align, vs⟩, vv, by simp [Aligned.mapM, mapM_consts (p := p) (env := env) hvs], hc, h⟩
    · simp at h

theorem overwrites_spec {k : Aligned Expr} : ∀ {n : Nat} {rest : List Stmt}, overwrites k n rest = true →
    ∃ P v₂ R, rest = P ++ .ledger (.const 1) [] [.push false k, .push true v₂, .ins false 1] :: R ∧
      ∀ st ∈ P, DSQuiet st
  | 0, _, h => by simp [overwrites] at h
  | _ + 1, [], h => by simp [overwrites] at h
  | n + 1, s :: rest, h => by
      have quiet : DSQuiet s → overwrites k n rest = true → ∃ P v₂ R,
          s :: rest = P ++ .ledger (.const 1) [] [.push false k, .push true v₂, .ins false 1] :: R ∧
            ∀ st ∈ P, DSQuiet st := fun hs h' => by
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
        · simp_all
      | bind v hint e => exact quiet ⟨by intros; simp, by intros; simp_all⟩ (by simpa [overwrites] using h)
      | assert c m => exact quiet ⟨by intros; simp, by intros; simp_all⟩ (by simpa [overwrites] using h)
      | constrain e r => exact quiet ⟨by intros; simp, by intros; simp_all⟩ (by simpa [overwrites] using h)
      | witness g name args outs sh =>
        simp only [overwrites, Bool.and_eq_true] at h
        refine quiet ⟨by intros; simp, fun g' n a o sh' he => ?_⟩ h.2
        simp only [Stmt.witness.injEq] at he
        obtain ⟨-, rfl, -⟩ := he
        have := h.1
        simp only [stateWitness, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at this
        exact this

/-! ## The window -/

section Window
variable (p : Prims) (H : Hooks) {ω : Type} (wit : Damp.Exec.WitnessOracle ω LedgerState)

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

/-- A cell write neither reads nor changes the call context. -/
theorem cellWrite_ctx (k v : Aligned Fr) (q : LedgerState) (c : SV) :
    ledgerOracle H (writeOps k v) { q with context := c } =
      (ledgerOracle H (writeOps k v) q).map fun r => (r.1, { r.2 with context := c }) := by
  simp only [ledgerOracle_cellWrite, Option.bind_eq_bind]
  cases h1 : AV.ofAligned k <;> simp
  cases h2 : AV.ofAligned v <;> simp
  rename_i kv vv
  cases h3 : setCell q.state kv vv <;> simp
  cases h4 : decodeEffects q.effects <;> simp

theorem ledger_eta_ctx {q q' : LedgerState} (h1 : q'.state = q.state) (h2 : q'.effects = q.effects) :
    q' = { q with context := q'.context } := by
  cases q; cases q'; simp_all

theorem window (hW : WitnessesOK wit) {k : Aligned Expr} {v : Aligned Expr} (hk : k.vals.all Expr.isConst = true)
    (hv : ∀ env : Env, ∃ v' vv, v.mapM (Expr.eval p env) = some v' ∧ AV.ofAligned v' = some vv ∧
      vv.toHash.isSome = true)
    {P R : List Stmt} {v₂ : Aligned Expr} (hP : ∀ st ∈ P, DSQuiet st)
    (s : Exec.State ω LedgerState) :
    (Exec.steps p (oracles H wit)
        (.ledger (.const 1) [] [.push false k, .push true v, .ins false 1] ::
          (P ++ .ledger (.const 1) [] [.push false k, .push true v₂, .ins false 1] :: R)) s).map Exec.State.obs =
      (Exec.steps p (oracles H wit)
        (P ++ .ledger (.const 1) [] [.push false k, .push true v₂, .ins false 1] :: R) s).map Exec.State.obs := by
  obtain ⟨k', hk'⟩ := const_aligned_eval p hk
  obtain ⟨v', vv, hv1, hof, hhash⟩ := hv s.env
  have hvv : ∀ y ∈ v.vals, (y.eval p s.env).isSome := by
    have := (aligned_mapM_vals _ _ _ hv1).2
    rw [← evalList_eq_mapM] at this
    exact (evalList_isSome_iff p s.env _).mp (by simp [this])
  have htwice := fun w q => ledgerOracle_cellWrite_twice H k' v' w vv q hof hhash
  -- after the gap the ledger is the starting one with another call context
  have hgapL : ∀ sP, Exec.steps p (oracles H wit) P s = some sP →
      sP.ledger = { s.ledger with context := sP.ledger.context } := fun sP h => by
    obtain ⟨h1, h2⟩ := steps_quiet_frame p H wit hW P s sP hP h
    exact ledger_eta_ctx h1 h2
  have hW1 : ∀ sP, Exec.steps p (oracles H wit) P s = some sP →
      ledgerOracle H (writeOps k' v') sP.ledger =
        (ledgerOracle H (writeOps k' v') s.ledger).map fun r => (r.1, { r.2 with context := sP.ledger.context }) :=
    fun sP h => by rw [hgapL sP h, cellWrite_ctx]
  -- the groups of the dropped write
  have hgr : (ledgerGroups p s.env true
      [.push false k, .push true v, .ins false 1]).isSome := by
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
      all_goals first | rfl | exact hvv y hy
    · simp [Op.encode, Expr.evalList, Expr.eval]
  obtain ⟨gs, hgs⟩ := Option.isSome_iff_exists.mp hgr
  have h1 : asBool (Fr.ofInt 1) = some true := rfl
  have hstep : Exec.step p (oracles H wit) s
      (.ledger (.const 1) [] [.push false k, .push true v, .ins false 1]) =
      (ledgerOracle H (writeOps k' v') s.ledger).bind fun r =>
        (Exec.assign s.env [] r.1).bind fun env =>
          (ledgerGroups p env true [.push false k, .push true v, .ins false 1]).bind fun gs =>
            some { s with env, ledger := r.2, pub := s.pub ++ r.1, groups := s.groups ++ gs } := by
    simp only [Exec.step, Expr.eval, Option.bind_eq_bind, Option.bind_some, h1, request_write, hk', hv1]
    simp [oracles]
  rw [Exec.steps_append p (oracles H wit)]
  cases ho : ledgerOracle H (writeOps k' v') s.ledger with
  | none =>
    simp only [Exec.steps, hstep, ho, Option.bind_eq_bind, Option.bind_none, Option.map_none]
    cases hPs : Exec.steps p (oracles H wit) P s with
    | none => rfl
    | some sP =>
      have hW2 : ∀ w, ledgerOracle H (writeOps k' w) sP.ledger = none := fun w => by
        rw [← htwice w sP.ledger, hW1 sP hPs, ho]; rfl
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
    have hσ₁ : vals = [] ∧ σ₁.context = s.ledger.context := by
      rw [ledgerOracle_cellWrite] at ho
      simp only [Option.bind_eq_bind] at ho
      cases h1 : AV.ofAligned k' <;> simp [h1] at ho
      cases h2 : AV.ofAligned v' <;> simp [h2] at ho
      rename_i a b
      cases h3 : setCell s.ledger.state a b <;> simp [h3] at ho
      cases h4 : decodeEffects s.ledger.effects <;> simp [h4] at ho
      exact ⟨ho.1, by rw [← ho.2]⟩
    obtain ⟨hvals, hctx⟩ := hσ₁
    subst hvals
    have hL : Exec.steps p (oracles H wit)
        (.ledger (.const 1) [] [.push false k, .push true v, .ins false 1] ::
          (P ++ .ledger (.const 1) [] [.push false k, .push true v₂, .ins false 1] :: R)) s =
        Exec.steps p (oracles H wit) (P ++ .ledger (.const 1) [] [.push false k, .push true v₂, .ins false 1] :: R)
          { s with ledger := σ₁, pub := s.pub ++ [], groups := s.groups ++ gs } := by
      simp only [Exec.steps, hstep, ho, Option.bind_eq_bind, Option.bind_some, Exec.assign, hgs]
    -- the state after the dropped write differs from `s` only in the ledger (and the transcript)
    have hobs : Exec.State.obs { s with ledger := σ₁, pub := s.pub ++ [], groups := s.groups ++ gs } =
        Exec.State.obs { s with ledger := σ₁ } := rfl
    rw [hL, steps_obs p _ _ hobs, Exec.steps_append p (oracles H wit), steps_ctxmap p H wit hW P s σ₁ hP hctx]
    cases hPs : Exec.steps p (oracles H wit) P s with
    | none => rfl
    | some sP =>
      have heq : ∀ w, ledgerOracle H (writeOps k' w) { σ₁ with context := sP.ledger.context } =
          ledgerOracle H (writeOps k' w) sP.ledger := fun w => by
        rw [← htwice w sP.ledger, hW1 sP hPs, ho]; rfl
      simp only [Option.map_some, Option.bind_some, Exec.steps,
        step_W2_eq p H wit hk' v₂ sP { σ₁ with context := sP.ledger.context } heq]

theorem deadStore_go (hW : WitnessesOK wit) : ∀ (stmts : List Stmt) (s t : Exec.State ω LedgerState), s.obs = t.obs →
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
        exact deadStore_go hW rest r1 r2 e
      cases hd : droppableWrite? st with
      | none =>
        simp only [deadStoreGo, hd]; exact keep
      | some k =>
        by_cases ho : overwrites k deadStoreWindow rest = true
        · simp only [deadStoreGo, hd, ho, ite_true]
          obtain ⟨v, rfl, hk, hv⟩ := droppableWrite?_spec hd
          obtain ⟨P, v₂, R, rfl, hP⟩ := overwrites_spec ho
          rw [deadStore_go hW _ s t hobs, window p H wit hW hk (droppableValue_spec p hv) hP s]
        · simp only [deadStoreGo, hd, ho, Bool.false_eq_true, ite_false]; exact keep

end Window

/-- `Circuit.ledgerDeadStore` is sound against the modelled ledger (for any
    ledger state, well formed or not). -/
theorem Circuit.ledgerDeadStore_soundLedger : Pass.SoundLedger Circuit.ledgerDeadStore := by
  refine ⟨fun {ω} H p w hW c inputs pr σ _ => ?_⟩
  simp only [Exec.run, Circuit.ledgerDeadStore, List.toList_toArray, Option.bind_eq_bind]
  cases hb : bindInputs (fun _ => 0) c.inputs inputs with
  | none => simp
  | some env =>
    simp only [Option.bind_some]
    have e := deadStore_go p H w hW c.body.toList ⟨env, [], [], [], pr, σ⟩ ⟨env, [], [], [], pr, σ⟩ rfl
    cases h1 : Exec.steps p (oracles H w) (deadStoreGo c.body.toList) ⟨env, [], [], [], pr, σ⟩ <;>
      cases h2 : Exec.steps p (oracles H w) c.body.toList ⟨env, [], [], [], pr, σ⟩ <;>
      rw [h1, h2] at e <;> simp at e ⊢
    rename_i r1 r2
    simp only [Exec.State.obs, Prod.mk.injEq] at e
    obtain ⟨he, hp, hw, hl⟩ := e
    rw [he]
    cases Expr.evalList p r2.env c.outputs <;> simp [Result.ledgerObservable, hp, hw, hl]

end Damp.IR
