/-
`Circuit.ledgerHoist` (`Damp/Optimize/LedgerHoist.lean`) is sound against the
modelled ledger: `Circuit.ledgerHoist_soundLedger`.

A read of the call context (`dup 2; idx _ false path; popeq`) answers
`readSpec 2` on the call context and leaves the ledger state as it was
(`ledgerOracle_read`, on a well-formed state); no ledger statement changes the
call context (`ledgerOracle_context`). So, on the executor's state, the read
acts as a patch of the variables it binds that depends only on what it reads
and the call context (`step_ctx_patch`), and it commutes with any ledger
statement that neither reads nor binds those variables and whose own
variables it does not bind (`step_commute_ctx`): the executor's states after
the two orders agree on everything but the public transcript and the public
inputs (`Exec.State.obs`). With `step_commute` (statements that are not
ledger statements) the read moves above every statement between
(`steps_mid`), and `hoistGo_steps` follows by induction.
-/
import Damp.Optimize.LedgerHoist
import Damp.Proofs.Optimize.LedgerMerge

namespace Damp.IR
open Damp.Impact Damp.Exec Damp.Ledger
open Damp.Zkir (Prims Group)

set_option linter.unusedSimpArgs false

section Hoist
variable {ω : Type} (p : Prims) (H : Hooks) (w : String → List Fr → ω → Option (List Fr × ω))

theorem request_ctx {env : Env} {ci c : Bool} {path : List (Aligned Expr)} {a : List Zkir.AlignAtom}
    {res : List Expr} {req : List (Op Fr)}
    (h : Exec.request p env [.dup 2, .idx ci false path, .popeq c a res] = some req) :
    ∃ path', req = readOps 2 path' ci c a := by
  simp only [Exec.request, Op.mapM, Option.bind_eq_bind, Option.pure_def] at h
  cases hp : path.mapM (fun k : Aligned Expr => k.mapM (Expr.eval p env)) with
  | none => simp [hp] at h
  | some path' =>
    cases hr : res.mapM (Expr.eval p env) with
    | none => simp [hp, hr] at h
    | some res' =>
      simp [hp, hr] at h
      exact ⟨path', by rw [← h]; rfl⟩

/-- The oracle's answer to a context read: `readSpec 2`, the ledger unchanged. -/
theorem oracle_ctx {env : Env} {ci c : Bool} {path : List (Aligned Expr)} {a : List Zkir.AlignAtom}
    {res : List Expr} {req : List (Op Fr)} (q : LedgerState) (hq : q.WF)
    (h : Exec.request p env [.dup 2, .idx ci false path, .popeq c a res] = some req) :
    ∃ path', req = readOps 2 path' ci c a ∧
      ledgerOracle H req q = (readSpec 2 path' a q).map fun ys => (ys, q) := by
  obtain ⟨path', rfl⟩ := request_ctx p h
  exact ⟨path', rfl, ledgerOracle_read H 2 (by omega) path' ci c (Or.inr (by omega)) a q hq⟩

/-- **A context read is a patch** of the variables it binds, the same for every
    well-formed state that agrees on what it reads, the private state and the
    call context. -/
theorem step_ctx_patch (g : Expr) (rs : List Var) (ci c : Bool) (path : List (Aligned Expr))
    (a : List Zkir.AlignAtom) (res : List Expr) (s : Exec.State ω LedgerState) (hs : s.ledger.WF) :
    ∃ o : Option (Patch ω), (∀ P ∈ o, P.W = rs ∧ P.pv = s.private_ ∧ P.d = []) ∧
      ∀ t : Exec.State ω LedgerState, (∀ v ∈ g.vars ++ opsVars [.dup 2, .idx ci false path, .popeq c a res],
          t.env v = s.env v) → t.private_ = s.private_ → t.ledger.WF → t.ledger.context = s.ledger.context →
        (Exec.step p (oracles H w) t (.ledger g rs [.dup 2, .idx ci false path, .popeq c a res])).map
          Exec.State.obs = o.map fun P => (P.apply t).obs := by
  have hne : ([.dup 2, .idx ci false path, .popeq c a res] : List (Op Expr)) ≠ [] := by simp
  generalize hops : ([.dup 2, .idx ci false path, .popeq c a res] : List (Op Expr)) = ops at hne
  -- what `s` does
  let mk : Env → Patch ω := fun env' => ⟨rs, env', s.private_, []⟩
  have key : ∀ (t : Exec.State ω LedgerState) (env' : Env) (xs : List Fr),
      Exec.assign s.env (rs.map fun v => (v, none)) xs = some env' →
      Exec.assign t.env (rs.map fun v => (v, none)) xs = some ((mk env').env t.env) := by
    intro t env' xs h
    rw [assign_patch h t.env]
    congr 1; funext v; simp [Patch.env, mk]
  have hagree : ∀ (t : Exec.State ω LedgerState) (env' : Env),
      (∀ v ∈ g.vars ++ opsVars ops, t.env v = s.env v) →
      ∀ v ∈ opsVars ops, (mk env').env t.env v = (mk env').env s.env v := by
    intro t env' ht v hv
    simp only [Patch.env, mk]
    split
    · rfl
    · exact ht v (by simp [hv])
  -- the answer of the oracle on a state, from the call context
  have horacle : ∀ (t : Exec.State ω LedgerState) (req : List (Op Fr)), t.ledger.WF →
      t.ledger.context = s.ledger.context → Exec.request p t.env ops = some req →
      Exec.request p s.env ops = some req →
      (oracles H w).ledger req t.ledger = ((oracles H w).ledger req s.ledger).map fun r => (r.1, t.ledger) := by
    intro t req htw htc hreqt hreqs
    subst hops
    obtain ⟨path', rfl, ho⟩ := oracle_ctx p H t.ledger htw hreqt
    obtain ⟨path'', he, ho'⟩ := oracle_ctx p H s.ledger hs hreqs
    simp only [readOps, List.cons.injEq, Op.idx.injEq, true_and, and_true] at he
    subst he
    simp only [oracles]
    rw [ho, ho']
    rw [readSpec_congr (q := t.ledger) (q' := s.ledger) (by simp [LedgerState.comp, htc])]
    cases readSpec 2 path' a s.ledger <;> rfl
  have hledger : ∀ req r, (oracles H w).ledger req s.ledger = some r → Exec.request p s.env ops = some req →
      r.2 = s.ledger := by
    intro req r h hreqs
    subst hops
    obtain ⟨path', rfl, ho⟩ := oracle_ctx p H s.ledger hs hreqs
    simp only [oracles] at h
    rw [ho] at h
    obtain ⟨ys, _, rfl⟩ := Option.map_eq_some_iff.mp h
    rfl
  refine ⟨(Exec.step p (oracles H w) s (.ledger g rs ops)).map fun r => mk r.env, ?_, ?_⟩
  · intro P hP
    cases h : Exec.step p (oracles H w) s (.ledger g rs ops) <;> simp [h] at hP
    subst hP; exact ⟨rfl, rfl, rfl⟩
  · intro t ht htp htw htc
    rw [step_ledger_nf p _ t g rs ops hne, step_ledger_nf p _ s g rs ops hne]
    have hg : g.eval p t.env = g.eval p s.env := eval_congr_of fun v hv => ht v (by simp [hv])
    have hq : Exec.request p t.env ops = Exec.request p s.env ops :=
      lm_request_congr p ops fun v hv => ht v (by simp [hv])
    rw [hg]
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
          cases hz : Exec.assign s.env (rs.map fun v => (v, none)) (rs.map fun _ => 0) with
          | none =>
            simp [assign_none_any hz t.env]
          | some env' =>
            rw [key t env' _ hz]
            simp only [Option.bind_some, Option.map_map]
            rw [ledgerGroups_congr' p false ops (hagree t env' ht)]
            have hs' : (mk env').env s.env = env' := by
              funext v; simp only [Patch.env, mk]; split
              · rfl
              · exact (assign_frame hz v (by simpa using ‹_›)).symm
            rw [hs']
            cases ledgerGroups p env' false ops with
            | none => rfl
            | some gs =>
              simp [Exec.State.obs, Patch.apply, mk, htp]
        · simp only [ite_true]
          rw [hq]
          cases hreq : Exec.request p s.env ops with
          | none => rfl
          | some req =>
            simp only [Option.bind_some]
            rw [horacle t req htw htc (hq.trans hreq) hreq]
            cases hor : (oracles H w).ledger req s.ledger with
            | none => rfl
            | some r =>
              have hr2 := hledger req r hor hreq
              simp only [Option.map_some, Option.bind_some]
              cases hz : Exec.assign s.env (rs.map fun v => (v, none)) r.1 with
              | none => simp [assign_none_any hz t.env]
              | some env' =>
                rw [key t env' _ hz]
                simp only [Option.bind_some]
                rw [ledgerGroups_congr' p true ops (hagree t env' ht)]
                have hs' : (mk env').env s.env = env' := by
                  funext v; simp only [Patch.env, mk]; split
                  · rfl
                  · exact (assign_frame hz v (by simpa using ‹_›)).symm
                rw [hs']
                cases ledgerGroups p env' true ops with
                | none => rfl
                | some gs =>
                  simp [Exec.State.obs, Patch.apply, mk, htp, hr2]

/-- A ledger statement leaves the call context as it was. -/
theorem step_ledger_context {s r : Exec.State ω LedgerState} {g : Expr} {rs : List Var} {ops : List (Op Expr)}
    (h : Exec.step p (oracles H w) s (.ledger g rs ops) = some r) : r.ledger.context = s.ledger.context := by
  rcases step_ledger_cases p _ h with ⟨_, rfl⟩ | ⟨gv, _, h⟩
  · rfl
  · rcases h with ⟨_, hl, _⟩ | ⟨_, req, xs, _, ho, _⟩
    · rw [hl]
    · exact ledgerOracle_context ho

/-- **A context read and a ledger statement commute**, up to the public
    transcript and public inputs, when neither reads or binds what the other
    binds. -/
theorem step_commute_ctx (g : Expr) (rs : List Var) (ci c : Bool) (path : List (Aligned Expr))
    (a : List Zkir.AlignAtom) (res : List Expr) (g' : Expr) (rs' : List Var) (ops' : List (Op Expr))
    (hne' : ops' ≠ [])
    (hc : lcommutes (.ledger g rs [.dup 2, .idx ci false path, .popeq c a res]) (.ledger g' rs' ops') = true)
    (s : Exec.State ω LedgerState) (hs : s.ledger.WF) :
    ((Exec.step p (oracles H w) s (.ledger g' rs' ops')).bind fun r =>
        Exec.step p (oracles H w) r (.ledger g rs [.dup 2, .idx ci false path, .popeq c a res])).map Exec.State.obs =
      ((Exec.step p (oracles H w) s (.ledger g rs [.dup 2, .idx ci false path, .popeq c a res])).bind fun r =>
        Exec.step p (oracles H w) r (.ledger g' rs' ops')).map Exec.State.obs := by
  simp only [lcommutes, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false, Bool.or_eq_false_iff] at hc
  obtain ⟨⟨-, hc1⟩, hc2⟩ := hc
  obtain ⟨o, hW, ho⟩ := step_ctx_patch p H w g rs ci c path a res s hs
  -- the read sees, after the ledger statement, what it saw before
  have hafter : ∀ r, Exec.step p (oracles H w) s (.ledger g' rs' ops') = some r →
      (Exec.step p (oracles H w) r (.ledger g rs [.dup 2, .idx ci false path, .popeq c a res])).map Exec.State.obs =
        o.map fun P => (P.apply r).obs := by
    intro r hr
    apply ho r
    · intro v hv
      apply step_env_frame p _ hr v
      intro hvr
      have := hc1 v (by simpa [Stmt.mUses] using hv)
      simp [Stmt.mBinds, Stmt.lrBinds] at this hvr
      exact this hvr
    · exact ledger_step_private p _ hr
    · exact step_wf p H w hr hs
    · exact step_ledger_context p H w hr
  cases o with
  | none =>
    have hn : Exec.step p (oracles H w) s (.ledger g rs [.dup 2, .idx ci false path, .popeq c a res]) = none := by
      have := ho s (fun _ _ => rfl) rfl hs rfl
      cases h : Exec.step p (oracles H w) s (.ledger g rs [.dup 2, .idx ci false path, .popeq c a res]) <;>
        simp_all
    rw [hn]
    cases h : Exec.step p (oracles H w) s (.ledger g' rs' ops') with
    | none => rfl
    | some r => simp only [Option.bind_some]; rw [hafter r h]; rfl
  | some P =>
    obtain ⟨hPW, -, -⟩ := hW P rfl
    have hs1 := ho s (fun _ _ => rfl) rfl hs rfl
    cases h1 : Exec.step p (oracles H w) s (.ledger g rs [.dup 2, .idx ci false path, .popeq c a res]) with
    | none => rw [h1] at hs1; simp at hs1
    | some r1 =>
      rw [h1] at hs1
      simp only [Option.map_some, Option.some.injEq] at hs1
      simp only [Option.bind_some]
      -- `r1` is `P.apply s` up to the transcript
      rw [step_obs p _ hs1 (.ledger g' rs' ops')]
      rw [step_ledger_patch p _ P s g' rs' ops' hne'
        (fun v hv hvW => by
          rw [hPW] at hvW
          have := hc2 v (by simpa [Stmt.mBinds] using hvW)
          simp only [Stmt.mUses, Bool.or_eq_true, List.contains_iff_mem] at this
          exact this (Or.inl (by simpa using hv)))
        (fun v hv hvW => by
          rw [hPW] at hvW
          have := hc2 v (by simpa [Stmt.mBinds] using hvW)
          simp only [Stmt.mBinds, Bool.or_eq_true, List.contains_iff_mem] at this
          exact this (Or.inr hv))]
      cases h : Exec.step p (oracles H w) s (.ledger g' rs' ops') with
      | none => rfl
      | some r => simp only [Option.map_some, Option.bind_some]; rw [hafter r h]; rfl

theorem ctxRead_spec {r : Stmt} (h : r.ctxRead = true) :
    ∃ g rs ci c path a res, r = .ledger g rs [.dup 2, .idx ci false path, .popeq c a res] := by
  unfold Stmt.ctxRead at h
  split at h
  · exact ⟨_, _, _, _, _, _, _, rfl⟩
  · simp at h

theorem findCtxRead_spec {g : Expr} {rs : List Var} {ops : List (Op Expr)} :
    ∀ {n : Nat} {l mid rest : List Stmt} {r : Stmt}, findCtxRead g rs ops n l = some (mid, r, rest) →
      l = mid ++ r :: rest ∧ r.ctxRead = true ∧ ∀ x ∈ mid, lcommutes r x = true ∧ x.emptyLedger = false
  | 0, _, _, _, _, h => by simp [findCtxRead] at h
  | _ + 1, [], _, _, _, h => by simp [findCtxRead] at h
  | n + 1, x :: l, mid, rest, r, h => by
      simp only [findCtxRead] at h
      by_cases hx : (x.ctxRead && x.guardIs g && (mergeInto g rs ops x).isSome) = true
      · rw [if_pos hx] at h
        simp only [Bool.and_eq_true] at hx
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨rfl, hx.1.1, by simp⟩
      · rw [if_neg hx] at h
        cases h' : findCtxRead g rs ops n l with
        | none => simp [h'] at h
        | some t =>
          obtain ⟨mid', r', rest'⟩ := t
          simp only [h', Option.bind_some] at h
          by_cases hc : (lcommutes r' x && !x.emptyLedger) = true
          · rw [if_pos hc] at h
            simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            obtain ⟨rfl, hr, hm⟩ := findCtxRead_spec h'
            refine ⟨rfl, hr, fun y hy => ?_⟩
            simp only [List.mem_cons] at hy
            rcases hy with rfl | hy
            · exact hc
            · exact hm y hy
          · rw [if_neg hc] at h; simp at h

theorem bind_steps_obs {A A' : Option (Exec.State ω LedgerState)} (h : A.map Exec.State.obs = A'.map Exec.State.obs)
    (L : List Stmt) :
    (A.bind fun r => Exec.steps p (oracles H w) L r).map Exec.State.obs =
      (A'.bind fun r => Exec.steps p (oracles H w) L r).map Exec.State.obs := by
  cases A <;> cases A' <;> simp at h ⊢
  exact steps_obs p _ L h

/-- The context read `r` moves above the statements it commutes with. -/
theorem steps_mid {r : Stmt} (hr : r.ctxRead = true) :
    ∀ (mid rest : List Stmt), (∀ x ∈ mid, lcommutes r x = true ∧ x.emptyLedger = false) →
      ∀ s : Exec.State ω LedgerState, s.ledger.WF →
        (Exec.steps p (oracles H w) (mid ++ r :: rest) s).map Exec.State.obs =
          (Exec.steps p (oracles H w) (r :: mid ++ rest) s).map Exec.State.obs
  | [], rest, _, s, _ => rfl
  | x :: mid, rest, h, s, hs => by
      obtain ⟨g, rs, ci, c, path, a, res, rfl⟩ := ctxRead_spec hr
      have hx := h x (by simp)
      have ih := steps_mid hr mid rest (fun y hy => h y (by simp [hy]))
      -- after `x`, the read moves above `mid`
      have e1 : (Exec.steps p (oracles H w) (x :: mid ++ .ledger g rs [.dup 2, .idx ci false path, .popeq c a res] ::
            rest) s).map Exec.State.obs =
          (((Exec.step p (oracles H w) s x).bind fun r =>
              Exec.step p (oracles H w) r (.ledger g rs [.dup 2, .idx ci false path, .popeq c a res])).bind
            fun r => Exec.steps p (oracles H w) (mid ++ rest) r).map Exec.State.obs := by
        simp only [List.cons_append, Exec.steps, Option.bind_eq_bind]
        cases hx1 : Exec.step p (oracles H w) s x with
        | none => rfl
        | some r1 =>
          simp only [Option.bind_some]
          rw [ih r1 (step_wf p H w hx1 hs)]
          simp only [List.cons_append, Exec.steps, Option.bind_eq_bind]
      rw [e1]
      have e2 : (Exec.steps p (oracles H w)
            (.ledger g rs [.dup 2, .idx ci false path, .popeq c a res] :: (x :: mid ++ rest)) s).map Exec.State.obs =
          (((Exec.step p (oracles H w) s (.ledger g rs [.dup 2, .idx ci false path, .popeq c a res])).bind
              fun r => Exec.step p (oracles H w) r x).bind
            fun r => Exec.steps p (oracles H w) (mid ++ rest) r).map Exec.State.obs := by
        simp only [List.cons_append, Exec.steps, Option.bind_eq_bind]
        cases Exec.step p (oracles H w) s (.ledger g rs [.dup 2, .idx ci false path, .popeq c a res]) with
        | none => rfl
        | some r1 => rfl
      rw [show (Stmt.ledger g rs [.dup 2, .idx ci false path, .popeq c a res] :: x :: mid ++ rest) =
        (Stmt.ledger g rs [.dup 2, .idx ci false path, .popeq c a res] :: (x :: mid ++ rest)) from rfl, e2]
      apply bind_steps_obs p H w
      cases x with
      | ledger g' rs' ops' =>
        have hne' : ops' ≠ [] := by
          intro h0; subst h0; simp [Stmt.emptyLedger] at hx
        exact step_commute_ctx p H w g rs ci c path a res g' rs' ops' hne' hx.1 s hs
      | _ =>
        rw [step_commute p _ _ (by rfl) g rs _ (by simp) hx.1 s]
  termination_by mid => mid.length

theorem hoistGo_steps : ∀ (fuel : Nat) (l : List Stmt) (s t : Exec.State ω LedgerState), s.obs = t.obs →
    s.ledger.WF →
    (Exec.steps p (oracles H w) (hoistGo fuel l) t).map Exec.State.obs =
      (Exec.steps p (oracles H w) l s).map Exec.State.obs
  | 0, l, s, t, h, _ => (steps_obs p _ l h).symm
  | _ + 1, [], s, t, h, _ => by simp [hoistGo, Exec.steps, h]
  | fuel + 1, st :: rest, s, t, h, hs => by
      have keep : (Exec.steps p (oracles H w) (st :: hoistGo fuel rest) t).map Exec.State.obs =
          (Exec.steps p (oracles H w) (st :: rest) s).map Exec.State.obs := by
        have e := step_obs p (oracles H w) h st
        simp only [Exec.steps, Option.bind_eq_bind]
        cases h1 : Exec.step p (oracles H w) s st <;> cases h2 : Exec.step p (oracles H w) t st <;>
          rw [h1, h2] at e <;> simp at e ⊢
        rename_i r1 r2
        exact hoistGo_steps fuel rest r1 r2 e (step_wf p H w h1 hs)
      unfold hoistGo
      split
      · rename_i g rs ops
        split
        · rename_i mid r rest' hf
          obtain ⟨rfl, hr, hm⟩ := findCtxRead_spec hf
          have e := step_obs p (oracles H w) h (.ledger g rs ops)
          simp only [Exec.steps, Option.bind_eq_bind]
          cases h1 : Exec.step p (oracles H w) s (.ledger g rs ops) <;>
            cases h2 : Exec.step p (oracles H w) t (.ledger g rs ops) <;> rw [h1, h2] at e <;> simp at e ⊢
          rename_i u1 u2
          have hu1 := step_wf p H w h1 hs
          rw [steps_mid p H w hr mid rest' hm u1 hu1]
          simp only [List.cons_append, Exec.steps, Option.bind_eq_bind]
          have e2 := step_obs p (oracles H w) e r
          cases h3 : Exec.step p (oracles H w) u1 r <;> cases h4 : Exec.step p (oracles H w) u2 r <;>
            rw [h3, h4] at e2 <;> simp at e2 ⊢
          rename_i v1 v2
          exact hoistGo_steps fuel (mid ++ rest') v1 v2 e2 (step_wf p H w h3 hu1)
        · exact keep
      · exact keep

end Hoist

/-- `Circuit.ledgerHoist` is sound against the modelled ledger. -/
theorem Circuit.ledgerHoist_soundLedger : Pass.SoundLedger Circuit.ledgerHoist := by
  refine ⟨fun {ω} H p w c inputs pr σ hσ => ?_⟩
  simp only [Exec.run, Circuit.ledgerHoist, List.toList_toArray, Option.bind_eq_bind]
  cases hb : bindInputs (fun _ => 0) c.inputs inputs with
  | none => simp
  | some env =>
    simp only [Option.bind_some]
    have e := hoistGo_steps p H w (c.body.size + 1) c.body.toList ⟨env, [], [], [], pr, σ⟩ ⟨env, [], [], [], pr, σ⟩
      rfl hσ
    cases h1 : Exec.steps p (oracles H w) (hoistGo (c.body.size + 1) c.body.toList) ⟨env, [], [], [], pr, σ⟩ <;>
      cases h2 : Exec.steps p (oracles H w) c.body.toList ⟨env, [], [], [], pr, σ⟩ <;>
      rw [h1, h2] at e <;> simp at e ⊢
    rename_i r1 r2
    simp only [Exec.State.obs, Prod.mk.injEq] at e
    obtain ⟨he, hp, hw, hl⟩ := e
    rw [he]
    cases Expr.evalList p r2.env c.outputs <;> simp [Result.ledgerObservable, hp, hw, hl]

theorem hoistGo_mem : ∀ (fuel : Nat) (l : List Stmt), ∀ x ∈ hoistGo fuel l, x ∈ l
  | 0, l, x, hx => hx
  | _ + 1, [], x, hx => by simp [hoistGo] at hx
  | fuel + 1, st :: rest, x, hx => by
      unfold hoistGo at hx
      split at hx
      · split at hx
        · rename_i mid r rest' hf
          obtain ⟨rfl, -, -⟩ := findCtxRead_spec hf
          simp only [List.mem_cons] at hx
          rcases hx with rfl | rfl | hx
          · simp
          · simp
          · have := hoistGo_mem fuel (mid ++ rest') x hx
            simp only [List.mem_append] at this
            rcases this with h | h <;> simp [h]
        · simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · simp
          · exact List.mem_cons_of_mem _ (hoistGo_mem fuel rest x hx)
      · simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · simp
        · exact List.mem_cons_of_mem _ (hoistGo_mem fuel rest x hx)

/-- `Circuit.ledgerHoist` keeps a circuit's ledger statements well formed: it only reorders them. -/
theorem Circuit.ledgerHoist_checkLedger : Pass.KeepsLedger Circuit.ledgerHoist := by
  intro c h
  rw [LedgerWF.Circuit.checkLedger_ok_iff] at h ⊢
  intro s hs
  simp only [Circuit.ledgerHoist, List.toList_toArray] at hs
  exact h s (hoistGo_mem _ _ s hs)

end Damp.IR
