/-
Soundness of a pass relative to one choice of hash functions.

The IR semantics (`Circuit.run`, `Exec.run`) takes the hash functions as a
parameter `p : Prims`, and `Pass.Sound` asks a pass to preserve what a run
produces for *every* `p`. A pass that computes a hash at compile time
(`Circuit.foldHashes p`) cannot: it bakes in the values of one `p`.
`Pass.SoundFor p f` is the same two equalities at that one `p`.

* A sound pass is sound for every `p` (`Pass.Sound.soundFor`).
* Passes sound for `p` compose (`Pass.SoundFor.comp`, `runPasses_soundFor`).
* The generic vehicle `Circuit.mapExprs` is sound for `p` when the rewrite
  preserves `Expr.eval` at `p` (`Circuit.mapExprs_soundFor`).
-/
import Damp.Proofs.Optimize.Algebra

namespace Damp.IR
open Damp.Zkir (Prims Outcome)
open Damp.Exec

/-- At `p`, the pass does not change what a run produces that anyone can observe. -/
def Pass.SoundRunFor (p : Prims) (f : Pass) : Prop :=
  ∀ (c : Circuit) (inputs priv pub : List Fr),
    ((f c).run p inputs priv pub).map Outcome.observable =
      (c.run p inputs priv pub).map Outcome.observable

/-- At `p`, the pass does not change what the executor does, for any oracles. -/
def Pass.SoundExecFor (p : Prims) (f : Pass) : Prop :=
  ∀ {ω σ : Type} (O : Oracles ω σ) (c : Circuit) (inputs : List Fr) (private_ : ω) (ledger : σ),
    (Exec.run p O (f c) inputs private_ ledger).map Result.observable =
      (Exec.run p O c inputs private_ ledger).map Result.observable

/-- A pass sound when the hash functions are `p`. -/
structure Pass.SoundFor (p : Prims) (f : Pass) : Prop where
  run : Pass.SoundRunFor p f
  exec : Pass.SoundExecFor p f

/-- A sound pass is sound for every choice of hash functions. -/
theorem Pass.Sound.soundFor {f : Pass} (h : Pass.Sound f) (p : Prims) : Pass.SoundFor p f :=
  ⟨fun c i pr pu => h.run p c i pr pu, fun O c i w l => h.exec p O c i w l⟩

theorem Pass.SoundFor.id (p : Prims) : Pass.SoundFor p (fun c => c) := Pass.Sound.id.soundFor p

/-- Passes sound for `p` compose. -/
theorem Pass.SoundFor.comp {p : Prims} {f g : Pass} (hf : Pass.SoundFor p f) (hg : Pass.SoundFor p g) :
    Pass.SoundFor p (fun c => g (f c)) :=
  ⟨fun c i pr pu => (hg.run (f c) i pr pu).trans (hf.run c i pr pu),
   fun O c i w l => (hg.exec O (f c) i w l).trans (hf.exec O c i w l)⟩

/-- A list of passes sound for `p`, applied in order, is sound for `p`. -/
theorem runPasses_soundFor (p : Prims) :
    ∀ (ps : List Pass), (∀ f ∈ ps, Pass.SoundFor p f) → Pass.SoundFor p (runPasses ps)
  | [], _ => Pass.SoundFor.id p
  | f :: ps, h => by
      have hf := h f (List.mem_cons_self ..)
      have hps := runPasses_soundFor p ps fun g hg => h g (List.mem_cons_of_mem _ hg)
      exact Pass.SoundFor.comp (f := f) (g := runPasses ps) hf hps

/-! ## The generic vehicle at one `p` -/

section VehicleAt
variable {p : Prims} {f : Expr → Expr}

/-- `f` preserves evaluation exactly at `p`, failures included. -/
def EvalPreservingAt (p : Prims) (f : Expr → Expr) : Prop := ∀ (env : Env) (e : Expr), (f e).eval p env = e.eval p env

theorem EvalPreservingAt.eq (hf : EvalPreservingAt p f) : ∀ (env : Env) (e : Expr), (f e).eval p env = e.eval p env := hf

theorem EvalPreserving.at (hf : EvalPreserving f) (p : Prims) : EvalPreservingAt p f := fun env e => hf p env e

theorem Expr.keepLeaves_evalAt (hf : EvalPreservingAt p f) : EvalPreservingAt p (Expr.keepLeaves f) := by
  intro env e
  cases e <;> first | rfl | exact hf env _

theorem evalList_mapAt (hf : EvalPreservingAt p f) (env : Env) :
    ∀ xs : List Expr, Expr.evalList p env (xs.map f) = Expr.evalList p env xs
  | [] => rfl
  | x :: xs => by
      simp only [List.map_cons, Expr.evalList, hf env x, evalList_mapAt hf env xs]

theorem request_mapAt (hf : EvalPreservingAt p f) (env : Env) :
    ∀ ops : List (Impact.Op Expr), Exec.request p env (ops.map (·.map f)) = Exec.request p env ops
  | [] => rfl
  | op :: ops => by
      simp only [List.map_cons, Exec.request]
      rw [Exec.Op.mapM_map f (Expr.eval p env) (Expr.eval p env) (hf env) op, request_mapAt hf env ops]

theorem ledgerGroups_mapAt (hf : EvalPreservingAt p f) (hc : ∀ k, f (.const k) = .const k) (env : Env)
    (active : Bool) :
    ∀ ops : List (Impact.Op Expr), ledgerGroups p env active (ops.map (·.map f)) = ledgerGroups p env active ops
  | [] => rfl
  | op :: ops => by
      simp only [List.map_cons, ledgerGroups]
      rw [Op.encode_map f hc, evalList_mapAt hf, ledgerGroups_mapAt hf hc env active ops]

theorem Stmt.mapExprs_execAt (hf : EvalPreservingAt p f) (hc : ∀ k, f (.const k) = .const k)
    (s : RunState) (st : Stmt) : (st.mapExprs f).exec p s = st.exec p s := by
  cases st with
  | bind v hint e => simp only [Stmt.mapExprs, Stmt.exec, hf.eq]
  | assert c msg => simp only [Stmt.mapExprs, Stmt.exec, hf.eq]
  | constrain e r => simp only [Stmt.mapExprs, Stmt.exec, hf.eq]
  | witness guard name args outs shape => simp only [Stmt.mapExprs, Stmt.exec, hf.eq]
  | ledger guard reads ops =>
      rw [Stmt.mapExprs_ledger]
      split
      · have he : (ops.map (·.map f)).isEmpty = ops.isEmpty := by cases ops <;> rfl
        simp only [Stmt.exec, hf.eq, he, ledgerGroups_mapAt hf hc]
      · simp only [Stmt.exec, hf.eq]

theorem Stmt.mapExprs_stepAt (hf : EvalPreservingAt p f) (hc : ∀ k, f (.const k) = .const k)
    {ω σ : Type} (O : Exec.Oracles ω σ) (s : Exec.State ω σ) (st : Stmt) :
    Exec.step p O s (st.mapExprs f) = Exec.step p O s st := by
  cases st with
  | bind v hint e => simp only [Stmt.mapExprs, Exec.step, hf.eq]
  | assert c msg => simp only [Stmt.mapExprs, Exec.step, hf.eq]
  | constrain e r => simp only [Stmt.mapExprs, Exec.step, hf.eq]
  | witness guard name args outs shape =>
      simp only [Stmt.mapExprs, Exec.step, hf.eq, evalList_mapAt hf]
  | ledger guard reads ops =>
      rw [Stmt.mapExprs_ledger]
      split
      · have he : (ops.map (·.map f)).isEmpty = ops.isEmpty := by cases ops <;> rfl
        simp only [Exec.step, hf.eq, he, ledgerGroups_mapAt hf hc, request_mapAt hf]
      · simp only [Exec.step, hf.eq]

theorem execAll_mapExprsAt (hf : EvalPreservingAt p f) (hc : ∀ k, f (.const k) = .const k) :
    ∀ (stmts : List Stmt) (s : RunState), execAll p (stmts.map (Stmt.mapExprs f)) s = execAll p stmts s
  | [], _ => rfl
  | st :: rest, s => by
      simp only [List.map_cons, execAll, Stmt.mapExprs_execAt hf hc, execAll_mapExprsAt hf hc rest]

theorem steps_mapExprsAt (hf : EvalPreservingAt p f) (hc : ∀ k, f (.const k) = .const k)
    {ω σ : Type} (O : Exec.Oracles ω σ) :
    ∀ (stmts : List Stmt) (s : Exec.State ω σ), Exec.steps p O (stmts.map (Stmt.mapExprs f)) s = Exec.steps p O stmts s
  | [], _ => rfl
  | st :: rest, s => by
      simp only [List.map_cons, Exec.steps, Stmt.mapExprs_stepAt hf hc, steps_mapExprsAt hf hc O rest]

/-- Rewriting every expression with a function that preserves evaluation at
    `p` does not change a run at `p` at all. -/
theorem Circuit.mapExprs_runAt (hf : EvalPreservingAt p f) (c : Circuit) (inputs priv pub : List Fr) :
    (c.mapExprs f).run p inputs priv pub = c.run p inputs priv pub := by
  have hk := Expr.keepLeaves_evalAt hf
  simp only [Circuit.run, Circuit.mapExprs, Array.toList_map,
    execAll_mapExprsAt hk (fun k => Expr.keepLeaves_const k), evalList_mapAt hk]

/-- ... nor what the executor does at `p`. -/
theorem Circuit.mapExprs_execAt (hf : EvalPreservingAt p f) {ω σ : Type} (O : Exec.Oracles ω σ)
    (c : Circuit) (inputs : List Fr) (private_ : ω) (ledger : σ) :
    Exec.run p O (c.mapExprs f) inputs private_ ledger = Exec.run p O c inputs private_ ledger := by
  have hk := Expr.keepLeaves_evalAt hf
  simp only [Exec.run, Circuit.mapExprs, Array.toList_map,
    steps_mapExprsAt hk (fun k => Expr.keepLeaves_const k) O, evalList_mapAt hk]

/-- The generic vehicle at `p`. -/
theorem Circuit.mapExprs_soundFor (hf : EvalPreservingAt p f) : Pass.SoundFor p (Circuit.mapExprs f) :=
  ⟨fun c inputs priv pub => by rw [Circuit.mapExprs_runAt hf],
   fun O c inputs private_ ledger => by rw [Circuit.mapExprs_execAt hf]⟩

end VehicleAt

end Damp.IR
