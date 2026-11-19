/-
The entry point for contract-level theorems: a `Runs` description of a circuit
function's body, applied to its decoded arguments, gives the run of the circuit
`mkCircuit` builds.
-/
import Damp.Proofs.Interface.Bytes

namespace Damp
open IR

variable {p : Zkir.Prims}

/-- Running a body described by `Runs` from the start of a circuit. -/
theorem runBody_of_Runs {ρ : Type} [Value ρ] {m : CircuitM ρ} {N : Nat} {xs priv pub : List Fr}
    {ok : Prop} [Decidable ok] {outs : List Fr}
    (h : Runs p m { next := N } { env := fun v => xs.getD v 0, priv, pub } ok (fun r env => Value.Is p env r outs)) :
    runBody p (m.run { next := N }).2.stmts.toList (Value.toExprs (m.run { next := N }).1)
        (fun v => xs.getD v 0) priv pub =
      if ok ∧ priv = [] ∧ pub = [] then some { outputs := outs, groups := [] } else none := by
  obtain ⟨-, -, T, hT, hs, hst⟩ := h
  have hT' : (m.run { next := N }).2.stmts.toList = T := by rw [hT]; rfl
  unfold runBody
  rw [hT']
  cases he : execAll p T { env := fun v => xs.getD v 0, priv, pub } with
  | none =>
    have : ¬ ok := by rw [← hs, he]; simp
    simp [this]
  | some st' =>
    have hok : ok := hs.1 (by rw [he]; rfl)
    obtain ⟨-, hp, hq, hg, hQ⟩ := hst st' he
    simp only at hp hq hg
    have hout : Expr.evalList p st'.env (Value.toExprs (m.run { next := N }).1) = some outs := hQ.holds
    simp only [hok, true_and]
    show (Expr.evalList p st'.env (Value.toExprs (m.run { next := N }).1)).bind _ = _
    rw [hout, Option.bind_some, hp, hq, hg]
    by_cases h1 : priv = [] <;> by_cases h2 : pub = [] <;> simp [h1, h2]

/-- **Contract-level runs.** If the body, applied to the arguments read off the input
    variables, is described by `Runs` with outputs `outs`, then on inputs of the right number
    that pass their range checks the circuit accepts exactly when `ok` holds (and the
    transcripts are empty), and then outputs `outs`. -/
theorem mkCircuit_run_of_Runs {φ : Type} [CircuitFn φ] [CircuitFnSpec φ] (name : String) (names : List String)
    (f : φ) {xs priv pub : List Fr} {ok : Prop} [Decidable ok] {outs : List Fr}
    (hlen : xs.length = (CircuitFnSpec.ranges φ).length)
    (hr : rangesHold (CircuitFnSpec.ranges φ) xs = true)
    (h : Runs p (CircuitFnSpec.apply f (argVars 0 (CircuitFnSpec.ranges φ).length))
      { next := (CircuitFnSpec.ranges φ).length } { env := fun v => xs.getD v 0, priv, pub } ok
      (fun r env => Value.Is p env r outs)) :
    (mkCircuit name names f).run p xs priv pub =
      if ok ∧ priv = [] ∧ pub = [] then some { outputs := outs, groups := [] } else none := by
  rw [mkCircuit_run]; simp only [hlen, hr, and_self, ↓reduceIte]
  exact runBody_of_Runs h

/-- And on inputs that fail a range check, or are too many or too few, it rejects. -/
theorem mkCircuit_run_reject {φ : Type} [CircuitFn φ] [CircuitFnSpec φ] (name : String) (names : List String)
    (f : φ) {xs priv pub : List Fr}
    (h : ¬ (xs.length = (CircuitFnSpec.ranges φ).length ∧ rangesHold (CircuitFnSpec.ranges φ) xs = true)) :
    (mkCircuit name names f).run p xs priv pub = none := by
  rw [mkCircuit_run]; split
  · exact absurd ‹_› h
  · rfl

/-- A `Uint m` read off an input variable means the input's number, stably, once the input
    passed its range check. -/
theorem arg_uint_means {m : Nat} (hm : m ≤ Uint.maxBound) {k : Nat} {env : Env} {v : Var} (hv : v < k)
    (h : (uintRange m).holds (env v) = true) :
    Stable k env (fun e => Uint.Means p e (Value.ofExprs [Expr.var v] : Uint m) (env v).val) := by
  intro e he
  have hv' := he v hv
  refine ⟨hm, (uintRange_holds (Uint.lt_of_le_maxBound hm) _ ▸ h |> of_decide_eq_true), ?_⟩
  show (Uint.capped m (.var v)).eval p e = _
  rw [Uint.capped_eval hm]; show some (e v) = _; rw [← hv', Fr.ofNat_val]

/-- A `Boolean` read off an input variable that passed its range check means a truth value, stably. -/
theorem arg_boolean_means {k : Nat} {env : Env} {v : Var} (hv : v < k) {b : Bool} (h : env v = Fr.ofBool b) :
    Stable k env (fun e => Boolean.Is p e (Value.ofExprs [Expr.var v] : Boolean) b) := by
  intro e he
  show some (e v) = _; rw [← he v hv, h]

end Damp
