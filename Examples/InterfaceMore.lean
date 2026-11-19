import Damp
import Damp.Proofs.Interface.Circuit

/-!
Contract-level theorems about circuits written in the surface syntax, proved with the
interface lemmas of `Damp/Proofs/Interface/`.
-/
namespace Examples.InterfaceMore
open Damp Damp.IR

struct Order where
  qty : Uint8
  price : Uint8

/-- Settle a payment, or refund part of it: the refund must not exceed the amount. -/
circuit settle (amount refund : Uint16) (isRefund : Boolean) : Uint16 := do
  if% isRefund then amount.sub refund else pure amount

/-- Charge an order to a balance: the cost must be covered. -/
circuit charge (o : Order) (balance : Uint16) : Uint16 := do
  const cost := o.qty * o.price
  require (cost <=. balance) "insufficient balance"
  balance.sub cost

variable (p : Zkir.Prims)

theorem charge_ranges : CircuitFnSpec.ranges (Order → Uint16 → CircuitM Uint16) =
    [some (uintRange 255), some (uintRange 255), some (uintRange 65535)] := by
  simp [Value.ranges, Value.shape, Shape.ranges_struct, Shape.ranges_prim, ranges_uint]

example (o : Order) (b : Uint16) : charge o b = (Damp.val (o.qty * o.price) "cost" >>= fun cost =>
    Damp.require (cost <=. b) "insufficient balance" >>= fun _ => b.sub cost) := rfl

theorem charge_apply : CircuitFnSpec.apply charge (argVars 0 3) =
    charge (Value.ofExprs [.var 0, .var 1]) (Value.ofExprs [.var 2]) := rfl

theorem charge_runs (q pr bal : Fr) (hq : q.val ≤ 255) (hpr : pr.val ≤ 255) (hbal : bal.val ≤ 65535) :
    Runs p (charge (Value.ofExprs [.var 0, .var 1]) (Value.ofExprs [.var 2])) { next := 3 }
      { env := fun v => [q, pr, bal].getD v 0, priv := [], pub := [] } (q.val * pr.val ≤ bal.val)
      (fun r env => Value.Is p env r [Fr.ofNat (bal.val - q.val * pr.val)]) := by
  have u255 : (255 : Nat) < 2 ^ 254 := by decide
  have u65535 : (65535 : Nat) < 2 ^ 254 := by decide
  have hQ := arg_uint_means (p := p) (m := 255) (by decide) (k := 3) (env := fun v => [q, pr, bal].getD v 0)
    (v := 0) (by decide) (by rw [uintRange_holds u255]; simpa using hq)
  have hP := arg_uint_means (p := p) (m := 255) (by decide) (k := 3) (env := fun v => [q, pr, bal].getD v 0)
    (v := 1) (by decide) (by rw [uintRange_holds u255]; simpa using hpr)
  have hB := arg_uint_means (p := p) (m := 65535) (by decide) (k := 3) (env := fun v => [q, pr, bal].getD v 0)
    (v := 2) (by decide) (by rw [uintRange_holds u65535]; simpa using hbal)
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hQ hP hB
  -- `const cost := o.qty * o.price`
  refine Runs.bind' (Runs.val_uint "cost" ((hQ.and hP).imp fun e h => Uint.mul_means (by decide) h.1 h.2))
    (Grows.bind (Grows.require _ _) fun _ => Grows.sub _ _) fun st₁ ha₁ hp₁ hq₁ hg₁ hcost => ?_
  have hg := (Grows.val ((Value.ofExprs [Expr.var 0, .var 1] : Order).qty * (Value.ofExprs [Expr.var 0, .var 1] : Order).price) "cost" { next := 3 })
  generalize (Damp.val ((Value.ofExprs [Expr.var 0, .var 1] : Order).qty *
    (Value.ofExprs [Expr.var 0, .var 1] : Order).price) "cost").run { next := 3 } = q₁ at hcost hg ⊢
  obtain ⟨cost, s₁⟩ := q₁
  simp only at hcost hg ⊢
  have hB₁ := (hB.transfer ha₁).mono hg.1
  -- `require (cost <=. balance)`
  have hreq := Runs.require_top (p := p) (s := s₁) (st := st₁)
    (c := cmpLe cost (Value.ofExprs [Expr.var 2] : Uint16)) "insufficient balance" hg.2.1
    ((hcost.and hB₁).imp fun e h => cmpLe_means h.1 h.2)
  refine (Runs.bind hreq (Grows.sub _ _) fun st₂ ha₂ hp₂ hq₂ hg₂ _ => ?_).conseq
    (ok := decide (q.val * pr.val ≤ bal.val) = true ∧ q.val * pr.val ≤ bal.val) (by simp) (fun _ _ h => h)
  have hs₂ := Grows.require (cmpLe cost (Value.ofExprs [Expr.var 2] : Uint16)) "insufficient balance" s₁
  generalize (Damp.require (cmpLe cost (Value.ofExprs [Expr.var 2] : Uint16)) "insufficient balance").run s₁
    = q₂ at hs₂ ⊢
  obtain ⟨u, s₂⟩ := q₂
  simp only at hs₂ ⊢
  have hcost₂ := (hcost.transfer ha₂).mono hs₂.1
  have hB₂ := (hB₁.transfer ha₂).mono hs₂.1
  -- `balance.sub cost`
  refine (Runs.sub_top (hs₂.2.1.trans hg.2.1) hB₂ hcost₂).conseq Iff.rfl fun r e h => ?_
  simp only [Value.Is, Value.toExprs, Expr.evalList, h.eval]; rfl

/-- **`charge`, as a function of its inputs.** The circuit accepts the inputs `[q, pr, bal]`
    (the order's quantity and price, and the balance) exactly when each fits its type and the
    cost `q · pr` is at most the balance, and then outputs the balance minus the cost. -/
theorem charge_run (q pr bal : Fr) :
    charge.circuit.run p [q, pr, bal] [] [] =
      if q.val ≤ 255 ∧ pr.val ≤ 255 ∧ bal.val ≤ 65535 ∧ q.val * pr.val ≤ bal.val then
        some { outputs := [Fr.ofNat (bal.val - q.val * pr.val)], groups := [] }
      else none := by
  have hrh : rangesHold (CircuitFnSpec.ranges (Order → Uint16 → CircuitM Uint16)) [q, pr, bal] =
      decide (q.val ≤ 255 ∧ pr.val ≤ 255 ∧ bal.val ≤ 65535) := by
    rw [charge_ranges]
    simp [rangesHold, uintRange_holds (show (255 : Nat) < 2 ^ 254 by decide),
      uintRange_holds (show (65535 : Nat) < 2 ^ 254 by decide)]
  show (mkCircuit "charge" ["o", "balance"] charge).run p _ _ _ = _
  by_cases hin : q.val ≤ 255 ∧ pr.val ≤ 255 ∧ bal.val ≤ 65535
  · rw [mkCircuit_run_of_Runs _ _ charge (by rw [charge_ranges]; rfl) (by rw [hrh]; simpa using hin)
      (by rw [charge_ranges]; exact charge_runs p q pr bal hin.1 hin.2.1 hin.2.2)]
    simp [hin]
  · rw [mkCircuit_run_reject _ _ charge (by rw [hrh]; simpa using fun _ => hin)]
    split
    · rename_i h; exact absurd ⟨h.1, h.2.1, h.2.2.1⟩ hin
    · rfl

theorem settle_ranges : CircuitFnSpec.ranges (Uint16 → Uint16 → Boolean → CircuitM Uint16) =
    [some (uintRange 65535), some (uintRange 65535), some .bool] := by
  simp [Value.ranges, Value.shape, Shape.ranges_prim, ranges_uint, ranges_bool]

theorem settle_runs (a b : Fr) (u : Bool) (ha : a.val ≤ 65535) (hb : b.val ≤ 65535) :
    Runs p (settle (Value.ofExprs [.var 0]) (Value.ofExprs [.var 1]) (Value.ofExprs [.var 2])) { next := 3 }
      { env := fun v => [a, b, Fr.ofBool u].getD v 0, priv := [], pub := [] } (u = true → b.val ≤ a.val)
      (fun r env => Value.Is p env r [Fr.ofNat (if u then a.val - b.val else a.val)]) := by
  have u65535 : (65535 : Nat) < 2 ^ 254 := by decide
  have hA := arg_uint_means (p := p) (m := 65535) (by decide) (k := 3) (env := fun v => [a, b, Fr.ofBool u].getD v 0)
    (v := 0) (by decide) (by rw [uintRange_holds u65535]; simpa using ha)
  have hB := arg_uint_means (p := p) (m := 65535) (by decide) (k := 3) (env := fun v => [a, b, Fr.ofBool u].getD v 0)
    (v := 1) (by decide) (by rw [uintRange_holds u65535]; simpa using hb)
  have hC := arg_boolean_means (p := p) (k := 3) (env := fun v => [a, b, Fr.ofBool u].getD v 0) (v := 2)
    (by decide) (b := u) rfl
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hA hB
  have hg : GuardIs p { next := 3 } { env := fun v => [a, b, Fr.ofBool u].getD v 0, priv := [], pub := [] } true :=
    fun _ _ => guard_one_is
  refine Runs.conseq (Runs.cond (gb := true) hg hC (Grows.sub _ _) (Grows.pure' _)
    (fun s' st' ctx => Runs.sub ctx.2.2.2.2.2 (ctx.transfer hA) (ctx.transfer hB))
    (fun s' st' ctx => Runs.pure (Q := fun r e => Uint.Means p e r a.val) (ctx.transfer hA))) (by simp)
    fun r e h => ?_
  obtain ⟨x, y, rfl, hx, hy, hc⟩ := h
  have := select_uint_means hc hx hy
  simp only [Bool.true_and] at this
  simp only [Value.Is, Value.toExprs, Expr.evalList, this.eval]
  cases u <;> rfl

/-- **`settle`, as a function of its inputs.** The circuit accepts `[a, b, r]` exactly when the
    amounts fit `Uint16`, `r` is a truth value, and, if it is a refund (`r = 1`), the refund `b`
    does not exceed `a`; it then outputs `a - b` for a refund and `a` otherwise. In particular
    the subtraction in the branch not taken never fails the circuit. -/
theorem settle_run (a b r : Fr) :
    settle.circuit.run p [a, b, r] [] [] =
      if a.val ≤ 65535 ∧ b.val ≤ 65535 ∧ (r = 0 ∨ r = 1) ∧ (r = 1 → b.val ≤ a.val) then
        some { outputs := [Fr.ofNat (if r = 1 then a.val - b.val else a.val)], groups := [] }
      else none := by
  have hrh : rangesHold (CircuitFnSpec.ranges (Uint16 → Uint16 → Boolean → CircuitM Uint16)) [a, b, r] =
      decide (a.val ≤ 65535 ∧ b.val ≤ 65535 ∧ (r = 0 ∨ r = 1)) := by
    rw [settle_ranges]
    simp only [rangesHold, List.zip_cons_cons, List.zip_nil_right, List.all_cons, List.all_nil, Option.all,
      uintRange_holds (show (65535 : Nat) < 2 ^ 254 by decide)]
    simp [Range.holds]
  show (mkCircuit "settle" ["amount", "refund", "isRefund"] settle).run p _ _ _ = _
  by_cases hin : a.val ≤ 65535 ∧ b.val ≤ 65535 ∧ (r = 0 ∨ r = 1)
  · obtain ⟨u, rfl⟩ : ∃ u, r = Fr.ofBool u := by
      rcases hin.2.2 with h | h
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    rw [mkCircuit_run_of_Runs _ _ settle (by rw [settle_ranges]; rfl) (by rw [hrh]; simpa using hin)
      (by rw [settle_ranges]; exact settle_runs p a b u hin.1 hin.2.1)]
    cases u <;> simp [hin, Fr.ofBool, Fr.zero_ne_one, Ne.symm Fr.zero_ne_one]
  · rw [mkCircuit_run_reject _ _ settle (by rw [hrh]; simpa using fun _ => hin)]
    split
    · rename_i h; exact absurd ⟨h.1, h.2.1, h.2.2.1⟩ hin
    · rfl
end Examples.InterfaceMore
