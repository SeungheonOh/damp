/-
More rules of the executor logic `XRuns` (`LedgerLogic.lean`), for what the
token library (`Damp/Lang/Tokens.lean`) and cross-contract calls
(`Damp/Lang/Calls.lean`) build:

* `XRuns.askWitness0`, `XRuns.askWitness0_off`: a witness call whose result
  has no field elements (`createZswapInput`, `createZswapOutput`, any `Unit`
  witness). `Exec.step` treats it apart from the others: under a guard that is
  exactly 1 it asks the oracle, which must answer nothing, and keeps the
  private state it returns; otherwise it does nothing. `XRuns.askWitness`
  needs a positive width and does not cover it.
* `XRuns.ledgerOpG`, `XRuns.ledgerReadG`: a ledger operation under a guard
  meaning `gb`, either value: the two rules of `LedgerLogic.lean` in one.
* `XRuns.when_ledgerOp`: `if% c then op` for a ledger operation `op` that
  reads nothing (`Kernel.claimZswapCoinReceive`, `Kernel.incUnshieldedInputs`
  under their conditions), under a guard meaning `gb`: the operation runs, and
  must succeed, exactly when `gb && cb`.
* `XRuns.val`, `XRuns.seqQ`: conveniences.

None of the earlier rules is changed.
-/
import Damp.Proofs.Interface.LedgerLogic

namespace Damp
open IR

set_option linter.unusedSimpArgs false

variable {ω σ : Type} {p : Zkir.Prims} {O : Exec.Oracles ω σ}

/-! ## Zero-width witnesses -/

theorem askWitness0_run {α : Type} [Value α] (hw0 : Value.width α = 0) (name : String) (args : List Expr)
    (s : Build) :
    ((askWitness name α args).run s).2.next = s.next ∧
      ((askWitness name α args).run s).2.guard = s.guard ∧
      ((askWitness name α args).run s).2.stmts.toList = s.stmts.toList ++ [.witness s.guard name args [] (Value.shape α)] := by
  obtain ⟨-, h2, h3, h4⟩ := askWitness_run name α args s
  have hr : Value.ranges α = [] := by
    have : (Value.ranges α).length = 0 := hw0
    exact List.eq_nil_of_length_eq_zero this
  refine ⟨by rw [h2, hw0]; rfl, h3, ?_⟩
  rw [h4, hw0, hr]; rfl

/-- **A witness call with nothing to read** (`Value.width α = 0`, e.g. `Unit`:
    `createZswapInput`, `createZswapOutput`), under a guard that holds: the
    oracle is asked with the arguments' values; the call completes exactly when
    it answers with no field elements, and then the private state and the ledger
    state are the ones it returned; the environment is unchanged. -/
theorem XRuns.askWitness0 {α : Type} [Value α] (hw0 : Value.width α = 0) (name : String) {args : List Expr}
    {argVals : List Fr} {s : Build} {st : Exec.State ω σ}
    (hg : GuardIs p s st.runState true) (hargs : Expr.evalList p st.env args = some argVals) :
    XRuns p O (Damp.askWitness name α args) s st
      (∃ w' l', O.witness name argVals st.private_ st.ledger = some ([], w', l'))
      (fun _ _ w l => O.witness name argVals st.private_ st.ledger = some ([], w, l)) := by
  obtain ⟨h2, h3, h4⟩ := askWitness0_run hw0 name args s
  have hstep : Exec.steps p O [.witness s.guard name args [] (Value.shape α)] st =
      (O.witness name argVals st.private_ st.ledger).bind fun r =>
        if r.1.isEmpty then some { st with private_ := r.2.1, ledger := r.2.2 } else none := by
    rw [steps_single]
    simp only [Exec.step, guard_eval hg, List.isEmpty_nil, ↓reduceIte, Option.bind_eq_bind, Option.bind_some,
      show Fr.ofBool true = 1 from rfl, hargs]
    cases O.witness name argVals st.private_ st.ledger with
    | none => rfl
    | some r => obtain ⟨vals, w', l'⟩ := r; rfl
  refine ⟨by rw [h2]; exact Nat.le_refl _, h3, _, h4, ?_, ?_⟩
  · rw [hstep]
    cases hw : O.witness name argVals st.private_ st.ledger with
    | none => simp
    | some r =>
      obtain ⟨vals, w', l'⟩ := r
      cases vals with
      | nil => simp
      | cons v vs => simp
  · intro st' h'
    rw [hstep] at h'
    cases hw : O.witness name argVals st.private_ st.ledger with
    | none => rw [hw] at h'; simp at h'
    | some r =>
      obtain ⟨vals, w', l'⟩ := r
      rw [hw] at h'
      cases vals with
      | cons v vs => simp at h'
      | nil =>
        simp only [Option.bind_some, List.isEmpty_nil, ↓reduceIte, Option.some.injEq] at h'
        subst h'
        exact ⟨Agree.refl _ _, Stable.const rfl⟩

/-- A witness call with nothing to read, under a guard that is off: nothing is
    asked and nothing changes. -/
theorem XRuns.askWitness0_off {α : Type} [Value α] (hw0 : Value.width α = 0) (name : String) {args : List Expr}
    {s : Build} {st : Exec.State ω σ} (hg : GuardIs p s st.runState false) :
    XRuns p O (Damp.askWitness name α args) s st True (fun _ _ w l => w = st.private_ ∧ l = st.ledger) := by
  obtain ⟨h2, h3, h4⟩ := askWitness0_run hw0 name args s
  have hstep : Exec.steps p O [.witness s.guard name args [] (Value.shape α)] st = some st := by
    rw [steps_single]
    simp only [Exec.step, guard_eval hg, List.isEmpty_nil, ↓reduceIte, Option.bind_eq_bind, Option.bind_some,
      show Fr.ofBool false = 0 from rfl, Fr.zero_ne_one, ite_false]
    rfl
  refine ⟨by rw [h2]; exact Nat.le_refl _, h3, _, h4, by rw [hstep]; simp, fun st' h' => ?_⟩
  rw [hstep, Option.some.injEq] at h'
  subst h'
  exact ⟨Agree.refl _ _, Stable.const ⟨rfl, rfl⟩⟩

/-- Both cases in one: under a guard meaning `gb`, the oracle is asked exactly
    when `gb`. -/
theorem XRuns.askWitness0G {α : Type} [Value α] (hw0 : Value.width α = 0) (name : String) {args : List Expr}
    {argVals : List Fr} {s : Build} {st : Exec.State ω σ} {gb : Bool}
    (hg : GuardIs p s st.runState gb) (hargs : Expr.evalList p st.env args = some argVals) :
    XRuns p O (Damp.askWitness name α args) s st
      (gb = true → ∃ w' l', O.witness name argVals st.private_ st.ledger = some ([], w', l'))
      (fun _ _ w l => if gb then O.witness name argVals st.private_ st.ledger = some ([], w, l)
        else w = st.private_ ∧ l = st.ledger) := by
  cases gb with
  | true =>
    exact (XRuns.askWitness0 hw0 name hg hargs).conseq (by simp) fun _ _ _ _ h => by simpa using h
  | false =>
    exact (XRuns.askWitness0_off hw0 name hg).conseq (by simp) fun _ _ _ _ h => by simpa using h

/-! ### Witnesses that cannot touch the ledger

The rules above for oracles whose witnesses are `liftWitness w`: they see only
the private state and hand the ledger back unchanged. These are the rules the
contract theorems were first proved with; they hold, as stated, of isolated
witnesses (`Exec.Isolated`: `ownPublicKey`, `createZswapInput`, calls), and
of any witness in an executor whose witness oracle is `liftWitness w`. -/

theorem liftWitness_eq_some {w : String → List Fr → ω → Option (List Fr × ω)} {n : String} {a : List Fr}
    {x : ω} {l l' : σ} {r : List Fr} {x' : ω} :
    Exec.liftWitness w n a x l = some (r, x', l') ↔ w n a x = some (r, x') ∧ l' = l := by
  simp only [Exec.liftWitness, Option.map_eq_some_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨r0, x0⟩, h, rfl, rfl, rfl⟩; exact ⟨h, rfl⟩
  · rintro ⟨h, rfl⟩; exact ⟨(r, x'), h, rfl, rfl, rfl⟩

theorem XRuns.askWitness0_iso {α : Type} [Value α] {w : String → List Fr → ω → Option (List Fr × ω)}
    (hO : O.witness = Exec.liftWitness w) (hw0 : Value.width α = 0) (name : String) {args : List Expr}
    {argVals : List Fr} {s : Build} {st : Exec.State ω σ}
    (hg : GuardIs p s st.runState true) (hargs : Expr.evalList p st.env args = some argVals) :
    XRuns p O (Damp.askWitness name α args) s st
      (∃ w', w name argVals st.private_ = some ([], w'))
      (fun _ _ w' l => l = st.ledger ∧ w name argVals st.private_ = some ([], w')) :=
  (XRuns.askWitness0 hw0 name hg hargs).conseq
    (by rw [hO]; simp only [liftWitness_eq_some]; exact ⟨fun ⟨w', _, h, _⟩ => ⟨w', h⟩, fun ⟨w', h⟩ => ⟨w', _, h, rfl⟩⟩)
    (fun _ _ _ _ h => by rw [hO, liftWitness_eq_some] at h; exact ⟨h.2, h.1⟩)

theorem XRuns.askWitness0G_iso {α : Type} [Value α] {w : String → List Fr → ω → Option (List Fr × ω)}
    (hO : O.witness = Exec.liftWitness w) (hw0 : Value.width α = 0) (name : String) {args : List Expr}
    {argVals : List Fr} {s : Build} {st : Exec.State ω σ} {gb : Bool}
    (hg : GuardIs p s st.runState gb) (hargs : Expr.evalList p st.env args = some argVals) :
    XRuns p O (Damp.askWitness name α args) s st
      (gb = true → ∃ w', w name argVals st.private_ = some ([], w'))
      (fun _ _ w' l => l = st.ledger ∧
        (if gb then w name argVals st.private_ = some ([], w') else w' = st.private_)) := by
  cases gb with
  | true =>
    exact (XRuns.askWitness0_iso hO hw0 name hg hargs).conseq (by simp) fun _ _ _ _ h => ⟨h.1, by simpa using h.2⟩
  | false =>
    exact (XRuns.askWitness0_off hw0 name hg).conseq (by simp) fun _ _ _ _ h => ⟨h.2, by simpa using h.1⟩

theorem XRuns.askWitness_iso {α : Type} [Value α] {w : String → List Fr → ω → Option (List Fr × ω)}
    (hO : O.witness = Exec.liftWitness w) (hrt : Value.RoundTrip α) (name : String) {args : List Expr}
    {argVals : List Fr} {s : Build} {st : Exec.State ω σ} (hw : 0 < Value.width α)
    (hg : GuardIs p s st.runState true) (hargs : Expr.evalList p st.env args = some argVals) :
    XRuns p O (Damp.askWitness name α args) s st
      (∃ ys w', w name argVals st.private_ = some (ys, w') ∧ ys.length = Value.width α ∧
        rangesHold (Value.ranges α) ys = true)
      (fun r e w' l => l = st.ledger ∧ ∃ ys, w name argVals st.private_ = some (ys, w') ∧
        rangesHold (Value.ranges α) ys = true ∧ Value.Is p e r ys) :=
  (XRuns.askWitness hrt name hw hg hargs).conseq
    (by
      rw [hO]; simp only [liftWitness_eq_some]
      exact ⟨fun ⟨ys, w', _, ⟨h, _⟩, h2⟩ => ⟨ys, w', h, h2⟩, fun ⟨ys, w', h, h2⟩ => ⟨ys, w', _, ⟨h, rfl⟩, h2⟩⟩)
    (fun _ _ _ _ ⟨ys, h, h2⟩ => by rw [hO, liftWitness_eq_some] at h; exact ⟨h.2, ys, h.1, h2⟩)

theorem Grows.askWitness0 (name : String) (α : Type) [Value α] (args : List Expr) :
    Grows (Damp.askWitness name α args) := Grows.askWitness name α args

/-! ## Ledger operations under a guard of either value -/

/-- **A ledger operation that reads nothing, under a guard meaning `gb`**: with
    the guard on, it completes exactly when the answer `res` reads nothing, and
    leaves the ledger the answer gives; with it off, nothing is asked and the
    ledger is unchanged. -/
theorem XRuns.ledgerOpG {ops : List (Impact.Op Expr)} {s : Build} {st : Exec.State ω σ} {gb : Bool}
    {res : Option (List Fr × σ)} (hops : ops ≠ []) (hg : GuardIs p s st.runState gb)
    (hreq : ∀ e, Agree s.next st.env e → ∃ req, Exec.request p e ops = some req ∧ O.ledger req st.ledger = res) :
    XRuns p O (Damp.ledgerOp [] ops) s st (gb = true → ∃ l, res = some ([], l))
      (fun _ _ w l => w = st.private_ ∧ (if gb then res = some ([], l) else l = st.ledger)) := by
  cases gb with
  | true => exact (XRuns.ledgerOp hops hg hreq).conseq (by simp) fun _ _ _ _ h => ⟨h.1, by simpa using h.2⟩
  | false =>
    obtain ⟨req, hr, -⟩ := hreq st.env (Agree.refl _ _)
    exact (XRuns.ledgerOp_off hops hg ⟨req, hr⟩).conseq (by simp) fun _ _ _ _ h => ⟨h.1, by simpa using h.2⟩

/-- **A reading operation under a guard meaning `gb`**: on, as
    `XRuns.ledgerRead`; off, the result is zeros and the ledger is unchanged. -/
theorem XRuns.ledgerReadG {α : Type} [Value α] (hrt : Value.RoundTrip α) {mk : List Expr → List (Impact.Op Expr)}
    (hmk : ReadOps mk) {s : Build} {st : Exec.State ω σ} {gb : Bool} {res : Option (List Fr × σ)}
    (hw : 0 < Value.width α) (hg : GuardIs p s st.runState gb)
    (hreq : ∀ e, Agree s.next st.env e →
      ∃ req, Exec.request p e (mk (Ledger.readVars α)) = some req ∧ O.ledger req st.ledger = res) :
    XRuns p O (Damp.ledgerRead α mk) s st (gb = true → ∃ ys l, res = some (ys, l) ∧ ys.length = Value.width α)
      (fun r e w l => w = st.private_ ∧
        (if gb then ∃ ys, res = some (ys, l) ∧ Value.Is p e r ys
         else l = st.ledger ∧ Value.Is p e r (List.replicate (Value.width α) 0))) := by
  cases gb with
  | true => exact (XRuns.ledgerRead hrt hmk hw hg hreq).conseq (by simp) fun _ _ _ _ h => ⟨h.1, by simpa using h.2⟩
  | false =>
    exact (XRuns.ledgerRead_off hrt hmk hw hg (fun e he => (hreq e he).imp fun _ h => h.1)).conseq (by simp)
      fun _ _ _ _ h => ⟨h.1, by simpa using h.2⟩

/-- **`if% c then op`, `op` a ledger operation that reads nothing**, under a
    guard meaning `gb`, `c` meaning `cb`: the operation runs exactly when
    `gb && cb`; then the call completes exactly when the answer `res` reads
    nothing, and leaves the ledger it gives; otherwise nothing changes. -/
theorem XRuns.when_ledgerOp {c : Boolean} {ops : List (Impact.Op Expr)} {s : Build} {st : Exec.State ω σ}
    {gb cb : Bool} {res : Option (List Fr × σ)} (hops : ops ≠ []) (hg : GuardIs p s st.runState gb)
    (hc : Stable s.next st.env (fun e => Boolean.Is p e c cb))
    (hreq : ∀ e, Agree s.next st.env e → ∃ req, Exec.request p e ops = some req ∧ O.ledger req st.ledger = res) :
    XRuns p O (Damp.when_ c (Damp.ledgerOp [] ops)) s st ((gb && cb) = true → ∃ l, res = some ([], l))
      (fun _ _ w l => w = st.private_ ∧ (if gb && cb then res = some ([], l) else l = st.ledger)) :=
  XRuns.when_ hg hc (Grows.ledgerOp _ _) fun s' st' ctx =>
    (XRuns.ledgerOpG (res := res) hops ctx.2.2.2.2 (fun e he => by
      rw [ctx.2.2.2.1]; exact hreq e (ctx.2.1.trans (he.mono ctx.1)))).conseq Iff.rfl
      fun _ _ w l h => ⟨h.1.trans ctx.2.2.1, by rw [← ctx.2.2.2.1]; exact h.2⟩

/-- `XRuns.ledgerOpG` for an operation `m` given by name (`Kernel.claimZswapCoinSpend cm`, …),
    with its answer in the form the specifications of `Damp/Proofs/Ledger/` give it
    (`(emitted m).bind (Exec.request p e)`). -/
theorem XRuns.ledgerOpE {m : CircuitM Unit} {ops : List (Impact.Op Expr)} (hm : m = Damp.ledgerOp [] ops)
    {s : Build} {st : Exec.State ω σ} {gb : Bool}
    {res : Option (List Fr × σ)} (hops : ops ≠ []) (hg : GuardIs p s st.runState gb)
    (hreq : ∀ e, Agree s.next st.env e →
      ∃ req, (Ledger.emitted m).bind (Exec.request p e) = some req ∧ O.ledger req st.ledger = res) :
    XRuns p O m s st (gb = true → ∃ l, res = some ([], l))
      (fun _ _ w l => w = st.private_ ∧ (if gb then res = some ([], l) else l = st.ledger)) := by
  subst hm
  exact XRuns.ledgerOpG hops hg hreq

/-- `XRuns.when_ledgerOp` for an operation given by name. -/
theorem XRuns.when_ledgerOpE {c : Boolean} {m : CircuitM Unit} {ops : List (Impact.Op Expr)}
    (hm : m = Damp.ledgerOp [] ops) {s : Build} {st : Exec.State ω σ}
    {gb cb : Bool} {res : Option (List Fr × σ)} (hops : ops ≠ []) (hg : GuardIs p s st.runState gb)
    (hc : Stable s.next st.env (fun e => Boolean.Is p e c cb))
    (hreq : ∀ e, Agree s.next st.env e →
      ∃ req, (Ledger.emitted m).bind (Exec.request p e) = some req ∧ O.ledger req st.ledger = res) :
    XRuns p O (Damp.when_ c m) s st ((gb && cb) = true → ∃ l, res = some ([], l))
      (fun _ _ w l => w = st.private_ ∧ (if gb && cb then res = some ([], l) else l = st.ledger)) := by
  subst hm
  exact XRuns.when_ledgerOp hops hg hc hreq

/-- What a guarded operation answering `if P then some ([], σ₁) else none` leaves. -/
theorem guarded_step {gb : Bool} {P : Prop} [Decidable P] {σ₀ σ₁ l : σ}
    (h : if gb then (if P then some (([] : List Fr), σ₁) else none) = some ([], l) else l = σ₀) :
    (gb = true → P) ∧ l = (if gb then σ₁ else σ₀) := by
  cases gb with
  | true =>
    simp only [ite_true] at h
    by_cases hP : P
    · simp only [hP, ite_true, Option.some.injEq, Prod.mk.injEq, true_and] at h; exact ⟨fun _ => hP, by simp [h]⟩
    · simp [hP] at h
  | false => exact ⟨(fun h => nomatch h), by simpa using h⟩

/-- The same for an operation that always succeeds. -/
theorem guarded_step' {gb : Bool} {σ₀ σ₁ l : σ}
    (h : if gb then some (([] : List Fr), σ₁) = some ([], l) else l = σ₀) : l = (if gb then σ₁ else σ₀) := by
  cases gb with
  | true => simp only [ite_true, Option.some.injEq, Prod.mk.injEq, true_and] at h ⊢; exact h.symm
  | false => simpa using h

/-- **A guarded ledger operation that reads nothing and either fails or leaves
    `σ₁`** (`if P then some ([], σ₁) else none`, the form of the additions to
    the effects): under a guard meaning `gb` it completes exactly when
    `gb → P`, and leaves `σ₁` if `gb`, the ledger unchanged otherwise. -/
theorem XRuns.condOp {m : CircuitM Unit} {ops : List (Impact.Op Expr)} (hm : m = Damp.ledgerOp [] ops)
    {s : Build} {st : Exec.State ω σ} {gb : Bool} {P : Prop} [Decidable P] {σ₁ : σ}
    (hops : ops ≠ []) (hg : GuardIs p s st.runState gb)
    (hreq : ∀ e, Agree s.next st.env e →
      ∃ req, (Ledger.emitted m).bind (Exec.request p e) = some req ∧
        O.ledger req st.ledger = if P then some ([], σ₁) else none) :
    XRuns p O m s st (gb = true → P)
      (fun _ _ w l => w = st.private_ ∧ (gb = true → P) ∧ l = if gb then σ₁ else st.ledger) :=
  (XRuns.ledgerOpE hm hops hg hreq).conseq
    (by
      cases gb with
      | false => simp
      | true => by_cases hP : P <;> simp [hP])
    fun _ _ _ _ h => ⟨h.1, guarded_step h.2⟩

/-- An operation that always succeeds, leaving `σ₁`. -/
theorem XRuns.someOp {m : CircuitM Unit} {ops : List (Impact.Op Expr)} (hm : m = Damp.ledgerOp [] ops)
    {s : Build} {st : Exec.State ω σ} {gb : Bool} {σ₁ : σ}
    (hops : ops ≠ []) (hg : GuardIs p s st.runState gb)
    (hreq : ∀ e, Agree s.next st.env e →
      ∃ req, (Ledger.emitted m).bind (Exec.request p e) = some req ∧ O.ledger req st.ledger = some ([], σ₁)) :
    XRuns p O m s st True (fun _ _ w l => w = st.private_ ∧ l = if gb then σ₁ else st.ledger) :=
  (XRuns.ledgerOpE hm hops hg hreq).conseq (by simp) fun _ _ _ _ h => ⟨h.1, guarded_step' h.2⟩

/-- `if% c then op` for such an operation. -/
theorem XRuns.when_condOp {c : Boolean} {m : CircuitM Unit} {ops : List (Impact.Op Expr)}
    (hm : m = Damp.ledgerOp [] ops) {s : Build} {st : Exec.State ω σ}
    {gb cb : Bool} {P : Prop} [Decidable P] {σ₁ : σ} (hops : ops ≠ []) (hg : GuardIs p s st.runState gb)
    (hc : Stable s.next st.env (fun e => Boolean.Is p e c cb))
    (hreq : ∀ e, Agree s.next st.env e →
      ∃ req, (Ledger.emitted m).bind (Exec.request p e) = some req ∧
        O.ledger req st.ledger = if P then some ([], σ₁) else none) :
    XRuns p O (Damp.when_ c m) s st ((gb && cb) = true → P)
      (fun _ _ w l => w = st.private_ ∧ ((gb && cb) = true → P) ∧ l = if gb && cb then σ₁ else st.ledger) :=
  (XRuns.when_ledgerOpE hm hops hg hc hreq).conseq
    (by
      cases gb && cb with
      | false => simp
      | true => by_cases hP : P <;> simp [hP])
    fun _ _ _ _ h => ⟨h.1, guarded_step h.2⟩

/-- `if% c then op` for an operation that always succeeds. -/
theorem XRuns.when_someOp {c : Boolean} {m : CircuitM Unit} {ops : List (Impact.Op Expr)}
    (hm : m = Damp.ledgerOp [] ops) {s : Build} {st : Exec.State ω σ}
    {gb cb : Bool} {σ₁ : σ} (hops : ops ≠ []) (hg : GuardIs p s st.runState gb)
    (hc : Stable s.next st.env (fun e => Boolean.Is p e c cb))
    (hreq : ∀ e, Agree s.next st.env e →
      ∃ req, (Ledger.emitted m).bind (Exec.request p e) = some req ∧ O.ledger req st.ledger = some ([], σ₁)) :
    XRuns p O (Damp.when_ c m) s st True
      (fun _ _ w l => w = st.private_ ∧ l = if gb && cb then σ₁ else st.ledger) :=
  (XRuns.when_ledgerOpE hm hops hg hc hreq).conseq (by simp) fun _ _ _ _ h => ⟨h.1, guarded_step' h.2⟩

/-- **A guarded ledger operation that reads nothing and whose answer is
    `o.map fun q => ([], f q)`** (the form of the coin-storing operations, `o`
    the qualified coin): under a guard meaning `gb` it completes exactly when
    `gb → o.isSome`, and leaves `f q` for the `q` in `o` if `gb`, the ledger
    unchanged otherwise. -/
theorem XRuns.mapOp {m : CircuitM Unit} {ops : List (Impact.Op Expr)} (hm : m = Damp.ledgerOp [] ops)
    {s : Build} {st : Exec.State ω σ} {gb : Bool} {β : Type} {o : Option β} {f : β → σ}
    (hops : ops ≠ []) (hg : GuardIs p s st.runState gb)
    (hreq : ∀ e, Agree s.next st.env e →
      ∃ req, (Ledger.emitted m).bind (Exec.request p e) = some req ∧
        O.ledger req st.ledger = o.map fun q => ([], f q)) :
    XRuns p O m s st (gb = true → o.isSome = true)
      (fun _ _ w l => w = st.private_ ∧ (if gb then ∃ q, o = some q ∧ l = f q else l = st.ledger)) :=
  (XRuns.ledgerOpE hm hops hg hreq).conseq
    (by cases o <;> simp)
    fun _ _ _ l h => ⟨h.1, by
      cases gb with
      | false => simpa using h.2
      | true =>
        simp only [ite_true] at h ⊢
        cases o with
        | none => simp at h
        | some q => simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and] at h; exact ⟨q, rfl, h.2.symm⟩⟩

/-! ## Conveniences -/

theorem Quiet.castTo {m : Nat} (a : Uint m) (k : Nat) : Quiet (a.castTo k) := by
  unfold Uint.castTo
  refine Quiet.bind (Quiet.of_errors (checkUintBounds_run _)) fun _ => ?_
  split
  · exact Quiet.pure' _
  · exact Quiet.bind (Quiet.guarded _) fun _ => Quiet.bind (by
      unfold constrainTy; split
      · exact Quiet.emit rfl
      · exact Quiet.pure' _) fun _ => Quiet.pure' _

/-- `val x` (`const y := x`), as an `XRuns`: the result means what `x` meant,
    nothing else changes. -/
theorem XRuns.val {α : Type} [Value α] (hrt : Value.RoundTrip α) {x : α} {xs : List Fr} (hint : String)
    {s : Build} {st : Exec.State ω σ} (hlen : (Value.toExprs x).length = Value.width α)
    (hx : Stable s.next st.env (fun e => Value.Is p e x xs)) :
    XRuns p O (Damp.val x hint) s st True (fun r e w l => Value.Is p e r xs ∧ w = st.private_ ∧ l = st.ledger) :=
  XRuns.lift (Runs.val (st := st.runState) hrt hint hlen hx) (Quiet.val _ _)

/-! ## Values read off a list of expressions -/

/-- `r` is read off a list of expressions of its type's width: true of every
    `val`, ledger read and witness result. -/
def Value.Shaped {α : Type} [Value α] (r : α) : Prop := ∃ es : List Expr, es.length = Value.width α ∧ r = Value.ofExprs es

theorem val_run_fst {α : Type} [Value α] (x : α) (hint : String) (s : Build) :
    ((Damp.val x hint).run s).1 = Value.ofExprs (argVars s.next (Value.toExprs x).length) := by
  obtain ⟨r1, -, -, -⟩ := valLoop_run hint (Value.toExprs x) s
  show ((valLoop hint (Value.toExprs x) >>= fun vs => Pure.pure (Value.ofExprs vs)).run s).1 = _
  rw [CircuitM.bind_run]; rw [← r1]; rfl

theorem val_shaped {α : Type} [Value α] (x : α) (hint : String) (s : Build)
    (hlen : (Value.toExprs x).length = Value.width α) : Value.Shaped ((Damp.val x hint).run s).1 :=
  ⟨_, by simp [argVars, hlen], val_run_fst x hint s⟩

theorem ledgerRead_shaped (α : Type) [Value α] (mk : List Expr → List (Impact.Op Expr)) (s : Build) :
    Value.Shaped ((ledgerRead α mk).run s).1 := by
  rw [ledgerRead_run]; exact ⟨_, by simp [readVarsAt], rfl⟩

theorem askWitness_shaped (name : String) (α : Type) [Value α] (args : List Expr) (s : Build) :
    Value.Shaped ((askWitness name α args).run s).1 := by
  rw [(askWitness_run name α args s).1]; exact ⟨_, by simp, rfl⟩

/-- A fact about the result a computation builds can be added to its description. -/
theorem XRuns.addResult {α : Type} {m : CircuitM α} {s : Build} {st : Exec.State ω σ} {ok : Prop}
    {Q : α → Env → ω → σ → Prop} (h : XRuns p O m s st ok Q) {P : α → Prop} (hP : P (m.run s).1) :
    XRuns p O m s st ok (fun a e w l => Q a e w l ∧ P a) := by
  obtain ⟨hn, hg, T, hT, hs, hst⟩ := h
  exact ⟨hn, hg, T, hT, hs, fun st' h' => (hst st' h').imp_right fun hQ => hQ.imp fun e hq => ⟨hq, hP⟩⟩

/-- A guard meaning `gb` keeps meaning it in a later state. -/
theorem GuardIs.later {g : Bool} {s s₁ : Build} {st st₁ : Exec.State ω σ}
    (hgd : GuardIs p s st.runState g) (ha : Agree s.next st.env st₁.env) (hn : s.next ≤ s₁.next)
    (hg : s₁.guard = s.guard) : GuardIs p s₁ st₁.runState g := by
  intro e he; rw [hg]; exact (hgd.transfer ha).mono hn e he

/-- A stable fact keeps holding in a later state. -/
theorem Stable.later {P : Env → Prop} {k k₁ : Nat} {env env₁ : Env} (h : Stable k env P) (ha : Agree k env env₁)
    (hn : k ≤ k₁) : Stable k₁ env₁ P := (h.transfer ha).mono hn

end Damp
