/-
What a witness can touch, as hypotheses on the witness oracle.

`Exec.Oracles.witness` (`Damp/Executor/Spec.lean`) is given the ledger state
and returns one, so the executor's definition does not limit what a witness
does to the ledger. What the runtime's witnesses actually do is established in
docs/ledger-model.md ("What a witness can touch", backed by
`test/witness-effects.sh`) and stated here, by the witness's name, which is how
the executor (`oracles` in `executor/src/executor.mjs`) dispatches:

* `ownPublicKey`, `createZswapInput` (the runtime's built-ins), and every
  cross-contract call `call:…`: **isolated** (`Isolated`): the answer and the
  private state afterwards do not depend on the ledger state, which comes back
  unchanged. The built-ins work on the call's Zswap local state; a call runs
  another contract against that contract's own state and the caller's query
  context is restored (the call assumption, `CallIsolated`, tested by
  `test/calls-isolation.sh`). Both are part of `ω`, not of the ledger state.
* `createZswapOutput`: **writes call-context slot 1** (`CtxSlotWriter 1`):
  the runtime inserts the coin's commitment into the query context's
  commitment indices (`QueryContext.insertCommitment`), which the VM sees as
  slot 1 of the call context; nothing else in the ledger state changes, and
  what it does depends on the call context only (and its arguments and the
  Zswap local state, in `ω`).
* every other name, a user's witness: **reads the ledger**
  (`ReadsLedger`): the runtime hands it `WitnessContext { ledger,
  privateState, contractAddress }`, the contract's current state and the
  contract's address (slot 0 of the call context); it returns a new private
  state and a value, and cannot change the ledger state. Its answer may depend
  on the contract state and the call context; not on the effects.

`WitnessesOK W` is the conjunction, name by name. The ledger passes are proved
for every witness oracle that satisfies it (`Pass.SoundLedger`,
`Damp/Proofs/Optimize/LedgerSound.lean`), and each pass's barrier is exactly
what these footprints require (`Damp/Optimize/LedgerFrame.lean`).
-/
import Damp.Ledger.Query

namespace Damp.Exec
open Damp.IR

/-- How the executor treats a witness, decided by its name. -/
inductive WitnessClass where
  /-- Neither sees nor changes the ledger state. -/
  | isolated
  /-- `createZswapOutput`: changes call-context slot 1, sees only the call context. -/
  | zswapOutput
  /-- A user's witness: sees the contract state and the call context, changes no ledger state. -/
  | user
  deriving DecidableEq, Repr

/-- Whether a witness name is that of a cross-contract call (`callWitnessName`). -/
def isCallName (n : String) : Bool := n.startsWith "call:"

/-- The class of a witness, as the executor dispatches on its name
    (`executor/src/executor.mjs`: the built-ins `BUILTIN_WITNESSES` first,
    then the calls `CALL_PREFIX`, then the user's own). -/
def witnessClass (name : String) : WitnessClass :=
  if name == "createZswapOutput" then .zswapOutput
  else if name == "ownPublicKey" || name == "createZswapInput" || isCallName name then .isolated
  else .user

variable {ω σ : Type}

/-- **Isolated**: the witness `n` neither sees the ledger state nor changes it. -/
def Isolated (W : WitnessOracle ω σ) (n : String) : Prop :=
  ∃ g : List Fr → ω → Option (List Fr × ω), ∀ args x l, W n args x l = (g args x).map fun (r, x') => (r, x', l)

/-- **Keeps the ledger**: the witness `n` may see the ledger state but hands it back unchanged. -/
def KeepsLedger (W : WitnessOracle ω σ) (n : String) : Prop :=
  ∀ args x l r x' l', W n args x l = some (r, x', l') → l' = l

/-- **The call assumption**: every cross-contract call is isolated from the
    caller's ledger state. A callee runs against its own state and neither
    reads nor writes the caller's (contract state, effects, call context). -/
def CallIsolated (W : WitnessOracle ω σ) : Prop := ∀ n, isCallName n = true → Isolated W n

theorem Isolated.keepsLedger {W : WitnessOracle ω σ} {n : String} (h : Isolated W n) : KeepsLedger W n := by
  intro args x l r x' l' hw
  obtain ⟨g, hg⟩ := h
  rw [hg] at hw
  cases hgx : g args x with
  | none => simp [hgx] at hw
  | some y => simp [hgx] at hw; exact hw.2.2.symm

theorem isolated_lift (w : String → List Fr → ω → Option (List Fr × ω)) (n : String) :
    Isolated (liftWitness (σ := σ) w) n := ⟨w n, fun _ _ _ => rfl⟩

end Damp.Exec

namespace Damp.Ledger
open Damp.IR Damp.Exec

/-- Two call contexts that are equal, or arrays of the same length agreeing everywhere but at slot `k`. -/
def CtxAgreeExcept (k : Nat) (c c' : SV) : Prop :=
  c' = c ∨ ∃ cs cs', c = .array cs ∧ c' = .array cs' ∧ cs.length = cs'.length ∧ ∀ i, i ≠ k → cs[i]? = cs'[i]?

variable {ω : Type}

/-- **Writes call-context slot `k`**: what the witness `n` answers, the private
    state afterwards and the new call context depend on its arguments, the
    private state and the call context only; the new ledger state is the old
    one with that call context, which agrees with the old one everywhere but at
    slot `k`. The contract state and the effects are unchanged. -/
def CtxSlotWriter (k : Nat) (W : WitnessOracle ω LedgerState) (n : String) : Prop :=
  ∃ g : List Fr → ω → SV → Option (List Fr × ω × SV),
    (∀ args x l, W n args x l = (g args x l.context).map fun (r, x', c) => (r, x', { l with context := c })) ∧
    ∀ args x c r x' c', g args x c = some (r, x', c') → CtxAgreeExcept k c c'

/-- **Reads the ledger**: the witness `n` may look at the contract state and the
    call context (not the effects), and hands the ledger state back unchanged. -/
def ReadsLedger (W : WitnessOracle ω LedgerState) (n : String) : Prop :=
  ∃ g : List Fr → ω → SV → SV → Option (List Fr × ω),
    ∀ args x l, W n args x l = (g args x l.context l.state).map fun (r, x') => (r, x', l)

/-- The footprint each class of witness is allowed. -/
def WitnessFootprint : WitnessClass → WitnessOracle ω LedgerState → String → Prop
  | .isolated => Isolated
  | .zswapOutput => CtxSlotWriter 1
  | .user => ReadsLedger

/-- **The witnesses do what the runtime's do** (docs/ledger-model.md, "What a
    witness can touch"): every witness stays within the footprint of its
    class. This is the only hypothesis `Pass.SoundLedger` makes about them. -/
def WitnessesOK (W : WitnessOracle ω LedgerState) : Prop := ∀ n, WitnessFootprint (witnessClass n) W n

theorem ReadsLedger.keepsLedger {W : WitnessOracle ω LedgerState} {n : String} (h : ReadsLedger W n) :
    KeepsLedger W n := by
  intro args x l r x' l' hw
  obtain ⟨g, hg⟩ := h
  rw [hg] at hw
  cases hgx : g args x l.context l.state with
  | none => simp [hgx] at hw
  | some y => simp [hgx] at hw; exact hw.2.2.symm

theorem WitnessesOK.isolated {W : WitnessOracle ω LedgerState} (h : WitnessesOK W) {n : String}
    (hn : witnessClass n = .isolated) : Isolated W n := by
  have := h n; rw [hn] at this; exact this

theorem WitnessesOK.zswapOutput {W : WitnessOracle ω LedgerState} (h : WitnessesOK W) {n : String}
    (hn : witnessClass n = .zswapOutput) : CtxSlotWriter 1 W n := by
  have := h n; rw [hn] at this; exact this

theorem WitnessesOK.user {W : WitnessOracle ω LedgerState} (h : WitnessesOK W) {n : String}
    (hn : witnessClass n = .user) : ReadsLedger W n := by
  have := h n; rw [hn] at this; exact this

/-- Every witness but `createZswapOutput` hands the ledger state back unchanged. -/
theorem WitnessesOK.keepsLedger {W : WitnessOracle ω LedgerState} (h : WitnessesOK W) {n : String}
    (hn : witnessClass n ≠ .zswapOutput) : KeepsLedger W n := by
  cases hc : witnessClass n with
  | isolated => exact (h.isolated hc).keepsLedger
  | zswapOutput => exact absurd hc hn
  | user => exact (h.user hc).keepsLedger

/-- The calls are isolated. -/
theorem WitnessesOK.callIsolated {W : WitnessOracle ω LedgerState} (h : WitnessesOK W) : CallIsolated W := by
  intro n hn
  apply h.isolated
  unfold witnessClass
  have : (n == "createZswapOutput") = false := by
    cases h' : (n == "createZswapOutput") with
    | false => rfl
    | true => rw [beq_iff_eq.mp h'] at hn; simp [isCallName] at hn
  simp [this, hn]

/-- Witnesses that see only the private state (the old interface) do what the runtime's do. -/
theorem witnessesOK_lift (w : String → List Fr → ω → Option (List Fr × ω)) :
    WitnessesOK (liftWitness (σ := LedgerState) w) := by
  intro n
  cases hc : witnessClass n with
  | isolated => exact isolated_lift w n
  | zswapOutput =>
    refine ⟨fun args x c => (w n args x).map fun (r, x') => (r, x', c), fun _ _ _ => ?_, ?_⟩
    · simp only [liftWitness]; cases w n _ _ <;> rfl
    · intro args x c r x' c' hg
      simp only [Option.map_eq_some_iff] at hg
      obtain ⟨⟨r0, x0⟩, -, he⟩ := hg
      simp only [Prod.mk.injEq] at he
      obtain ⟨-, -, rfl⟩ := he
      exact Or.inl rfl
  | user => exact ⟨fun args x _ _ => w n args x, fun _ _ _ => rfl⟩

end Damp.Ledger
