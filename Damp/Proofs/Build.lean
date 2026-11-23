/-
What a successful build guarantees, stated about the function the build runs.

`Contract.build` (`Damp/Compile/Build.lean`) is an `IO` action that does
nothing but run `Contract.buildCore`, write the files it returns
(`Contract.writeFiles`: `zkir/<name>.zkir` is `src.toJson.pretty ++ "\n"` for
each emitted `src` that needs a proof, `contract.json` is
`Export.contract shipped`) and, when asked, run Midnight's key generator.
`buildCore` is a pure function: the disclosure check on every circuit, the
optimization the flags select, the ledger check on every shipped circuit,
`Contract.check`, and `Emit.circuit` on every shipped circuit, failing on the
first error.

`build_correct` bundles, for every circuit of the contract, everything proved
about the ZKIR shipped for it, at every optimization level, with and without
`--ledger-opt`. What does not depend on how the shipped circuit relates to the
original (`ShippedBase`: disclosure, the ZKIR means the shipped circuit
exactly, unused bindings included (`Emit.circuit_exact`), accepts what the
executor records on it, the ledger check and its consequence for public
inputs, producer obligations, reading back) holds for every build. What
relates runs of the shipped circuit to runs of the original depends on the
flag (`ShippedAs`):

* without `--ledger-opt` (`ShippedOK`): the ZKIR accepts exactly the runs of
  the original, with the same outputs and active public inputs; it accepts
  exactly the proof data the `--no-opt` ZKIR accepts under Midnight's
  `preprocess` (`shipped_preprocessFor`); the disclosure check's
  noninterference holds of it (`shipped_noninterference`); and the executor
  does on the shipped circuit what it does on the original, for every oracle
  (`Pass.Sound` strength);
* with `--ledger-opt` (`ShippedLedgerOK`): the ZKIR means the shipped circuit
  exactly; and only against the modelled ledger (`Damp.Ledger.oracles`), with
  witnesses that do what the runtime's do (`Ledger.WitnessesOK`), from a
  well-formed ledger state, the executor completes on the shipped circuit
  exactly when on the original, with the same outputs, private transcript,
  private state and ledger state (`Pass.SoundLedger` strength), and the ZKIR
  accepts what the executor records on the shipped circuit. The public
  transcript and public inputs differ, so nothing relates the ZKIR to the
  original's on a preimage the executor did not produce.

These hold for every choice of hash functions at `--no-opt`, the default
level and `--O2`, and at `--O3` for Damp's implementations of Midnight's hash
functions (`Damp.Crypto.prims`), with which `--O3` computes hashes of
constants (`OptLevel.SoundAt`).
-/
import Damp.Compile.Build
import Damp.Proofs.Executor
import Damp.Proofs.LedgerAgreement
import Damp.Proofs.Optimize.LedgerCheck
import Damp.Proofs.Optimize.LedgerPipeline
import Damp.Proofs.ZkirJson
import Damp.Proofs.ZkirText
import Damp.Proofs.ExportJson
import Damp.Proofs.Shipped
import Damp.Proofs.Disclosure

namespace Damp
open IR
open Damp.Zkir (Prims Outcome)

/-! ## The pure core of `Contract.build`

`Contract.buildCore`, `Contract.emitAll`, `zkirFiles` and `buildPass` are
defined in `Damp/Compile/Build.lean` and `Damp/Compile/Export.lean`;
`Contract.build` runs `buildCore` and writes exactly what it returns. -/

/-- The hash functions for which a level's pass is sound: all of them, except
    at `--O3`, which computes hashes of constants with `Damp.Crypto.prims`. -/
def OptLevel.SoundAt : OptLevel → Prims → Prop
  | .max, p => p = Crypto.prims
  | _, _ => True

/-- Every level but `--O3` is a sound pass. -/
theorem buildPass_sound : ∀ (level : OptLevel), level ≠ .max → Pass.Sound (buildPass level)
  | .none, _ => Pass.Sound.id
  | .default, _ => Circuit.optimize_sound
  | .full, _ => Circuit.optimizeFull_sound
  | .max, h => absurd rfl h

/-- Each level's pass is sound for the hash functions it is sound at. -/
theorem buildPass_soundFor : ∀ (level : OptLevel) (p : Prims), level.SoundAt p → Pass.SoundFor p (buildPass level)
  | .none, p, _ => Pass.Sound.id.soundFor p
  | .default, p, _ => Circuit.optimize_sound.soundFor p
  | .full, p, _ => Circuit.optimizeFull_sound.soundFor p
  | .max, _, h => by subst h; exact Circuit.optimizeMax_soundFor

/-- With `--ledger-opt`, each level's pass followed by the ledger passes is
    sound against the modelled ledger for the hash functions the level is
    sound at. -/
theorem buildPass_soundLedgerFor (level : OptLevel) (p : Prims) (h : level.SoundAt p) :
    Pass.SoundLedgerFor p (buildPassWith level true) :=
  Pass.SoundLedgerFor.after_soundFor (f := buildPass level) (buildPass_soundFor level p h) ledgerPasses_soundLedger

/-- With `--ledger-opt`, every level but `--O3` is sound against the modelled ledger. -/
theorem buildPass_soundLedger (level : OptLevel) (h : level ≠ .max) : Pass.SoundLedger (buildPassWith level true) :=
  Pass.SoundLedger.after_sound (f := buildPass level) (buildPass_sound level h) ledgerPasses_soundLedger

theorem shipped_allCircuits (c : Contract) (level : OptLevel) (ledgerOpt : Bool := false) :
    (c.optimize level ledgerOpt).allCircuits = c.allCircuits.map (buildPassWith level ledgerOpt) := by
  simp [Contract.allCircuits, Contract.optimize, Option.toList]
  cases c.constructor <;> simp

namespace BuildProof

/-! ## Loops in `Except` -/

theorem forIn_check_ok {α : Type} (l : List α) (g : α → Except String Unit) (msg : α → String → String)
    (u : PUnit) :
    (forIn (m := Except String) l PUnit.unit fun x _ =>
        match g x with
        | .error e => throw (msg x e)
        | _ => pure (ForInStep.yield PUnit.unit)) = .ok u →
      ∀ x ∈ l, g x = .ok () := by
  induction l with
  | nil => simp
  | cons a l ih =>
      intro h x hx
      rw [List.forIn_cons] at h
      cases hg : g a with
      | error e => simp [hg, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
      | ok v =>
          simp only [hg, pure, Except.pure, bind, Except.bind] at h
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hg
          · exact ih h x hx

theorem mapM_emit_ok (msg : Circuit → String → String) :
    ∀ (l : List Circuit) (out : List (Circuit × Zkir.IrSource)),
    (l.mapM (m := Except String) fun circ =>
        match Emit.circuit circ with
        | .ok src => pure (circ, src)
        | .error e => throw (msg circ e)) = .ok out →
      out.map (·.1) = l ∧ ∀ x ∈ out, Emit.circuit x.1 = .ok x.2
  | [], out, h => by
      simp [List.mapM_nil, pure, Except.pure] at h; subst h; simp
  | a :: l, out, h => by
      rw [List.mapM_cons] at h
      cases hl : l.mapM (m := Except String) (fun circ =>
          match Emit.circuit circ with
          | .ok src => pure (circ, src)
          | .error e => throw (msg circ e)) with
      | error e =>
          rw [hl] at h
          cases ha : Emit.circuit a <;>
            simp [ha, throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure, Except.pure] at h
      | ok out' =>
          rw [hl] at h
          cases ha : Emit.circuit a with
          | error e => simp [ha, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
          | ok src =>
              simp [ha, bind, Except.bind, pure, Except.pure] at h; subst h
              obtain ⟨h1, h2⟩ := mapM_emit_ok msg l out' hl
              refine ⟨by simp [h1], ?_⟩
              intro x hx
              rcases List.mem_cons.mp hx with rfl | hx
              · exact ha
              · exact h2 x hx

theorem emitAll_ok {c : Contract} {out : List (Circuit × Zkir.IrSource)} (h : c.emitAll = .ok out) :
    c.check = .ok () ∧ out.map (·.1) = c.allCircuits ∧ ∀ x ∈ out, Emit.circuit x.1 = .ok x.2 := by
  unfold Contract.emitAll at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i u h3
    obtain ⟨h5, h6⟩ := mapM_emit_ok _ _ _ h
    exact ⟨by cases u; exact h3, h5, h6⟩

/-- What a successful `buildCore` establishes, plainly. -/
theorem buildCore_ok {c : Contract} {level : OptLevel} {ledgerOpt : Bool} {shipped : Contract}
    {srcs : List (Circuit × Zkir.IrSource)} (h : c.buildCore level ledgerOpt = .ok (shipped, srcs)) :
    shipped = c.optimize level ledgerOpt ∧
    (∀ circ ∈ c.allCircuits, circ.checkDisclosure = .ok ()) ∧
    (∀ circ ∈ shipped.allCircuits, circ.checkLedger = .ok ()) ∧
    shipped.check = .ok () ∧
    srcs.map (·.1) = shipped.allCircuits ∧
    ∀ x ∈ srcs, Emit.circuit x.1 = .ok x.2 := by
  unfold Contract.buildCore at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i u1 h1
    have hd := forIn_check_ok _ _ _ u1 h1
    split at h
    · cases h
    · rename_i u2 h2
      have hl := forIn_check_ok _ _ _ u2 h2
      split at h
      · cases h
      · rename_i out h4
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hc, h5, h6⟩ := emitAll_ok h4
        exact ⟨rfl, hd, hl, hc, h5, h6⟩

end BuildProof
open BuildProof

/-! ## Facts about one emitted circuit -/

/-- The emitter's own checks hold of what it returns. -/
theorem Emit.circuit_checkProducer (c : Circuit) (src : Zkir.IrSource) (h : Emit.circuit c = .ok src) :
    src.checkProducer = .ok () := by
  unfold Emit.circuit at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  · cases hcore : Emit.circuitCore (Emit.pruned c) with
    | error m => simp [hcore, bind, Except.bind] at h
    | ok src' =>
        cases hchk : src'.checkProducer with
        | error m => simp [hcore, hchk, bind, Except.bind] at h
        | ok u =>
            simp [hcore, hchk, bind, Except.bind, pure, Except.pure] at h
            subst h; cases u; exact hchk

/-- What is proved about the ZKIR `src` shipped for the contract circuit
    `circ`, when the shipped circuit is `s`, whatever the optimization: what
    does not depend on how `s` relates to `circ` beyond the build's checks. -/
structure ShippedBase (circ s : Circuit) (src : Zkir.IrSource) : Prop where
  /-- The original circuit passed the disclosure check. -/
  disclosure : circ.checkDisclosure = .ok ()
  /-- (1) The ZKIR means exactly the shipped circuit, unused bindings dropped
      (`compile_exact`). -/
  exact : ∀ (p : Prims) (inputs priv pub : List Fr),
    src.run p inputs priv pub = (Emit.pruned s).run p inputs priv pub
  /-- (1') ... and so exactly the shipped circuit itself, unused bindings
      included: the emitter drops only bindings that cannot fail
      (`Emit.circuit_exact`, from `Emit.pruned_run_eq`). Whatever the ZKIR
      accepts, `Circuit.run` of the shipped circuit accepts, with the same
      outcome, and conversely. -/
  exactSource : ∀ (p : Prims) (inputs priv pub : List Fr),
    src.run p inputs priv pub = s.run p inputs priv pub
  /-- (3) What the executor records on the shipped circuit, the ZKIR accepts
      (`run_accepted_by_emitted`). -/
  accepted : ∀ {ω σ : Type} (p : Prims) (O : Exec.Oracles ω σ) (inputs : List Fr) (w : ω) (l : σ)
      (r : Exec.Result ω σ), Exec.run p O s inputs w l = some r →
    src.run p inputs r.priv r.pub = some { outputs := r.outputs, groups := r.groups }
  /-- (4) The shipped circuit passes the ledger check ... -/
  ledger : s.checkLedger = .ok ()
  /-- ... so every active public input the executor records on it encodes an
      instruction the ledger ran (`run_groups_fromLedger`). -/
  groups : ∀ {ω σ : Type} (p : Prims) (O : Exec.Oracles ω σ) (inputs : List Fr) (w : ω) (l : σ)
      (r : Exec.Result ω σ), Exec.run p O s inputs w l = some r →
    ∀ grp ∈ r.groups, grp.active = true → Exec.FromLedger p O s.body.toList grp
  /-- (5) The ZKIR meets the producer obligations of upstream's soundness result,
      and every immediate is one Midnight's loader accepts. -/
  producer : src.checkProducer = .ok ()
  /-- (6) The JSON tree written to the `.zkir` file reads back, with Damp's
      reader (which follows the loader's rules), as `src` itself
      (`IrSource.ofJson_toJson`). -/
  readsBack : Zkir.IrSource.ofJson src.toJson = .ok src
  /-- (7) ... and so does the text: any text that lexes as the tokens of
      `src.toJson` (the compact text, or any layout of the same tokens with
      JSON whitespace between them) parses, with Damp's total reference parser
      (`Zkir.Text.parse`), to a value Damp's reader reads as `src`
      (`IrSource.ofText`). That the `Json.pretty` text written to the file is
      such a layout, and that `Zkir.Text.parse` agrees with Lean's
      `Json.parse`, is tested, not proved (`test/jsontext.sh`). -/
  readsBackText : ∀ text, Zkir.Text.lex text = .ok (Zkir.Text.toks src.toJson) →
    (Zkir.Text.parse text >>= Zkir.IrSource.ofJson) = .ok src

/-- Everything proved about the ZKIR `src` shipped for the contract circuit
    `circ`, when the shipped circuit is `s` and the build ran without
    `--ledger-opt`: `ShippedBase`, and what relates runs of `s` to runs of
    `circ`, proved for the hash functions `sound` admits. -/
structure ShippedOK (sound : Prims → Prop) (circ s : Circuit) (src : Zkir.IrSource) : Prop
    extends ShippedBase circ s src where
  /-- (2) The ZKIR accepts exactly the runs the original circuit accepts, with
      the same outputs and active public inputs: on every inputs, private
      transcript and ledger reads, both reject or both accept with the same
      observable outcome (`Emit.circuit_exact` and `Pass.SoundFor.run`; the
      direction "original accepts ⇒ ZKIR accepts" is `compile_complete`). -/
  complete : ∀ (p : Prims), sound p → ∀ (inputs priv pub : List Fr),
    (src.run p inputs priv pub).map Outcome.observable = (circ.run p inputs priv pub).map Outcome.observable
  /-- (2') The shipped ZKIR and the ZKIR `--no-opt` ships for `circ` (`src₀`)
      accept exactly the same proof data under Midnight's `preprocess` (inputs,
      private transcript, ledger reads, claimed public inputs, commitment),
      with the same outputs and active public inputs
      (`shipped_preprocessFor`). -/
  sameAsNoOpt : ∀ (p : Prims), sound p → ∀ (src₀ : Zkir.IrSource), Emit.circuit circ = .ok src₀ →
    ∀ pre : Zkir.Preimage, (src.preprocess p pre).map Outcome.observable = (src₀.preprocess p pre).map Outcome.observable
  /-- (2'') Noninterference holds of the shipped ZKIR: two runs it accepts that
      read the same values from the ledger, and in which every disclosed value
      the original circuit's public inputs could depend on agrees
      (`IR.Agree`, about `circ`), have the same active public inputs, whatever
      their arguments and private transcripts (`shipped_noninterference`, from
      `groups_noninterference` on `circ`). -/
  noninterference : ∀ (p : Prims), sound p → ∀ (in₁ in₂ priv₁ priv₂ pub : List Fr) (o₁ o₂ : Outcome),
    src.run p in₁ priv₁ pub = some o₁ → src.run p in₂ priv₂ pub = some o₂ →
    (∀ env₁ env₂, bindInputs (fun _ => 0) circ.inputs in₁ = some env₁ →
      bindInputs (fun _ => 0) circ.inputs in₂ = some env₂ →
      IR.Agree p circ.body.toList { env := env₁, priv := priv₁, pub } { env := env₂, priv := priv₂, pub }) →
    o₁.activeInputs = o₂.activeInputs
  /-- The executor on the shipped circuit does what it does on the original. -/
  exec_same : ∀ {ω σ : Type} (p : Prims), sound p → ∀ (O : Exec.Oracles ω σ) (inputs : List Fr) (w : ω) (l : σ),
    (Exec.run p O s inputs w l).map Exec.Result.observable =
      (Exec.run p O circ inputs w l).map Exec.Result.observable

/-- `ShippedOK.complete` in the form of `compile_complete`. -/
theorem ShippedOK.complete_run {sound : Prims → Prop} {circ s : Circuit} {src : Zkir.IrSource}
    (h : ShippedOK sound circ s src) (p : Prims) (hp : sound p) (inputs priv pub : List Fr) (o : Outcome)
    (hr : circ.run p inputs priv pub = some o) :
    ∃ o', src.run p inputs priv pub = some o' ∧ o'.observable = o.observable := by
  have e := h.complete p hp inputs priv pub
  rw [hr] at e
  cases h1 : src.run p inputs priv pub with
  | none => rw [h1] at e; cases e
  | some o' => rw [h1] at e; exact ⟨o', rfl, Option.some.inj e⟩

/-- `ShippedOK.complete`, the other way: whatever the shipped ZKIR accepts, the
    original circuit accepts, with the same outputs and active public inputs. -/
theorem ShippedOK.sound_run {sound : Prims → Prop} {circ s : Circuit} {src : Zkir.IrSource}
    (h : ShippedOK sound circ s src) (p : Prims) (hp : sound p) (inputs priv pub : List Fr) (o' : Outcome)
    (hr : src.run p inputs priv pub = some o') :
    ∃ o, circ.run p inputs priv pub = some o ∧ o.observable = o'.observable := by
  have e := h.complete p hp inputs priv pub
  rw [hr] at e
  cases h1 : circ.run p inputs priv pub with
  | none => rw [h1] at e; cases e
  | some o => rw [h1] at e; exact ⟨o, rfl, (Option.some.inj e).symm⟩

/-- Everything proved about the ZKIR `src` shipped for the contract circuit
    `circ`, when the shipped circuit is `s` and the build ran with
    `--ledger-opt`: `ShippedBase`, and, only against the modelled ledger
    (`Damp.Ledger.oracles`) with witnesses that do what the runtime's do
    (`Ledger.WitnessesOK`), from a well-formed ledger state and for the hash
    functions `sound` admits, what relates runs of `s` to runs of `circ`.

    What the ZKIR accepts is pinned to the shipped circuit exactly
    (`ShippedBase.exactSource`: `src.run = s.run`), and the executor runs of `s`
    are pinned to those of `circ` in both directions (`exec_ledger`,
    `complete_exec`, `sound_exec`). What is **not** stated, because it is not
    true or not proved:

    * the public transcript and the public inputs of `s` differ from those of
      `circ` by design (the ledger passes drop, merge and reorder ledger
      instructions), so nothing relates `src` to the ZKIR of `circ` (no
      `sameAsNoOpt`) and the disclosure check's noninterference is not
      transferred (it is about `circ`'s public inputs);
    * nothing relates acceptance of `src` on an arbitrary preimage (inputs,
      private transcript, ledger reads chosen by a prover rather than produced
      by the executor against the modelled ledger from a well-formed state) to
      anything about `circ`: `src` accepts it exactly when `s` does, and that
      is all;
    * the on-chain replay of the public transcript against a state other than
      the one the executor ran from (audit finding F4), and gas, are not
      modelled. -/
structure ShippedLedgerOK (sound : Prims → Prop) (circ s : Circuit) (src : Zkir.IrSource) : Prop
    extends ShippedBase circ s src where
  /-- The executor against the modelled ledger completes on the shipped
      circuit exactly when on the original, with the same outputs, private
      transcript, private state and ledger state (`Pass.SoundLedger`). -/
  exec_ledger : ∀ (p : Prims), sound p → ∀ {ω : Type} (H : Ledger.Hooks)
      (w : Exec.WitnessOracle ω Ledger.LedgerState), Ledger.WitnessesOK w → ∀ (inputs : List Fr) (private_ : ω)
      (σ : Ledger.LedgerState), σ.WF →
    (Exec.run p (Ledger.oracles H w) s inputs private_ σ).map Exec.Result.ledgerObservable =
      (Exec.run p (Ledger.oracles H w) circ inputs private_ σ).map Exec.Result.ledgerObservable
  /-- So every call of the original circuit the executor completes against the
      modelled ledger completes on the shipped circuit, with the same outputs,
      private transcript, private state and ledger state, and the ZKIR accepts
      what the executor records on the shipped circuit, which is a run of the
      shipped circuit itself (`exactSource`). -/
  complete_exec : ∀ (p : Prims), sound p → ∀ {ω : Type} (H : Ledger.Hooks)
      (w : Exec.WitnessOracle ω Ledger.LedgerState), Ledger.WitnessesOK w → ∀ (inputs : List Fr) (private_ : ω)
      (σ : Ledger.LedgerState), σ.WF → ∀ r, Exec.run p (Ledger.oracles H w) circ inputs private_ σ = some r →
    ∃ r', Exec.run p (Ledger.oracles H w) s inputs private_ σ = some r' ∧
      r'.ledgerObservable = r.ledgerObservable ∧
      src.run p inputs r'.priv r'.pub = some { outputs := r'.outputs, groups := r'.groups } ∧
      s.run p inputs r'.priv r'.pub = some { outputs := r'.outputs, groups := r'.groups }
  /-- Conversely, every call the executor completes on the shipped circuit
      against the modelled ledger, from a well-formed state, is one it
      completes on the original, with the same outputs, private transcript,
      private state and ledger state; and the ZKIR accepts what was recorded. -/
  sound_exec : ∀ (p : Prims), sound p → ∀ {ω : Type} (H : Ledger.Hooks)
      (w : Exec.WitnessOracle ω Ledger.LedgerState), Ledger.WitnessesOK w → ∀ (inputs : List Fr) (private_ : ω)
      (σ : Ledger.LedgerState), σ.WF → ∀ r', Exec.run p (Ledger.oracles H w) s inputs private_ σ = some r' →
    ∃ r, Exec.run p (Ledger.oracles H w) circ inputs private_ σ = some r ∧
      r.ledgerObservable = r'.ledgerObservable ∧
      src.run p inputs r'.priv r'.pub = some { outputs := r'.outputs, groups := r'.groups }

/-- What is proved about a shipped circuit, by whether the build ran with
    `--ledger-opt`. -/
def ShippedAs (sound : Prims → Prop) : Bool → Circuit → Circuit → Zkir.IrSource → Prop
  | false => ShippedOK sound
  | true => ShippedLedgerOK sound

theorem ShippedAs.base {sound : Prims → Prop} {ledgerOpt : Bool} {circ s : Circuit} {src : Zkir.IrSource}
    (h : ShippedAs sound ledgerOpt circ s src) : ShippedBase circ s src := by
  cases ledgerOpt
  · exact ShippedOK.toShippedBase h
  · exact ShippedLedgerOK.toShippedBase h

theorem shippedBase_of {f : Pass} {circ : Circuit} {src : Zkir.IrSource}
    (hd : circ.checkDisclosure = .ok ()) (hl : (f circ).checkLedger = .ok ())
    (he : Emit.circuit (f circ) = .ok src) : ShippedBase circ (f circ) src where
  disclosure := hd
  exact p inputs priv pub :=
    Emit.circuitCore_correct p _ src (Emit.circuit_eq_core _ src he) inputs priv pub
  exactSource p inputs priv pub := Emit.circuit_exact p _ src he inputs priv pub
  accepted p O inputs w l r h := Exec.run_accepted_by_emitted p O _ src he inputs w l r h
  ledger := hl
  groups p _ _ _ _ _ h := Exec.run_groups_fromLedger p hl h
  producer := Emit.circuit_checkProducer _ src he
  readsBack := Zkir.IrSource.ofJson_toJson_of_emitted he
  readsBackText := Zkir.IrSource.ofText_of_emitted he

/-- **Noninterference of the shipped ZKIR.** For a pass sound at `p` and a
    circuit that passes the disclosure check, two runs the ZKIR emitted for
    `f circ` accepts with the same ledger reads, in which every disclosed value
    `circ`'s public inputs could depend on agrees, have the same active public
    inputs: `groups_noninterference` on `circ`, carried to the ZKIR by
    `Emit.circuit_exact` and `Pass.SoundFor.run`. -/
theorem shipped_noninterference {p : Prims} {f : Pass} (hf : Pass.SoundFor p f) {circ : Circuit}
    (hd : circ.checkDisclosure = .ok ()) {src : Zkir.IrSource} (he : Emit.circuit (f circ) = .ok src)
    (in₁ in₂ priv₁ priv₂ pub : List Fr) (o₁ o₂ : Outcome)
    (h₁ : src.run p in₁ priv₁ pub = some o₁) (h₂ : src.run p in₂ priv₂ pub = some o₂)
    (hagree : ∀ env₁ env₂, bindInputs (fun _ => 0) circ.inputs in₁ = some env₁ →
      bindInputs (fun _ => 0) circ.inputs in₂ = some env₂ →
      IR.Agree p circ.body.toList { env := env₁, priv := priv₁, pub } { env := env₂, priv := priv₂, pub }) :
    o₁.activeInputs = o₂.activeInputs := by
  have e₁ := hf.run circ in₁ priv₁ pub
  have e₂ := hf.run circ in₂ priv₂ pub
  rw [← Emit.circuit_exact p _ src he, h₁] at e₁
  rw [← Emit.circuit_exact p _ src he, h₂] at e₂
  cases hc₁ : circ.run p in₁ priv₁ pub with
  | none => rw [hc₁] at e₁; cases e₁
  | some c₁ =>
  cases hc₂ : circ.run p in₂ priv₂ pub with
  | none => rw [hc₂] at e₂; cases e₂
  | some c₂ =>
  rw [hc₁] at e₁; rw [hc₂] at e₂
  simp only [Option.map_some, Option.some.injEq, Outcome.observable, Prod.mk.injEq] at e₁ e₂
  have hg := groups_noninterference p circ hd in₁ in₂ priv₁ priv₂ pub c₁ c₂ hc₁ hc₂ hagree
  rw [e₁.2, e₂.2]
  simp only [Zkir.Outcome.activeInputs, hg]

theorem shippedOK_of {f : Pass} {sound : Prims → Prop} (hf : ∀ p, sound p → Pass.SoundFor p f)
    {circ : Circuit} {src : Zkir.IrSource}
    (hd : circ.checkDisclosure = .ok ()) (hl : (f circ).checkLedger = .ok ())
    (he : Emit.circuit (f circ) = .ok src) : ShippedOK sound circ (f circ) src :=
  { shippedBase_of hd hl he with
    complete := fun p hp inputs priv pub => by
      rw [Emit.circuit_exact p _ src he]; exact (hf p hp).run circ inputs priv pub
    sameAsNoOpt := fun p hp src₀ h₀ pre => shipped_preprocessFor (hf p hp) circ src src₀ he h₀ pre
    noninterference := fun p hp in₁ in₂ priv₁ priv₂ pub o₁ o₂ h₁ h₂ hagree =>
      shipped_noninterference (hf p hp) hd he in₁ in₂ priv₁ priv₂ pub o₁ o₂ h₁ h₂ hagree
    exec_same := fun p hp O inputs w l => (hf p hp).exec O circ inputs w l }

theorem shippedLedgerOK_of {f : Pass} {sound : Prims → Prop} (hf : ∀ p, sound p → Pass.SoundLedgerFor p f)
    {circ : Circuit} {src : Zkir.IrSource}
    (hd : circ.checkDisclosure = .ok ()) (hl : (f circ).checkLedger = .ok ())
    (he : Emit.circuit (f circ) = .ok src) : ShippedLedgerOK sound circ (f circ) src :=
  have hb := shippedBase_of hd hl he
  { hb with
    exec_ledger := fun p hp {_} H w hw inputs private_ σ hσ => (hf p hp).exec H w hw circ inputs private_ σ hσ
    complete_exec := fun p hp {_} H w hw inputs private_ σ hσ r hr => by
      have e := (hf p hp).exec H w hw circ inputs private_ σ hσ
      rw [hr] at e
      cases h1 : Exec.run p (Ledger.oracles H w) (f circ) inputs private_ σ with
      | none => rw [h1] at e; cases e
      | some r' =>
          rw [h1] at e
          simp only [Option.map_some, Option.some.injEq] at e
          have ha := hb.accepted p _ inputs private_ σ r' h1
          exact ⟨r', rfl, e, ha, (hb.exactSource p inputs r'.priv r'.pub).symm.trans ha⟩
    sound_exec := fun p hp {_} H w hw inputs private_ σ hσ r' hr' => by
      have e := (hf p hp).exec H w hw circ inputs private_ σ hσ
      rw [hr'] at e
      cases h1 : Exec.run p (Ledger.oracles H w) circ inputs private_ σ with
      | none => rw [h1] at e; cases e
      | some r =>
          rw [h1] at e
          simp only [Option.map_some, Option.some.injEq] at e
          exact ⟨r, rfl, e.symm, hb.accepted p _ inputs private_ σ r' hr'⟩ }

/-! ## The theorem -/

/-- **What a successful build guarantees.** If `buildCore` succeeds (at any
    level: `--no-opt`, the default, `--O2`, `--O3`, with or without
    `--ledger-opt`), it returns one entry per circuit of the contract, in
    order, and for each circuit `circ` the entry is `(s, src)` where `s` is
    `circ` under the selected optimization and `src` is the ZKIR emitted for
    `s`; and `ShippedAs level.SoundAt ledgerOpt circ s src` holds. For every
    build (`ShippedBase`): the ZKIR means the shipped circuit exactly (unused
    bindings included), accepts what the executor records on the shipped
    circuit, the shipped circuit passes the ledger check (with its
    consequence for the executor's public inputs), the ZKIR meets the
    producer obligations, and its JSON reads back as itself, as a JSON tree
    and as text (for every text that lexes as its tokens). Without
    `--ledger-opt` (`ShippedOK`), the ZKIR accepts exactly the runs the
    original circuit accepts with the same observable outcome, accepts
    exactly the proof data the `--no-opt` ZKIR accepts, satisfies the
    disclosure noninterference of the original, and the executor does on the
    shipped circuit what it does on the original, for every oracle. With it
    (`ShippedLedgerOK`), the executor does on the shipped circuit what it does
    on the original only against the modelled ledger, with witnesses that
    respect `Ledger.WitnessesOK`, from a well-formed state, and only up to the
    public transcript and public inputs. The statements about runs of the
    original circuit hold for every choice of hash functions, except at
    `--O3`, where they hold for `Damp.Crypto.prims` (`OptLevel.SoundAt`). -/
theorem build_correct {c : Contract} {level : OptLevel} {ledgerOpt : Bool} {shipped : Contract}
    {srcs : List (Circuit × Zkir.IrSource)} (h : c.buildCore level ledgerOpt = .ok (shipped, srcs)) :
    shipped = c.optimize level ledgerOpt ∧
    shipped.check = .ok () ∧
    srcs.map (·.1) = c.allCircuits.map (buildPassWith level ledgerOpt) ∧
    ∀ circ ∈ c.allCircuits, ∃ src, (buildPassWith level ledgerOpt circ, src) ∈ srcs ∧
      ShippedAs level.SoundAt ledgerOpt circ (buildPassWith level ledgerOpt circ) src := by
  obtain ⟨hs, hd, hl, hc, hm, he⟩ := buildCore_ok h
  subst hs
  rw [shipped_allCircuits c level ledgerOpt] at hl hm
  refine ⟨rfl, hc, hm, ?_⟩
  intro circ hcirc
  have hmem : buildPassWith level ledgerOpt circ ∈ srcs.map (·.1) := by
    rw [hm]; exact List.mem_map_of_mem hcirc
  obtain ⟨⟨s, src⟩, hx, hs⟩ := List.mem_map.mp hmem
  simp only at hs; subst hs
  refine ⟨src, hx, ?_⟩
  cases ledgerOpt
  · exact shippedOK_of (buildPass_soundFor level) (hd circ hcirc)
      (hl _ (List.mem_map_of_mem hcirc)) (he _ hx)
  · exact shippedLedgerOK_of (buildPass_soundLedgerFor level) (hd circ hcirc)
      (hl _ (List.mem_map_of_mem hcirc)) (he _ hx)

/-- `build_correct` for a build without `--ledger-opt`, in the form it had
    before the flag existed: `ShippedOK`, `Pass.Sound` strength. -/
theorem build_correct_sound {c : Contract} {level : OptLevel} {shipped : Contract}
    {srcs : List (Circuit × Zkir.IrSource)} (h : c.buildCore level = .ok (shipped, srcs)) :
    shipped = c.optimize level ∧
    shipped.check = .ok () ∧
    srcs.map (·.1) = c.allCircuits.map (buildPass level) ∧
    ∀ circ ∈ c.allCircuits, ∃ src, (buildPass level circ, src) ∈ srcs ∧
      ShippedOK level.SoundAt circ (buildPass level circ) src :=
  build_correct h

/-- `build_correct` for a build with `--ledger-opt`: `ShippedLedgerOK`,
    `Pass.SoundLedger` strength. -/
theorem build_correct_ledgerOpt {c : Contract} {level : OptLevel} {shipped : Contract}
    {srcs : List (Circuit × Zkir.IrSource)} (h : c.buildCore level true = .ok (shipped, srcs)) :
    shipped = c.optimize level true ∧
    shipped.check = .ok () ∧
    srcs.map (·.1) = c.allCircuits.map (buildPassWith level true) ∧
    ∀ circ ∈ c.allCircuits, ∃ src, (buildPassWith level true circ, src) ∈ srcs ∧
      ShippedLedgerOK level.SoundAt circ (buildPassWith level true circ) src :=
  build_correct h

/-- **What `contract.json` gives the executor.** If `buildCore` succeeds, the
    contract written to `contract.json` is the shipped contract `c.optimize level`,
    and any text that lexes as the tokens of what is written (`Export.contract`)
    reads back, with Damp's reference parser and `Export.ofJson`, as that
    contract with what the file does not carry erased (`Contract.exported`:
    `disclose` wrappers, input names and ranges, circuit errors). That the
    `Json.pretty` text written to the file lexes so is tested
    (`test/jsontext.sh`). -/
theorem build_contractJson {c : Contract} {level : OptLevel} {ledgerOpt : Bool} {shipped : Contract}
    {srcs : List (Circuit × Zkir.IrSource)} (h : c.buildCore level ledgerOpt = .ok (shipped, srcs)) :
    shipped = c.optimize level ledgerOpt ∧
    ∀ text, Zkir.Text.lex text = .ok (Zkir.Text.toks (Export.contract shipped)) →
      Export.parse text = .ok shipped.exported :=
  ⟨(BuildProof.buildCore_ok h).1, fun text hl => Export.ofText shipped text hl⟩

/-- The ledger check `buildCore` makes on the shipped circuits never fails on
    a circuit that already passes it: the optimizer keeps ledger statements
    well formed (`Circuit.optimize_checkLedger`), and so do the ledger passes
    (`ledgerPasses_keepsLedger`). -/
theorem buildPassWith_checkLedger (level : OptLevel) (ledgerOpt : Bool) (c : Circuit)
    (h : c.checkLedger = .ok ()) : (buildPassWith level ledgerOpt c).checkLedger = .ok () := by
  have h0 : (level.pass c).checkLedger = .ok () := by
    cases level
    · exact h
    · exact Circuit.optimize_checkLedger c h
    · exact Circuit.optimizeFull_checkLedger c h
    · exact Circuit.optimizeMax_checkLedger c h
  cases ledgerOpt
  · exact h0
  · exact ledgerPasses_keepsLedger _ h0

theorem buildPass_checkLedger (level : OptLevel) (c : Circuit) (h : c.checkLedger = .ok ()) :
    (buildPass level c).checkLedger = .ok () :=
  buildPassWith_checkLedger level false c h

end Damp
