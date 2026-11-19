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
about the ZKIR shipped for it, at every optimization level. What concerns runs
of the original circuit (`ShippedOK.complete`, `ShippedOK.exec_same`) holds for
every choice of hash functions at `--no-opt`, the default level and `--O2`,
and at `--O3` for Damp's implementations of Midnight's hash functions
(`Damp.Crypto.prims`), with which `--O3` computes hashes of constants
(`OptLevel.SoundAt`).
-/
import Damp.Compile.Build
import Damp.Proofs.Executor
import Damp.Proofs.LedgerAgreement
import Damp.Proofs.Optimize.LedgerCheck
import Damp.Proofs.ZkirJson

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

theorem shipped_allCircuits (c : Contract) (level : OptLevel) :
    (c.optimize level).allCircuits = c.allCircuits.map (buildPass level) := by
  simp [Contract.allCircuits, Contract.optimize, buildPass, Option.toList]
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
theorem buildCore_ok {c : Contract} {level : OptLevel} {shipped : Contract}
    {srcs : List (Circuit × Zkir.IrSource)} (h : c.buildCore level = .ok (shipped, srcs)) :
    shipped = c.optimize level ∧
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

/-- Everything proved about the ZKIR `src` shipped for the contract circuit
    `circ`, when the shipped circuit is `s`; what relates runs of `s` to runs
    of `circ` is proved for the hash functions `sound` admits. -/
structure ShippedOK (sound : Prims → Prop) (circ s : Circuit) (src : Zkir.IrSource) : Prop where
  /-- The original circuit passed the disclosure check. -/
  disclosure : circ.checkDisclosure = .ok ()
  /-- (1) The ZKIR means exactly the shipped circuit, unused bindings dropped
      (`compile_exact`). -/
  exact : ∀ (p : Prims) (inputs priv pub : List Fr),
    src.run p inputs priv pub = (Emit.pruned s).run p inputs priv pub
  /-- (2) Every run the original circuit accepts, the ZKIR accepts, with the same
      outputs and active public inputs (`compile_complete`). -/
  complete : ∀ (p : Prims), sound p → ∀ (inputs priv pub : List Fr) (o : Outcome),
    circ.run p inputs priv pub = some o →
      ∃ o', src.run p inputs priv pub = some o' ∧ o'.observable = o.observable
  /-- The executor on the shipped circuit does what it does on the original. -/
  exec_same : ∀ {ω σ : Type} (p : Prims), sound p → ∀ (O : Exec.Oracles ω σ) (inputs : List Fr) (w : ω) (l : σ),
    (Exec.run p O s inputs w l).map Exec.Result.observable =
      (Exec.run p O circ inputs w l).map Exec.Result.observable
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

theorem shippedOK_of {f : Pass} {sound : Prims → Prop} (hf : ∀ p, sound p → Pass.SoundFor p f)
    {circ : Circuit} {src : Zkir.IrSource}
    (hd : circ.checkDisclosure = .ok ()) (hl : (f circ).checkLedger = .ok ())
    (he : Emit.circuit (f circ) = .ok src) : ShippedOK sound circ (f circ) src where
  disclosure := hd
  exact p inputs priv pub :=
    Emit.circuitCore_correct p _ src (Emit.circuit_eq_core _ src he) inputs priv pub
  complete p hp inputs priv pub o hrun := compile_complete_ofFor (hf p hp) circ src he inputs priv pub o hrun
  exec_same p hp O inputs w l := (hf p hp).exec O circ inputs w l
  accepted p O inputs w l r h := Exec.run_accepted_by_emitted p O _ src he inputs w l r h
  ledger := hl
  groups p _ _ _ _ _ h := Exec.run_groups_fromLedger p hl h
  producer := Emit.circuit_checkProducer _ src he
  readsBack := Zkir.IrSource.ofJson_toJson_of_emitted he

/-! ## The theorem -/

/-- **What a successful build guarantees.** If `buildCore` succeeds (at any
    level: `--no-opt`, the default, `--O2`, `--O3`), it returns one entry per circuit
    of the contract, in order, and for each circuit `circ` the entry is
    `(s, src)` where `s` is `circ` under the selected optimization and `src` is
    the ZKIR emitted for `s`; and `ShippedOK circ s src` holds: the ZKIR means
    the shipped circuit exactly, accepts every run of the original circuit with
    the same observable outcome, accepts what the executor records on the
    shipped circuit, the shipped circuit passes the ledger check (with its
    consequence for the executor's public inputs), the ZKIR meets the
    producer obligations, and its JSON reads back as itself. The two
    statements about runs of the original circuit hold for every choice of
    hash functions, except at `--O3`, where they hold for `Damp.Crypto.prims`
    (`OptLevel.SoundAt`). -/
theorem build_correct {c : Contract} {level : OptLevel} {shipped : Contract}
    {srcs : List (Circuit × Zkir.IrSource)} (h : c.buildCore level = .ok (shipped, srcs)) :
    shipped = c.optimize level ∧
    shipped.check = .ok () ∧
    srcs.map (·.1) = c.allCircuits.map (buildPass level) ∧
    ∀ circ ∈ c.allCircuits, ∃ src, (buildPass level circ, src) ∈ srcs ∧
      ShippedOK level.SoundAt circ (buildPass level circ) src := by
  obtain ⟨hs, hd, hl, hc, hm, he⟩ := buildCore_ok h
  subst hs
  rw [shipped_allCircuits] at hl hm
  refine ⟨rfl, hc, hm, ?_⟩
  intro circ hcirc
  have hmem : buildPass level circ ∈ srcs.map (·.1) := by
    rw [hm]; exact List.mem_map_of_mem hcirc
  obtain ⟨⟨s, src⟩, hx, hs⟩ := List.mem_map.mp hmem
  simp only at hs; subst hs
  refine ⟨src, hx, ?_⟩
  exact shippedOK_of (buildPass_soundFor level) (hd circ hcirc)
    (hl _ (List.mem_map_of_mem hcirc)) (he _ hx)

/-- The ledger check `buildCore` makes on the shipped circuits never fails on
    a circuit that already passes it: the optimizer keeps ledger statements
    well formed (`Circuit.optimize_checkLedger`). -/
theorem buildPass_checkLedger (level : OptLevel) (c : Circuit) (h : c.checkLedger = .ok ()) :
    (buildPass level c).checkLedger = .ok () := by
  cases level
  · exact h
  · exact Circuit.optimize_checkLedger c h
  · exact Circuit.optimizeFull_checkLedger c h
  · exact Circuit.optimizeMax_checkLedger c h

end Damp
