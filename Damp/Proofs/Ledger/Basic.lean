/-
Shared definitions for the theorems about ledger operations
(`Damp/Proofs/Ledger/*.lean`), stated against the VM model
(`Damp/Ledger/Vm.lean`, `Damp/Ledger/Query.lean`).

An operation of `Damp/Lang/Ledger.lean` (`Cell.read`, `Counter.increment`,
...) is a `CircuitM` action that emits one ledger statement. `emitted m` is
that statement's instruction list, taken from running the real definition; the
theorems are about `Exec.request` of it (operands evaluated, as the executor
sends them) run through `ledgerOracle`, the ledger oracle the VM model induces.
-/
import Damp.Lang.Ledger
import Damp.Ledger.Query

namespace Damp.Ledger
open Damp.IR Damp.Impact

/-- The instructions of the last ledger statement `m` emits, run from the empty builder. -/
def emitted {α : Type} (m : CircuitM α) : Option (List (Op Expr)) :=
  match (m.run {}).2.stmts.toList.getLast? with
  | some (.ledger _ _ ops) => some ops
  | _ => none

/-- A ledger state is well formed when its effects are as the runtime would
    re-encode them (true of every state the runtime produces). -/
def LedgerState.WF (σ : LedgerState) : Prop := decodeEffects σ.effects = some σ.effects

/-- The contract's state has top-level field `i` holding `v`. -/
def LedgerState.field (σ : LedgerState) (i : Nat) : Option SV :=
  match σ.state with
  | .array fs => fs[i]?
  | _ => none

/-- Replace top-level field `i`. -/
def LedgerState.setField (σ : LedgerState) (i : Nat) (v : SV) : LedgerState :=
  match σ.state with
  | .array fs => { σ with state := .array (fs.set i v) }
  | _ => σ

/-! ## Lemmas -/

theorem evalList_eq_mapM (p : Zkir.Prims) (env : Env) : ∀ xs : List Expr,
    Expr.evalList p env xs = xs.mapM (Expr.eval p env)
  | [] => rfl
  | x :: xs => by simp only [Expr.evalList, List.mapM_cons, evalList_eq_mapM p env xs]

theorem Fr.ofInt_natCast_val {i : Nat} (h : i < Fr.modulus) : (Fr.ofInt (i : Int)).val = i := by
  show (Fr.ofNat i).val = i
  exact Nat.mod_eq_of_lt h

theorem modulus_gt_2_64 : 2 ^ 64 < Fr.modulus := by decide

/-- A one-byte key `{1: i}`, as the VM sees it. -/
theorem ofAligned_byteKey {i : Nat} (h : i < 256) :
    AV.ofAligned ⟨[.bytes 1], [Fr.ofInt (i : Int)]⟩ = some ⟨[.bytes 1], [i]⟩ := by
  have hm : i < Fr.modulus := Nat.lt_trans h (by decide)
  simp [AV.ofAligned, AV.ofFields, atomWidth, atomOfFields, atomFits, Fr.ofInt_natCast_val hm]
  omega

theorem ofFields_key0 : AV.ofFields [.bytes 1] [Fr.ofInt 0] = some ⟨[.bytes 1], [0]⟩ :=
  ofAligned_byteKey (i := 0) (by decide)
theorem ofFields_key1 : AV.ofFields [.bytes 1] [Fr.ofInt 1] = some ⟨[.bytes 1], [1]⟩ :=
  ofAligned_byteKey (i := 1) (by decide)
theorem ofFields_key2 : AV.ofFields [.bytes 1] [Fr.ofInt 2] = some ⟨[.bytes 1], [2]⟩ :=
  ofAligned_byteKey (i := 2) (by decide)
theorem ofFields_key3 : AV.ofFields [.bytes 1] [Fr.ofInt 3] = some ⟨[.bytes 1], [3]⟩ :=
  ofAligned_byteKey (i := 3) (by decide)
theorem frOfInt_val_one : (Fr.ofInt 1).val = 1 := rfl

theorem readBack_nil : readBack [] [] = some [] := rfl

theorem readBack_cons (a : List Zkir.AlignAtom) (as : List (List Zkir.AlignAtom)) (v : AV) (vs : List AV) :
    readBack (a :: as) (v :: vs) = (do
      let f ← fieldsOf a v.atoms
      let rest ← readBack as vs
      pure (f ++ rest)) := rfl

/-! ## What a reading operation emits -/

theorem mapM_freshVar {β : Type} : ∀ (l : List β) (s : Build),
    (l.mapM (fun _ => freshVar)).run s =
      ((List.range l.length).map (s.next + ·), { s with next := s.next + l.length })
  | [], s => rfl
  | _ :: l, s => by
      rw [List.mapM_cons]
      have h : ((freshVar >>= fun a => l.mapM (fun _ => freshVar) >>= fun r => pure (a :: r)) : CircuitM _).run s
          = (s.next :: ((l.mapM (fun _ => freshVar)).run { s with next := s.next + 1 }).1,
             ((l.mapM (fun _ => freshVar)).run { s with next := s.next + 1 }).2) := rfl
      rw [h, mapM_freshVar l]
      simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
      refine Prod.ext ?_ ?_
      · show s.next :: _ = (s.next + 0) :: _
        congr 1
        apply List.map_congr_left; intro a _
        simp only [Function.comp, Nat.succ_eq_add_one]; rw [Nat.add_assoc, Nat.add_comm 1]
      · show Build.mk _ _ _ _ = Build.mk _ _ _ _
        congr 1; rw [Nat.add_assoc, Nat.add_comm 1]

/-- The variables a reading operation reads into, run from the empty builder. -/
def readVars (α : Type) [Value α] : List Expr := (List.range (Value.width α)).map Expr.var

theorem emitted_ledgerRead (α : Type) [Value α] (mk : List Expr → List (Op Expr)) :
    emitted (ledgerRead α mk) = some (mk (readVars α)) := by
  have h := mapM_freshVar (List.range (Value.width α)) {}
  simp only [List.length_range] at h
  have h0 : (List.range (Value.width α)).map ((({} : Build).next) + ·) = List.range (Value.width α) := by
    show (List.range (Value.width α)).map (0 + ·) = _
    simp
  rw [h0] at h
  have e : (ledgerRead α mk).run {} =
      (Value.ofExprs ((List.range (Value.width α)).map Expr.var),
       { ((List.range (Value.width α)).mapM (fun _ => freshVar)).run {} |>.2 with
         stmts := #[.ledger (.const 1) (List.range (Value.width α)) (mk ((List.range (Value.width α)).map Expr.var))] }) := by
    show (let r := ((List.range (Value.width α)).mapM (fun _ => freshVar)).run {};
          (Value.ofExprs (r.1.map Expr.var),
           { r.2 with stmts := r.2.stmts.push (.ledger r.2.guard r.1 (mk (r.1.map Expr.var))) })) = _
    rw [h]
    rfl
  simp [emitted, e, readVars]

/-- Evaluating plain variables never fails. -/
theorem mapM_eval_vars (p : Zkir.Prims) (env : Env) : ∀ vs : List Var,
    (vs.map Expr.var).mapM (Expr.eval p env) = some (vs.map env)
  | [] => rfl
  | v :: vs => by simp [List.mapM_cons, Expr.eval, mapM_eval_vars p env vs]

theorem mapM_eval_readVars (α : Type) [Value α] (p : Zkir.Prims) (env : Env) :
    (readVars α).mapM (Expr.eval p env) = some ((List.range (Value.width α)).map env) :=
  mapM_eval_vars p env _

/-! ## Running the VM model in proofs

`vm_simp [h₁, ...]` unfolds the ledger oracle, the query, the program's
decoding and every instruction the operations emit, with the given facts. -/

syntax (name := vmSimp) "vm_simp" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| vm_simp $[ [$hs,*] ]?) => do
    let hs : Array (Lean.TSyntax `Lean.Parser.Tactic.simpLemma) := match hs with
      | some hs => hs.getElems
      | none => #[]
    `(tactic| simp [ledgerOracle, Op.toR, AV.ofAligned, query, LedgerState.vm, VmState.init, runR, ROp.exec,
      ROp.stackReq, VmState.push, VmState.pop, VmState.popCell, VmState.popU64, VmState.popBool, VmState.pushNew,
      idxWalk, idxOne, insLoop, Cache.visit, CTree.visit, Cache.get, CTree.get, Cache.contains, CTree.contains,
      Cache.keyFor, insCache, assocGet, assocSet, AV.toU8, AV.toU64, SV.asCell, maxStackHeight, popeqAligns,
      CKey.push, readBack_nil, $hs,*])

end Damp.Ledger
