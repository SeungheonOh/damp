/-
What the ledger-level optimizer (`Damp/Optimize/LedgerReuse.lean`) needs to
know about the VM model, for any root hook `H`:

* `ledgerOracle_read`: a *plain read* `dup n; idx ci false path; popeq c a`
  (`n ≤ 2`: the contract state, the effects or the call context; the shape of
  `Cell.read`, `Counter.read`, the kernel's context reads; a cached `idx`
  only on the effects or the call context, whose cache is full) on a well-formed
  state answers `readSpec n path a q` and leaves the state exactly as it was.
  The answer is a function of the walked value only: of the contract state for
  `n = 0`, of the call context for `n = 2`.
* `ledgerOracle_context`: no successful request changes the call context.
* `ledgerOracle_cellWrite_read`: after a successful *cell write*
  `push false k; push true v; ins false 1`, a plain read of the contract state
  along `[k]` answers what `v` holds, read back under the read's alignment.
-/
import Damp.Proofs.Ledger.OptEffects

namespace Damp.Ledger
open Damp.Impact

set_option linter.unusedSimpArgs false

/-! ## Walking a state value -/

/-- One step of `idx` (`idxOne` without the cache): the value below `v` at `key`. -/
def svStep (v : SV) (key : AV) : Option SV :=
  match v with
  | .array es => do
      let i ← key.toU8
      es[i]?
  | .map m => some ((assocGet key m).getD .null)
  | .bmt h leaves => do
      let i ← key.toU64
      if h < 64 ∧ 2 ^ h ≤ i then none
      else some (match assocGet i leaves with
        | some hash => .cell (AV.ofHash hash)
        | none => .null)
  | _ => none

/-- `idx` along a path of literal keys, without the cache. -/
def svWalk : SV → List AV → Option SV
  | v, [] => some v
  | v, k :: ks => do
      let w ← svStep v k
      svWalk w ks

/-- A literal key as `Op::Idx` turns it into a stack entry. -/
def keyEntry (k : AV) : Entry := { val := .cell k, strong := false, key := none }

theorem idxOne_uncached (cache : Cache) (curr : Entry) (k : AV) :
    idxOne cache curr k false =
      (svStep curr.val k).map fun res =>
        ((cache.visit (curr.key.push k)).1, { val := res, strong := curr.strong, key := curr.key.push k }) := by
  unfold idxOne svStep
  cases curr.val <;> simp
  · congr 1; funext i; simp only [Function.comp]; cases _ : (_ : List SV)[i]? <;> rfl
  · congr 1; funext i; simp only [Function.comp]; split <;> rfl

/-- An uncached walk that does not push the path fails exactly when the value
    walk does, and otherwise pushes one entry holding the value reached,
    leaving the rest of the stack and the reads alone. -/
theorem idxWalk_spec : ∀ (keys : List AV) (s : VmState) (curr : Entry),
    (svWalk curr.val keys = none → idxWalk false false (keys.map keyEntry) s curr = none) ∧
    (∀ v, svWalk curr.val keys = some v →
      ∃ c' e, e.val = v ∧ idxWalk false false (keys.map keyEntry) s curr = some ⟨e :: s.stack, c', s.reads⟩)
  | [], s, curr => by
      refine ⟨fun h => by simp [svWalk] at h, fun v h => ?_⟩
      simp [svWalk] at h
      exact ⟨s.cache, curr, h, by simp [idxWalk, VmState.push]⟩
  | k :: ks, s, curr => by
      cases hs : svStep curr.val k with
      | none =>
        refine ⟨fun _ => ?_, fun v h => by simp [svWalk, hs] at h⟩
        simp [idxWalk, keyEntry, SV.asCell, idxOne_uncached, hs]
      | some w =>
        have ih := idxWalk_spec ks { s with cache := (s.cache.visit (curr.key.push k)).1 }
          { val := w, strong := curr.strong, key := curr.key.push k }
        have e1 : idxWalk false false ((k :: ks).map keyEntry) s curr =
            idxWalk false false (ks.map keyEntry) { s with cache := (s.cache.visit (curr.key.push k)).1 }
              { val := w, strong := curr.strong, key := curr.key.push k } := by
          simp [idxWalk, keyEntry, SV.asCell, idxOne_uncached, hs]
        have e2 : svWalk curr.val (k :: ks) = svWalk w ks := by simp [svWalk, hs]
        rw [e1, e2]
        exact ⟨ih.1, fun v h => by
          obtain ⟨c', e, he, h'⟩ := ih.2 v h
          exact ⟨c', e, he, h'⟩⟩


/-- On a fully cached root (a weak initial value: the call context or the
    effects), a cached walk is the uncached one: every visit is a hit. -/
theorem list_set_self {α : Type} : ∀ (l : List α) (i : Nat) (x : α), l[i]? = some x → l.set i x = l
  | [], _, _, h => by simp at h
  | y :: ys, 0, x, h => by simp at h; subst h; rfl
  | y :: ys, i + 1, x, h => by
      simp only [List.set_cons_succ, List.cons.injEq, true_and]
      exact list_set_self ys i x (by simpa using h)

theorem idxOne_full (cache : Cache) (curr : Entry) (k : AV) (i : Nat) (pth : List AV)
    (hk : curr.key = some (i, pth)) (hc : cache[i]? = some .full) :
    cache.visit (curr.key.push k) = (cache, true) ∧ idxOne cache curr k true = idxOne cache curr k false := by
  have hv : cache.visit (curr.key.push k) = (cache, true) := by
    rw [hk]; simp [CKey.push, Cache.visit, hc, CTree.visit, list_set_self cache i .full hc]
  refine ⟨hv, ?_⟩
  simp only [idxOne, hv]
  rfl

/-- On a fully cached root (a weak initial value: the call context or the
    effects), a cached walk is the uncached one: every visit is a hit. -/
theorem idxWalk_cached_eq : ∀ (keys : List AV) (s : VmState) (curr : Entry) (i : Nat) (pth : List AV),
    curr.key = some (i, pth) → s.cache[i]? = some .full →
    idxWalk true false (keys.map keyEntry) s curr = idxWalk false false (keys.map keyEntry) s curr
  | [], s, curr, _, _, _, _ => rfl
  | k :: ks, s, curr, i, pth, hk, hc => by
      obtain ⟨hv, h1⟩ := idxOne_full s.cache curr k i pth hk hc
      simp only [List.map_cons, idxWalk, keyEntry, SV.asCell, Option.bind_eq_bind, Option.bind_some,
        Bool.false_eq_true, if_false, ite_false, h1]
      rw [idxOne_uncached, hv]
      cases svStep curr.val k with
      | none => rfl
      | some w =>
        simp only [Option.map_some, Option.bind_some]
        apply idxWalk_cached_eq ks _ _ i (pth ++ [k])
        · simp [hk, CKey.push]
        · exact hc

/-! ## The ledger state's three initial values -/

/-- The initial stack value `n` (top first): the contract state, the effects, the call context. -/
def LedgerState.comp (q : LedgerState) : Nat → SV
  | 0 => q.state
  | 1 => q.effects
  | _ => q.context

/-- What a plain read `dup n; idx false false path; popeq c a` answers. -/
def readSpec (n : Nat) (path : List (Aligned Fr)) (a : List Zkir.AlignAtom) (q : LedgerState) :
    Option (List Fr) := do
  let keys ← path.mapM AV.ofAligned
  let v ← svWalk (q.comp n) keys
  let w ← v.asCell
  fieldsOf a w.atoms

/-- The program of a plain read. -/
def readOps (n : Nat) (path : List (Aligned Fr)) (ci c : Bool) (a : List Zkir.AlignAtom) : List (Op Fr) :=
  [.dup n, .idx ci false path, .popeq c a []]

theorem refine_values (keys : List AV) (f : List Entry × List Entry → Key → List Entry × List Entry)
    (hf : ∀ acc v, f acc (.value v) = (acc.1 ++ [keyEntry v], acc.2)) :
    ((keys.map Key.value).foldl f ([], [])).1 = keys.map keyEntry := by
  suffices h : ∀ (pre : List Entry), (keys.map Key.value).foldl f (pre, []) = (pre ++ keys.map keyEntry, []) by
    simp [h []]
  induction keys with
  | nil => intro pre; simp
  | cons k ks ih => intro pre; simp [hf, ih]

/-- The initial stack of a query, top first. -/
def initStack (q : LedgerState) : List Entry :=
  [⟨q.state, true, some (2, [])⟩, ⟨q.effects, false, some (1, [])⟩, ⟨q.context, false, some (0, [])⟩]

theorem vm_eq (q : LedgerState) : q.vm = ⟨initStack q, [.full, .full, .part []], []⟩ := by
  simp [LedgerState.vm, VmState.init, initStack]

theorem read_core (H : Hooks) (n : Nat) (hn : n ≤ 2) (curr : Entry) (hget : (initStack q)[n]? = some curr)
    (hcv : curr.val = q.comp n) (keys : List AV) (ci c : Bool) (a : List Zkir.AlignAtom)
    (hci : ci = true → ∃ i, curr.key = some (i, []) ∧ ([.full, .full, .part []] : Cache)[i]? = some .full)
    (hwf : decodeEffects q.effects = some q.effects) :
    ((query H [.dup n, .idx ci false (keys.map Key.value), .popeq c] q).bind fun r =>
        (readBack (popeqAligns [.dup n, .idx ci false [], .popeq c a []]) r.1).bind fun vals => some (vals, r.2)) =
      ((svWalk (q.comp n) keys).bind fun v => v.asCell.bind fun w => fieldsOf a w.atoms).map fun ys => (ys, q) := by
  have hrun := idxWalk_spec keys ⟨initStack q, [.full, .full, .part []], []⟩ curr
  rw [hcv] at hrun
  have hlen : (initStack q).length = 3 := rfl
  have hdup : ROp.exec H ⟨initStack q, [.full, .full, .part []], []⟩ (.dup n) =
      some (⟨curr :: initStack q, [.full, .full, .part []], []⟩, 0) := by
    simp only [ROp.exec, ROp.stackReq, hlen, hget, VmState.push]
    simp; omega
  have hidx : ROp.exec H ⟨curr :: initStack q, [.full, .full, .part []], []⟩ (.idx ci false (keys.map Key.value)) =
      (idxWalk false false (keys.map keyEntry) ⟨initStack q, [.full, .full, .part []], []⟩ curr).map fun s => (s, 0) := by
    have hw : idxWalk ci false (keys.map keyEntry) ⟨initStack q, [.full, .full, .part []], []⟩ curr =
        idxWalk false false (keys.map keyEntry) ⟨initStack q, [.full, .full, .part []], []⟩ curr := by
      cases ci with
      | false => rfl
      | true =>
        obtain ⟨i, hk, hc⟩ := hci rfl
        exact idxWalk_cached_eq keys _ curr i [] hk hc
    rw [← hw]
    have hfalse : ∀ l : List AV, l.filter (fun _ => false) = [] := by
      intro l; induction l with
      | nil => rfl
      | cons x xs ih => simp [List.filter, ih]
    simp [ROp.exec, ROp.stackReq, List.filter_map, Function.comp_def, VmState.pop, hfalse]
    rw [refine_values keys _ (fun _ _ => rfl)]
    cases idxWalk ci false (keys.map keyEntry) ⟨initStack q, [.full, .full, .part []], []⟩ curr <;> rfl
  simp only [query, vm_eq]
  cases hw : svWalk (q.comp n) keys with
  | none =>
    have := hrun.1 hw
    simp [runR, hdup, hidx, this, maxStackHeight, hlen]
  | some v =>
    obtain ⟨c', e, he, hiw⟩ := hrun.2 v hw
    have hpop : ROp.exec H ⟨e :: initStack q, c', []⟩ (.popeq c) =
        (v.asCell).map fun w => (⟨initStack q, c', [w]⟩, 0) := by
      simp [ROp.exec, ROp.stackReq, VmState.popCell, VmState.pop, he, initStack]
      cases v.asCell <;> rfl
    have hr : runR H [.dup n, .idx ci false (keys.map Key.value), .popeq c] ⟨initStack q, [.full, .full, .part []], []⟩ =
        (v.asCell).map fun w => ⟨initStack q, c', [w]⟩ := by
      simp [runR, hdup, hidx, hiw, hpop, maxStackHeight, hlen]
      cases v.asCell <;> rfl
    rw [hr]
    cases hv : v.asCell with
    | none => simp [hv]
    | some w =>
      simp [initStack, hwf, popeqAligns, readBack_cons, readBack_nil, hv]
      cases hf : fieldsOf a w.atoms <;> simp [hf]

/-- A plain read on a well-formed state: it answers `readSpec` and changes nothing. -/
theorem ledgerOracle_read (H : Hooks) (n : Nat) (hn : n ≤ 2) (path : List (Aligned Fr)) (ci c : Bool)
    (hci : ci = false ∨ 1 ≤ n) (a : List Zkir.AlignAtom) (q : LedgerState) (hwf : q.WF) :
    ledgerOracle H (readOps n path ci c a) q = (readSpec n path a q).map fun ys => (ys, q) := by
  unfold readSpec
  cases hk : path.mapM AV.ofAligned with
  | none =>
    simp [ledgerOracle, readOps, Op.toR, hk]
  | some keys =>
    have hdec : (readOps n path ci c a).mapM Op.toR =
        some [.dup n, .idx ci false (keys.map Key.value), .popeq c] := by
      simp [readOps, Op.toR, hk]
    have hal : popeqAligns (readOps n path ci c a) = popeqAligns [.dup n, .idx ci false [], .popeq c a []] := rfl
    simp only [ledgerOracle, hdec, Option.bind_eq_bind, Option.bind_some, hal]
    rw [LedgerState.WF] at hwf
    rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2) with rfl | rfl | rfl
    · exact read_core H 0 hn _ rfl rfl keys ci c a
        (fun h => by subst h; simp at hci) hwf
    · exact read_core H 1 hn _ rfl rfl keys ci c a (fun _ => ⟨1, rfl, rfl⟩) hwf
    · exact read_core H 2 hn _ rfl rfl keys ci c a (fun _ => ⟨0, rfl, rfl⟩) hwf

/-- A plain read's answer depends on the walked value only. -/
theorem readSpec_congr {n : Nat} {path : List (Aligned Fr)} {a : List Zkir.AlignAtom} {q q' : LedgerState}
    (h : q.comp n = q'.comp n) : readSpec n path a q = readSpec n path a q' := by
  simp [readSpec, h]

/-! ## Requests keep the call context -/

theorem query_context {H : Hooks} {rops : List ROp} {q q' : LedgerState} {reads : List AV}
    (h : query H rops q = some (reads, q')) : q'.context = q.context := by
  unfold query at h
  cases hr : runR H rops q.vm with
  | none => simp [hr] at h
  | some s =>
    simp only [hr, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · split at h
      · cases hd : decodeEffects _ with
        | none => rw [hd] at h; simp at h
        | some eff =>
          rw [hd] at h
          simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          rfl
      · simp at h
    · simp at h

/-- No successful request changes the call context. -/
theorem ledgerOracle_context {H : Hooks} {ops : List (Op Fr)} {q q' : LedgerState} {xs : List Fr}
    (h : ledgerOracle H ops q = some (xs, q')) : q'.context = q.context := by
  unfold ledgerOracle at h
  cases hr : ops.mapM Op.toR with
  | none => simp [hr] at h
  | some rops =>
    cases hq : query H rops q with
    | none => simp [hr, hq] at h
    | some r =>
      obtain ⟨reads, q₁⟩ := r
      cases hb : readBack (popeqAligns ops) reads with
      | none => simp [hr, hq, hb] at h
      | some v =>
        simp [hr, hq, hb] at h
        obtain ⟨_, rfl⟩ := h
        exact query_context hq

end Damp.Ledger

namespace Damp.Ledger
open Damp.Impact

theorem assocGet_set_self' {κ ν : Type} [DecidableEq κ] (k : κ) (v : ν) :
    ∀ m : List (κ × ν), assocGet k (assocSet k v m) = some v
  | [] => by simp [assocSet, assocGet]
  | (k', v') :: rest => by
      by_cases h : k' = k
      · simp [assocSet, assocGet, h]
      · simp [assocSet, assocGet, h, assocGet_set_self' k v rest]

/-- The program of a cell write. -/
def writeOps (k v : Aligned Fr) : List (Op Fr) := [.push false k, .push true v, .ins false 1]

/-- After a successful cell write of `v` at `k`, a plain read of the contract
    state along `[k]` answers what `v` holds, under the read's alignment. -/
theorem ledgerOracle_cellWrite_read {H : Hooks} {k v : Aligned Fr} {q q' : LedgerState} {xs : List Fr}
    (h : ledgerOracle H (writeOps k v) q = some (xs, q')) (a : List Zkir.AlignAtom) :
    readSpec 0 [k] a q' = (AV.ofAligned v).bind fun w => fieldsOf a w.atoms := by
  unfold ledgerOracle at h
  cases hk : AV.ofAligned k with
  | none => simp [writeOps, Op.toR, hk] at h
  | some kv =>
    cases hv : AV.ofAligned v with
    | none => simp [writeOps, Op.toR, hk, hv] at h
    | some vv =>
      simp only [readSpec, List.mapM_cons, List.mapM_nil, hk, Option.bind_eq_bind, Option.bind_some]
      simp [writeOps, Op.toR, hk, hv, query, vm_eq, initStack, runR, ROp.exec, ROp.stackReq, VmState.push,
        VmState.pop, insLoop, Cache.get, CTree.get, Cache.keyFor, insCache, SV.asCell, maxStackHeight,
        popeqAligns, readBack_nil, CKey.push, Cache.contains, CTree.contains] at h
      have e1 : (((pure [] : Option (List AV)).bind fun l => pure (kv :: l)) : Option (List AV)) = some [kv] := rfl
      rw [e1]; simp only [Option.bind_some, svWalk, LedgerState.comp]
      cases hs : q.state with
      | array es =>
        cases hi : kv.toU8 with
        | none => simp [hs, hi] at h
        | some i =>
          by_cases hl : i < es.length
          · simp [hs, hi, hl] at h
            cases hd : decodeEffects q.effects with
            | none => simp [hd] at h
            | some eff =>
              simp [hd] at h
              obtain ⟨_, rfl⟩ := h
              simp [svStep, hi, hl, SV.asCell]
          · simp [hs, hi, hl] at h
      | map m =>
        simp [hs] at h
        cases hd : decodeEffects q.effects with
        | none => simp [hd] at h
        | some eff =>
          simp [hd] at h
          obtain ⟨_, rfl⟩ := h
          simp [svStep, assocGet_set_self', SV.asCell]
      | bmt ht leaves =>
        cases hi : kv.toU64 with
        | none => simp [hs, hi] at h
        | some i =>
          by_cases hr : ht < 64 ∧ 2 ^ ht ≤ i
          · simp [hs, hi, hr] at h
          · cases hh : vv.toHash with
            | none => simp [hs, hi, hr, hh] at h
            | some x =>
              simp [hs, hi, hr, hh] at h
              cases hd : decodeEffects q.effects with
              | none => simp [hd] at h
              | some eff =>
                simp [hd] at h
                obtain ⟨_, rfl⟩ := h
                have hat : vv.atoms = [x] := by
                  unfold AV.toHash at hh; split at hh
                  · rename_i y hy; by_cases hy' : y < 2 ^ 256
                    · simp [hy'] at hh; subst hh; exact hy
                    · simp [hy'] at hh
                  · simp at hh
                simp [svStep, hi, hr, assocGet_set_self', SV.asCell, AV.ofHash, hat]
      | _ => simp [hs] at h


/-- What a cell write does to the contract state: `ins` of the cell at `k`. -/
def setCell (st : SV) (k v : AV) : Option SV :=
  match st with
  | .array es => do
      let i ← k.toU8
      if i < es.length then some (.array (es.set i (.cell v))) else none
  | .map m => some (.map (assocSet k (.cell v) m))
  | .bmt h leaves => do
      let i ← k.toU64
      if h < 64 ∧ 2 ^ h ≤ i then none
      else do
        let hash ← v.toHash
        some (.bmt h (assocSet i hash leaves))
  | _ => none

/-- A cell write, as a function of the state. -/
theorem ledgerOracle_cellWrite (H : Hooks) (k v : Aligned Fr) (q : LedgerState) :
    ledgerOracle H (writeOps k v) q =
      (do
        let kv ← AV.ofAligned k
        let vv ← AV.ofAligned v
        let st ← setCell q.state kv vv
        let eff ← decodeEffects q.effects
        pure ([], { q with state := st, effects := eff })) := by
  unfold ledgerOracle
  cases hk : AV.ofAligned k with
  | none => simp [writeOps, Op.toR, hk]
  | some kv =>
    cases hv : AV.ofAligned v with
    | none => simp [writeOps, Op.toR, hk, hv]
    | some vv =>
      simp [writeOps, Op.toR, hk, hv, query, vm_eq, initStack, runR, ROp.exec, ROp.stackReq, VmState.push,
        VmState.pop, insLoop, Cache.get, CTree.get, Cache.keyFor, insCache, SV.asCell, maxStackHeight,
        popeqAligns, CKey.push, Cache.contains, setCell, readBack_nil]
      cases hs : q.state with
      | array es =>
        cases hi : kv.toU8 with
        | none => simp [hi]
        | some i =>
          by_cases hl : i < es.length
          · simp [hi, hl]; cases decodeEffects q.effects <;> simp [readBack_nil]
          · simp [hi, hl]
      | map m => simp; cases decodeEffects q.effects <;> simp [readBack_nil]
      | bmt ht leaves =>
        cases hi : kv.toU64 with
        | none => simp [hi]
        | some i =>
          by_cases hr : ht < 64 ∧ 2 ^ ht ≤ i
          · simp [hi, hr]
          · cases hh : vv.toHash with
            | none => simp [hi, hr, hh]
            | some x => simp [hi, hr, hh]; cases decodeEffects q.effects <;> simp [readBack_nil]
      | null => simp
      | cell c => simp

theorem assocSet_assocSet {κ ν : Type} [DecidableEq κ] (k : κ) (a b : ν) :
    ∀ m : List (κ × ν), assocSet k b (assocSet k a m) = assocSet k b m
  | [] => by simp [assocSet]
  | (k', v') :: rest => by
      by_cases h : k' = k
      · simp [assocSet, h]
      · simp [assocSet, h, assocSet_assocSet k a b rest]

/-- Writing twice at one key is writing the second value. -/
theorem setCell_setCell {st st₁ : SV} {k a b : AV} (h : setCell st k a = some st₁) :
    setCell st₁ k b = setCell st k b := by
  cases st with
  | array es =>
    simp only [setCell] at h ⊢
    cases hi : k.toU8 with
    | none => simp [hi] at h
    | some i =>
      by_cases hl : i < es.length
      · simp [hi, hl] at h; subst h; simp [setCell, hi, hl]
      · simp [hi, hl] at h
  | map m => simp only [setCell, Option.some.injEq] at h; subst h; simp [setCell, assocSet_assocSet]
  | bmt ht leaves =>
    simp only [setCell] at h ⊢
    cases hi : k.toU64 with
    | none => simp [hi] at h
    | some i =>
      by_cases hr : ht < 64 ∧ 2 ^ ht ≤ i
      · simp [hi, hr] at h
      · cases ha : a.toHash with
        | none => simp [hi, hr, ha] at h
        | some x =>
          simp [hi, hr, ha] at h; subst h
          simp [setCell, hi, hr]
          cases b.toHash <;> simp [assocSet_assocSet]
  | null => simp [setCell] at h
  | cell c => simp [setCell] at h

/-- A write that fails on the state's shape fails for any hashable value. -/
theorem setCell_none {st : SV} {k a b : AV} (h : setCell st k a = none) (ha : a.toHash.isSome) :
    setCell st k b = none := by
  cases st with
  | array es =>
    simp only [setCell] at h ⊢
    cases hi : k.toU8 with
    | none => simp [hi]
    | some i => by_cases hl : i < es.length <;> simp_all
  | map m => simp [setCell] at h
  | bmt ht leaves =>
    simp only [setCell] at h ⊢
    cases hi : k.toU64 with
    | none => simp [hi]
    | some i =>
      by_cases hr : ht < 64 ∧ 2 ^ ht ≤ i
      · simp [hi, hr]
      · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp ha
        simp [hi, hr, hx] at h
  | null => rfl
  | cell c => rfl

/-- A cell write followed by a cell write at the same key leaves what the
    second alone leaves; and if the first fails, the second fails on the
    state the first saw. The first value must be hashable (one atom of at
    most 32 bytes: a field element is). -/
theorem ledgerOracle_cellWrite_twice (H : Hooks) (k v₁ v₂ : Aligned Fr) (vv₁ : AV) (q : LedgerState)
    (hv₁ : AV.ofAligned v₁ = some vv₁) (hh : vv₁.toHash.isSome) :
    (ledgerOracle H (writeOps k v₁) q).bind (fun r => ledgerOracle H (writeOps k v₂) r.2) =
      ledgerOracle H (writeOps k v₂) q := by
  simp only [ledgerOracle_cellWrite, Option.bind_eq_bind, hv₁, Option.bind_some]
  cases hk : AV.ofAligned k with
  | none => simp
  | some kv =>
    simp only [Option.bind_some]
    cases hs : setCell q.state kv vv₁ with
    | none =>
      simp only [Option.bind_none]
      cases AV.ofAligned v₂ with
      | none => rfl
      | some vv₂ => simp [setCell_none hs hh]
    | some st₁ =>
      simp only [Option.bind_some]
      cases hd : decodeEffects q.effects with
      | none =>
        simp only [Option.bind_none]
        cases AV.ofAligned v₂ with
        | none => rfl
        | some vv₂ => simp
      | some eff =>
        simp only [Option.bind_some, Option.pure_def]
        cases AV.ofAligned v₂ with
        | none => rfl
        | some vv₂ =>
          simp only [Option.bind_some, setCell_setCell hs, decodeEffects_idem hd]

end Damp.Ledger
