/-
The frame analysis of `Damp/Optimize/LedgerFrame.lean` is sound against the
VM model: `frame_ledgerOracle`. If `frameKeeps π ops`, then for any operand
values (`Exec.request p env ops = some req`) and any ledger state, a
successful `ledgerOracle H req q = some (xs, q')` leaves
`svWalk q'.state π = svWalk q.state π`: the contract state's part at the
constant path `π` is unchanged.

The proof follows the abstract interpretation instruction by instruction
(`fstep_sound`): every stack entry satisfies what its tag claims
(`FTag.Ok`, `Agrees`), every instruction keeps that, and the walk and the
writes of `idx`, `ins` and `rem` are related to `svStep` (`insNext_ne`,
`insNext_same`, `remNext_ne`).
-/
import Damp.Proofs.Ledger.OptVm
import Damp.Optimize.LedgerFrame

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Damp.Ledger
open Damp.IR Damp.Impact
open Damp.Zkir (Prims)

/-! ## What the tags claim -/

/-- What a tag claims of a stack entry, `T` being what the initial contract
    state holds at `π`. -/
def _root_.Damp.IR.FTag.Ok (π : List AV) (T : Option SV) : FTag → Entry → Prop
  | .pre d, e => d < π.length ∧ svWalk e.val (π.drop d) = T
  | .key k, e => e.val = .cell k
  | .other, _ => True

/-- Each tag holds of the entry at its position; same length. -/
def Agrees (π : List AV) (T : Option SV) : List FTag → List Entry → Prop
  | [], [] => True
  | t :: ts, e :: es => t.Ok π T e ∧ Agrees π T ts es
  | _, _ => False

section Agrees
variable {π : List AV} {T : Option SV}

theorem Agrees.length : ∀ {ts : List FTag} {es : List Entry}, Agrees π T ts es → ts.length = es.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp only [List.length_cons, Agrees.length h.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem Agrees.drop : ∀ (n : Nat) {ts : List FTag} {es : List Entry}, Agrees π T ts es →
    Agrees π T (ts.drop n) (es.drop n)
  | 0, _, _, h => h
  | _ + 1, [], [], _ => trivial
  | n + 1, _ :: _, _ :: _, h => Agrees.drop n h.2
  | _ + 1, [], _ :: _, h => h.elim
  | _ + 1, _ :: _, [], h => h.elim

theorem Agrees.get : ∀ (n : Nat) {ts : List FTag} {es : List Entry} {t : FTag}, Agrees π T ts es →
    ts[n]? = some t → ∃ e, es[n]? = some e ∧ t.Ok π T e
  | _, [], [], _, _, h => by simp at h
  | 0, t :: ts, e :: es, t', h, ht => by simp at ht; subst ht; exact ⟨e, rfl, h.1⟩
  | n + 1, t :: ts, e :: es, t', h, ht => Agrees.get n h.2 (by simpa using ht)
  | _, [], _ :: _, _, h, _ => h.elim
  | _, _ :: _, [], _, h, _ => h.elim

theorem Agrees.set : ∀ (n : Nat) {ts : List FTag} {es : List Entry} {t : FTag} {e : Entry}, Agrees π T ts es →
    t.Ok π T e → Agrees π T (ts.set n t) (es.set n e)
  | _, [], [], _, _, _, _ => trivial
  | 0, _ :: _, _ :: _, _, _, h, he => ⟨he, h.2⟩
  | n + 1, _ :: _, _ :: _, _, _, h, he => ⟨h.1, Agrees.set n h.2 he⟩
  | _, [], _ :: _, _, _, h, _ => h.elim
  | _, _ :: _, [], _, _, h, _ => h.elim

theorem Agrees.append : ∀ {ts ts' : List FTag} {es es' : List Entry}, Agrees π T ts es → Agrees π T ts' es' →
    Agrees π T (ts ++ ts') (es ++ es')
  | [], _, [], _, _, h => h
  | _ :: _, _, _ :: _, _, h, h' => ⟨h.1, Agrees.append h.2 h'⟩
  | [], _, _ :: _, _, h, _ => h.elim
  | _ :: _, _, [], _, h, _ => h.elim

theorem Agrees.cons_other {ts : List FTag} {es : List Entry} (h : Agrees π T ts es) (e : Entry) :
    Agrees π T (.other :: ts) (e :: es) := ⟨trivial, h⟩

end Agrees

/-! ## The VM's walks and writes -/

/-- What `ins` makes of container `cv` with `x` put at `k` (the `match` of `insLoop`). -/
def insNext (cv : SV) (k : AV) (x : SV) : Option SV :=
  match cv with
  | .array es => do
      let i ← k.toU8
      if i < es.length then some (SV.array (es.set i x)) else none
  | .map m => some (SV.map (assocSet k x m))
  | .bmt h leaves => do
      let i ← k.toU64
      if h < 64 ∧ 2 ^ h ≤ i then none
      else do
        let c ← x.asCell
        let hash ← c.toHash
        some (SV.bmt h (assocSet i hash leaves))
  | _ => none

/-- What `rem` makes of container `cv` without key `k`. -/
def remNext (cv : SV) (k : AV) : Option SV :=
  match cv with
  | .map m => some (SV.map (assocErase k m))
  | .bmt h leaves => do
      let i ← k.toU64
      if h < 64 ∧ 2 ^ h ≤ i then none else some (SV.bmt h (assocSet i 0 leaves))
  | _ => none

theorem assocGet_assocSet_ne' {κ ν : Type} [DecidableEq κ] {k j : κ} (v : ν) (h : k ≠ j) :
    ∀ m : List (κ × ν), assocGet j (assocSet k v m) = assocGet j m
  | [] => by simp [assocSet, assocGet, h]
  | (k', v') :: rest => by
      by_cases hk : k' = k
      · subst hk; simp [assocSet, assocGet, h]
      · simp only [assocSet, hk, ite_false, assocGet]
        split
        · rfl
        · exact assocGet_assocSet_ne' v h rest

theorem assocGet_assocErase_ne' {κ ν : Type} [DecidableEq κ] {k j : κ} (h : k ≠ j) :
    ∀ m : List (κ × ν), assocGet j (assocErase k m) = assocGet j m
  | [] => rfl
  | (k', v') :: rest => by
      by_cases hk : k' = k
      · subst hk; simp [assocErase, assocGet, h]
      · simp only [assocErase, hk, ite_false, assocGet]
        split
        · rfl
        · exact assocGet_assocErase_ne' h rest

theorem toU8_ne {k j : AV} (h : k.atoms ≠ j.atoms) {i i' : Nat} (hi : k.toU8 = some i) (hj : j.toU8 = some i') :
    i ≠ i' := by
  unfold AV.toU8 at hi hj
  split at hi <;> split at hj <;> simp_all

theorem toU64_ne {k j : AV} (h : k.atoms ≠ j.atoms) {i i' : Nat} (hi : k.toU64 = some i) (hj : j.toU64 = some i') :
    i ≠ i' := by
  unfold AV.toU64 at hi hj
  split at hi <;> split at hj <;> simp_all

theorem AV.ne_of_atoms {k j : AV} (h : k.atoms ≠ j.atoms) : k ≠ j := fun e => h (by rw [e])

/-- A write at another key leaves the entry at `j` alone. -/
theorem insNext_ne {cv : SV} {k j : AV} {x next : SV} (hkj : k.atoms ≠ j.atoms) (h : insNext cv k x = some next) :
    svStep next j = svStep cv j := by
  cases cv with
  | array es =>
    simp only [insNext] at h
    cases hi : k.toU8 with
    | none => simp [hi] at h
    | some i =>
      by_cases hl : i < es.length
      · simp [hi, hl] at h; subst h
        simp only [svStep]
        cases hj : j.toU8 with
        | none => rfl
        | some i' =>
          simp only [Option.bind_some, Option.bind_eq_bind]
          exact List.getElem?_set_ne (toU8_ne hkj hi hj)
      · simp [hi, hl] at h
  | map m =>
    simp only [insNext, Option.some.injEq] at h; subst h
    simp [svStep, assocGet_assocSet_ne' x (AV.ne_of_atoms hkj)]
  | bmt ht leaves =>
    simp only [insNext] at h
    cases hi : k.toU64 with
    | none => simp [hi] at h
    | some i =>
      by_cases hr : ht < 64 ∧ 2 ^ ht ≤ i
      · simp [hi, hr] at h
      · cases hc : x.asCell with
        | none => simp [hi, hr, hc] at h
        | some c =>
          cases hh : c.toHash with
          | none => simp [hi, hr, hc, hh] at h
          | some hash =>
            simp [hi, hr, hc, hh] at h; subst h
            simp only [svStep]
            cases hj : j.toU64 with
            | none => rfl
            | some i' =>
              simp only [Option.bind_some, Option.bind_eq_bind]
              rw [assocGet_assocSet_ne' hash (toU64_ne hkj hi hj)]
  | null => simp [insNext] at h
  | cell _ => simp [insNext] at h

theorem svWalk_cell_cons (c : AV) (k : AV) (ks : List AV) : svWalk (.cell c) (k :: ks) = none := by
  simp [svWalk, svStep]

/-- A write at `j` itself: below `j` there is now what was written (for a
    nonempty rest of the path; a Merkle leaf becomes a cell, under which
    nothing is reached either way). -/
theorem insNext_same {cv : SV} {j : AV} {x next : SV} (h : insNext cv j x = some next) {r : AV} {rs : List AV} :
    svWalk next (j :: r :: rs) = svWalk x (r :: rs) := by
  cases cv with
  | array es =>
    simp only [insNext] at h
    cases hi : j.toU8 with
    | none => simp [hi] at h
    | some i =>
      by_cases hl : i < es.length
      · simp [hi, hl] at h; subst h
        simp [svWalk, svStep, hi, hl]
      · simp [hi, hl] at h
  | map m =>
    simp only [insNext, Option.some.injEq] at h; subst h
    simp [svWalk, svStep, assocGet_set_self']
  | bmt ht leaves =>
    simp only [insNext] at h
    cases hi : j.toU64 with
    | none => simp [hi] at h
    | some i =>
      by_cases hr : ht < 64 ∧ 2 ^ ht ≤ i
      · simp [hi, hr] at h
      · cases hc : x.asCell with
        | none => simp [hi, hr, hc] at h
        | some c =>
          cases hh : c.toHash with
          | none => simp [hi, hr, hc, hh] at h
          | some hash =>
            simp [hi, hr, hc, hh] at h; subst h
            have hx : x = .cell c := by cases x <;> simp_all [SV.asCell]
            subst hx
            simp [svWalk, svStep, hi, hr, assocGet_set_self', svWalk_cell_cons]
  | null => simp [insNext] at h
  | cell _ => simp [insNext] at h

theorem remNext_ne {cv : SV} {k j : AV} {next : SV} (hkj : k.atoms ≠ j.atoms) (h : remNext cv k = some next) :
    svStep next j = svStep cv j := by
  cases cv with
  | map m =>
    simp only [remNext, Option.some.injEq] at h; subst h
    simp [svStep, assocGet_assocErase_ne' (AV.ne_of_atoms hkj)]
  | bmt ht leaves =>
    simp only [remNext] at h
    cases hi : k.toU64 with
    | none => simp [hi] at h
    | some i =>
      by_cases hr : ht < 64 ∧ 2 ^ ht ≤ i
      · simp [hi, hr] at h
      · simp [hi, hr] at h; subst h
        simp only [svStep]
        cases hj : j.toU64 with
        | none => rfl
        | some i' =>
          simp only [Option.bind_some, Option.bind_eq_bind]
          rw [assocGet_assocSet_ne' 0 (toU64_ne hkj hi hj)]
  | _ => simp [remNext] at h

/-- `idxOne` steps by `svStep`. -/
theorem idxOne_val {cache : Cache} {curr : Entry} {k : AV} {c : Bool} {cache' : Cache} {e : Entry}
    (h : idxOne cache curr k c = some (cache', e)) : svStep curr.val k = some e.val := by
  have h' : idxOne cache curr k false = some (cache', e) := by
    cases c with
    | false => exact h
    | true =>
      unfold idxOne at h ⊢
      simp only [Option.bind_eq_bind] at h ⊢
      split at h
      · simp at h
      · simpa using h
  rw [idxOne_uncached] at h'
  cases hs : svStep curr.val k <;> simp [hs] at h'
  obtain ⟨_, rfl⟩ := h'; rfl

/-! ## What each instruction does to the stack -/

theorem pop_stack {s : VmState} {e : Entry} {s' : VmState} (h : s.pop = some (e, s')) :
    s.stack = e :: s'.stack ∧ s'.cache = s.cache := by
  unfold VmState.pop at h
  split at h
  · rename_i e' es hs; simp at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨hs, rfl⟩
  · simp at h
theorem popCell_stack {s : VmState} {v : AV} {s' : VmState} (h : s.popCell = some (v, s')) :
    ∃ e, s.stack = e :: s'.stack := by
  simp only [VmState.popCell, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨e, s1⟩, h1, w, _, h⟩ := h
  simp at h; obtain ⟨_, rfl⟩ := h
  exact ⟨e, (pop_stack h1).1⟩
theorem popU64_stack {s : VmState} {v : Nat} {s' : VmState} (h : s.popU64 = some (v, s')) :
    ∃ e, s.stack = e :: s'.stack := by
  simp only [VmState.popU64, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨w, s1⟩, h1, x, _, h⟩ := h
  simp at h; obtain ⟨_, rfl⟩ := h
  exact popCell_stack h1
theorem popBool_stack {s : VmState} {v : Bool} {s' : VmState} (h : s.popBool = some (v, s')) :
    ∃ e, s.stack = e :: s'.stack := by
  simp only [VmState.popBool, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨w, s1⟩, h1, x, _, h⟩ := h
  simp at h; obtain ⟨_, rfl⟩ := h
  exact popCell_stack h1



theorem bind_some_elim {α β : Type} {o : Option α} {f : α → Option β} {r : β} (h : o.bind f = some r) :
    ∃ a, o = some a ∧ f a = some r := Option.bind_eq_some_iff.mp h

theorem stack_two {s s1 s2 : VmState} {e1 e2 : Entry} (h1 : s.stack = e1 :: s1.stack) (h2 : s1.stack = e2 :: s2.stack)
    (x : Entry) : x :: s2.stack = x :: s.stack.drop 2 := by simp [h1, h2]
theorem stack_one {s s1 : VmState} {e1 : Entry} (h1 : s.stack = e1 :: s1.stack)
    (x : Entry) : x :: s1.stack = x :: s.stack.drop 1 := by simp [h1]

theorem exec_lt (H : Hooks) {s s' : VmState} {k : Nat} (h : ROp.exec H s .lt = some (s', k)) :
    k = 0 ∧ ∃ x, s'.stack = x :: s.stack.drop 2 := by
  simp only [ROp.exec, Option.bind_eq_bind] at h
  split at h; · simp at h
  obtain ⟨⟨b, s1⟩, h1, h⟩ := bind_some_elim h
  obtain ⟨⟨a, s2⟩, h2, h⟩ := bind_some_elim h
  simp [VmState.pushNew, VmState.push] at h; obtain ⟨rfl, rfl⟩ := h
  obtain ⟨e1, he1⟩ := popU64_stack h1; obtain ⟨e2, he2⟩ := popU64_stack h2
  exact ⟨rfl, _, stack_two he1 he2 _⟩

theorem exec_add (H : Hooks) {s s' : VmState} {k : Nat} (h : ROp.exec H s .add = some (s', k)) :
    k = 0 ∧ ∃ x, s'.stack = x :: s.stack.drop 2 := by
  simp only [ROp.exec, Option.bind_eq_bind] at h
  split at h; · simp at h
  obtain ⟨⟨b, s1⟩, h1, h⟩ := bind_some_elim h
  obtain ⟨⟨a, s2⟩, h2, h⟩ := bind_some_elim h
  split at h
  · simp [VmState.pushNew, VmState.push] at h; obtain ⟨rfl, rfl⟩ := h
    obtain ⟨e1, he1⟩ := popU64_stack h1; obtain ⟨e2, he2⟩ := popU64_stack h2
    exact ⟨rfl, _, stack_two he1 he2 _⟩
  · simp at h

theorem exec_sub (H : Hooks) {s s' : VmState} {k : Nat} (h : ROp.exec H s .sub = some (s', k)) :
    k = 0 ∧ ∃ x, s'.stack = x :: s.stack.drop 2 := by
  simp only [ROp.exec, Option.bind_eq_bind] at h
  split at h; · simp at h
  obtain ⟨⟨b, s1⟩, h1, h⟩ := bind_some_elim h
  obtain ⟨⟨a, s2⟩, h2, h⟩ := bind_some_elim h
  split at h
  · simp [VmState.pushNew, VmState.push] at h; obtain ⟨rfl, rfl⟩ := h
    obtain ⟨e1, he1⟩ := popU64_stack h1; obtain ⟨e2, he2⟩ := popU64_stack h2
    exact ⟨rfl, _, stack_two he1 he2 _⟩
  · simp at h

theorem exec_and (H : Hooks) {s s' : VmState} {k : Nat} (h : ROp.exec H s .and = some (s', k)) :
    k = 0 ∧ ∃ x, s'.stack = x :: s.stack.drop 2 := by
  simp only [ROp.exec, Option.bind_eq_bind] at h
  split at h; · simp at h
  obtain ⟨⟨b, s1⟩, h1, h⟩ := bind_some_elim h
  obtain ⟨⟨a, s2⟩, h2, h⟩ := bind_some_elim h
  simp [VmState.pushNew, VmState.push] at h; obtain ⟨rfl, rfl⟩ := h
  obtain ⟨e1, he1⟩ := popBool_stack h1; obtain ⟨e2, he2⟩ := popBool_stack h2
  exact ⟨rfl, _, stack_two he1 he2 _⟩

theorem exec_or (H : Hooks) {s s' : VmState} {k : Nat} (h : ROp.exec H s .or = some (s', k)) :
    k = 0 ∧ ∃ x, s'.stack = x :: s.stack.drop 2 := by
  simp only [ROp.exec, Option.bind_eq_bind] at h
  split at h; · simp at h
  obtain ⟨⟨b, s1⟩, h1, h⟩ := bind_some_elim h
  obtain ⟨⟨a, s2⟩, h2, h⟩ := bind_some_elim h
  simp [VmState.pushNew, VmState.push] at h; obtain ⟨rfl, rfl⟩ := h
  obtain ⟨e1, he1⟩ := popBool_stack h1; obtain ⟨e2, he2⟩ := popBool_stack h2
  exact ⟨rfl, _, stack_two he1 he2 _⟩

theorem exec_eq (H : Hooks) {s s' : VmState} {k : Nat} (h : ROp.exec H s .eq = some (s', k)) :
    k = 0 ∧ ∃ x, s'.stack = x :: s.stack.drop 2 := by
  simp only [ROp.exec, Option.bind_eq_bind] at h
  split at h; · simp at h
  obtain ⟨⟨b, s1⟩, h1, h⟩ := bind_some_elim h
  obtain ⟨⟨a, s2⟩, h2, h⟩ := bind_some_elim h
  obtain ⟨e1, he1⟩ := popCell_stack h1; obtain ⟨e2, he2⟩ := popCell_stack h2
  split at h <;> simp [VmState.pushNew, VmState.push] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
    exact ⟨rfl, _, stack_two he1 he2 _⟩

theorem exec_member (H : Hooks) {s s' : VmState} {k : Nat} (h : ROp.exec H s .member = some (s', k)) :
    k = 0 ∧ ∃ x, s'.stack = x :: s.stack.drop 2 := by
  simp only [ROp.exec, Option.bind_eq_bind] at h
  split at h; · simp at h
  obtain ⟨⟨b, s1⟩, h1, h⟩ := bind_some_elim h
  obtain ⟨⟨a, s2⟩, h2, h⟩ := bind_some_elim h
  obtain ⟨e1, he1⟩ := popCell_stack h1; obtain ⟨he2, _⟩ := pop_stack h2
  split at h <;> simp [VmState.pushNew, VmState.push] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
    exact ⟨rfl, _, stack_two he1 he2 _⟩

theorem exec_concat (H : Hooks) {c : Bool} {n : Nat} {s s' : VmState} {k : Nat}
    (h : ROp.exec H s (.concat c n) = some (s', k)) : k = 0 ∧ ∃ x, s'.stack = x :: s.stack.drop 2 := by
  simp only [ROp.exec, Option.bind_eq_bind] at h
  split at h; · simp at h
  split at h; · simp at h
  obtain ⟨⟨b, s1⟩, h1, h⟩ := bind_some_elim h
  obtain ⟨⟨a, s2⟩, h2, h⟩ := bind_some_elim h
  split at h
  · simp [VmState.pushNew, VmState.push] at h; obtain ⟨rfl, rfl⟩ := h
    obtain ⟨e1, he1⟩ := popCell_stack h1; obtain ⟨e2, he2⟩ := popCell_stack h2
    exact ⟨rfl, _, stack_two he1 he2 _⟩
  · simp at h

theorem exec_type (H : Hooks) {s s' : VmState} {k : Nat} (h : ROp.exec H s .type = some (s', k)) :
    k = 0 ∧ ∃ x, s'.stack = x :: s.stack.drop 1 := by
  simp only [ROp.exec, Option.bind_eq_bind] at h
  split at h; · simp at h
  obtain ⟨⟨b, s1⟩, h1, h⟩ := bind_some_elim h
  obtain ⟨he1, _⟩ := pop_stack h1
  obtain ⟨r, _, h⟩ := bind_some_elim h
  simp [VmState.pushNew, VmState.push] at h; obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, _, stack_one he1 _⟩

theorem exec_size (H : Hooks) {s s' : VmState} {k : Nat} (h : ROp.exec H s .size = some (s', k)) :
    k = 0 ∧ ∃ x, s'.stack = x :: s.stack.drop 1 := by
  simp only [ROp.exec, Option.bind_eq_bind] at h
  split at h; · simp at h
  obtain ⟨⟨b, s1⟩, h1, h⟩ := bind_some_elim h
  obtain ⟨he1, _⟩ := pop_stack h1
  split at h <;> simp [VmState.pushNew, VmState.push] at h <;> obtain ⟨rfl, rfl⟩ := h <;>
    exact ⟨rfl, _, stack_one he1 _⟩

theorem exec_root (H : Hooks) {s s' : VmState} {k : Nat} (h : ROp.exec H s .root = some (s', k)) :
    k = 0 ∧ ∃ x, s'.stack = x :: s.stack.drop 1 := by
  simp only [ROp.exec, Option.bind_eq_bind] at h
  split at h; · simp at h
  obtain ⟨⟨b, s1⟩, h1, h⟩ := bind_some_elim h
  obtain ⟨he1, _⟩ := pop_stack h1
  split at h
  · obtain ⟨r, _, h⟩ := bind_some_elim h
    simp [VmState.pushNew, VmState.push] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, _, stack_one he1 _⟩
  · simp at h

theorem exec_neg (H : Hooks) {s s' : VmState} {k : Nat} (h : ROp.exec H s .neg = some (s', k)) :
    k = 0 ∧ ∃ x, s'.stack = x :: s.stack.drop 1 := by
  simp only [ROp.exec, Option.bind_eq_bind] at h
  split at h; · simp at h
  obtain ⟨⟨b, s1⟩, h1, h⟩ := bind_some_elim h
  obtain ⟨e1, he1⟩ := popBool_stack h1
  simp [VmState.pushNew, VmState.push] at h; obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, _, stack_one he1 _⟩

theorem exec_addi (H : Hooks) {i : Nat} {s s' : VmState} {k : Nat} (h : ROp.exec H s (.addi i) = some (s', k)) :
    k = 0 ∧ ∃ x, s'.stack = x :: s.stack.drop 1 := by
  simp only [ROp.exec, Option.bind_eq_bind] at h
  split at h; · simp at h
  obtain ⟨⟨b, s1⟩, h1, h⟩ := bind_some_elim h
  obtain ⟨e1, he1⟩ := popU64_stack h1
  split at h
  · simp [VmState.pushNew, VmState.push] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, _, stack_one he1 _⟩
  · simp at h

theorem exec_subi (H : Hooks) {i : Nat} {s s' : VmState} {k : Nat} (h : ROp.exec H s (.subi i) = some (s', k)) :
    k = 0 ∧ ∃ x, s'.stack = x :: s.stack.drop 1 := by
  simp only [ROp.exec, Option.bind_eq_bind] at h
  split at h; · simp at h
  obtain ⟨⟨b, s1⟩, h1, h⟩ := bind_some_elim h
  obtain ⟨e1, he1⟩ := popU64_stack h1
  split at h
  · simp [VmState.pushNew, VmState.push] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, _, stack_one he1 _⟩
  · simp at h

theorem exec_popeq (H : Hooks) {c : Bool} {s s' : VmState} {k : Nat} (h : ROp.exec H s (.popeq c) = some (s', k)) :
    k = 0 ∧ s'.stack = s.stack.drop 1 := by
  simp only [ROp.exec, Option.bind_eq_bind] at h
  split at h; · simp at h
  obtain ⟨⟨b, s1⟩, h1, h⟩ := bind_some_elim h
  obtain ⟨e1, he1⟩ := popCell_stack h1
  simp at h; obtain ⟨rfl, rfl⟩ := h
  simp [he1]

theorem exec_pop (H : Hooks) {s s' : VmState} {k : Nat} (h : ROp.exec H s .pop = some (s', k)) :
    k = 0 ∧ s'.stack = s.stack.drop 1 := by
  simp only [ROp.exec, Option.bind_eq_bind] at h
  split at h; · simp at h
  obtain ⟨⟨b, s1⟩, h1, h⟩ := bind_some_elim h
  obtain ⟨he1, _⟩ := pop_stack h1
  simp at h; obtain ⟨rfl, rfl⟩ := h
  simp [he1]

theorem exec_log (H : Hooks) {s s' : VmState} {k : Nat} (h : ROp.exec H s .log = some (s', k)) :
    k = 0 ∧ s'.stack = s.stack.drop 1 := by
  simp only [ROp.exec, Option.bind_eq_bind] at h
  split at h; · simp at h
  obtain ⟨⟨b, s1⟩, h1, h⟩ := bind_some_elim h
  obtain ⟨he1, _⟩ := pop_stack h1
  simp at h; obtain ⟨rfl, rfl⟩ := h
  simp [he1]

theorem exec_branch (H : Hooks) {n : Nat} {s s' : VmState} {k : Nat} (h : ROp.exec H s (.branch n) = some (s', k)) :
    (k = 0 ∨ k = n) ∧ s'.stack = s.stack.drop 1 := by
  simp only [ROp.exec, Option.bind_eq_bind] at h
  split at h; · simp at h
  obtain ⟨⟨b, s1⟩, h1, h⟩ := bind_some_elim h
  obtain ⟨e1, he1⟩ := popCell_stack h1
  simp at h; obtain ⟨rfl, rfl⟩ := h
  refine ⟨?_, by simp [he1]⟩
  split <;> simp

theorem exec_jmp (H : Hooks) {n : Nat} {s s' : VmState} {k : Nat} (h : ROp.exec H s (.jmp n) = some (s', k)) :
    k = n ∧ s' = s := by
  simp [ROp.exec, ROp.stackReq] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩

theorem exec_ckpt (H : Hooks) {s s' : VmState} {k : Nat} (h : ROp.exec H s .ckpt = some (s', k)) :
    k = 0 ∧ s' = s := by
  simp [ROp.exec, ROp.stackReq] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩

theorem exec_push (H : Hooks) {st : Bool} {v : SV} {s s' : VmState} {k : Nat}
    (h : ROp.exec H s (.push st v) = some (s', k)) :
    k = 0 ∧ s'.stack = { val := v, strong := st, key := none } :: s.stack := by
  simp [ROp.exec, ROp.stackReq, VmState.push] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩

theorem exec_dup (H : Hooks) {n : Nat} {s s' : VmState} {k : Nat} (h : ROp.exec H s (.dup n) = some (s', k)) :
    k = 0 ∧ ∃ e, s.stack[n]? = some e ∧ s'.stack = e :: s.stack := by
  simp only [ROp.exec, Option.bind_eq_bind] at h
  split at h; · simp at h
  obtain ⟨e, he, h⟩ := bind_some_elim h
  simp [VmState.push] at h; obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, e, he, rfl⟩

theorem exec_swap (H : Hooks) {n : Nat} {s s' : VmState} {k : Nat} (h : ROp.exec H s (.swap n) = some (s', k)) :
    k = 0 ∧ ∃ top oth, s.stack[0]? = some top ∧ s.stack[n + 1]? = some oth ∧
      s'.stack = (s.stack.set 0 oth).set (n + 1) top := by
  simp only [ROp.exec, Option.bind_eq_bind] at h
  split at h; · simp at h
  obtain ⟨top, ht, h⟩ := bind_some_elim h
  obtain ⟨oth, ho, h⟩ := bind_some_elim h
  simp at h; obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, top, oth, ht, ho, rfl⟩


theorem pop_eq {s : VmState} {e : Entry} {s' : VmState} (h : s.pop = some (e, s')) :
    s.stack = e :: s'.stack ∧ s' = { s with stack := s'.stack } := by
  unfold VmState.pop at h
  split at h
  · rename_i e' es hs; simp at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨hs, rfl⟩
  · simp at h

theorem popCell_entry {s : VmState} {v : AV} {s' : VmState} (h : s.popCell = some (v, s')) :
    ∃ e, s.stack = e :: s'.stack ∧ e.val.asCell = some v := by
  simp only [VmState.popCell, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨e, s1⟩, h1, w, hw, h⟩ := h
  simp at h; obtain ⟨rfl, rfl⟩ := h
  exact ⟨e, (pop_stack h1).1, hw⟩

theorem exec_rem (H : Hooks) {c : Bool} {s s' : VmState} {k : Nat} (h : ROp.exec H s (.rem c) = some (s', k)) :
    k = 0 ∧ ∃ key cont rest, s.stack = key :: cont :: rest ∧ ∃ kv next, key.val.asCell = some kv ∧
      remNext cont.val kv = some next ∧ s'.stack = { cont with val := next } :: rest := by
  simp only [ROp.exec, Option.bind_eq_bind] at h
  split at h; · simp at h
  obtain ⟨⟨kv, s1⟩, h1, h⟩ := bind_some_elim h
  obtain ⟨key, hk1, hkv⟩ := popCell_entry h1
  obtain ⟨⟨cont, s2⟩, h2, h⟩ := bind_some_elim h
  obtain ⟨hk2, _⟩ := pop_stack h2
  simp only at h hk2
  split at h
  · simp at h
  · obtain ⟨cv, cs, ck⟩ := cont
    have hst : s.stack = key :: ⟨cv, cs, ck⟩ :: s2.stack := by rw [hk1, hk2]
    cases cv with
    | map m =>
      simp [VmState.push] at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, key, _, s2.stack, hst, kv, _, hkv, rfl, rfl⟩
    | bmt ht leaves =>
      simp only at h
      cases hi : kv.toU64 with
      | none => simp [hi] at h
      | some i =>
        by_cases hr : ht < 64 ∧ 2 ^ ht ≤ i
        · simp [hi, hr] at h
        · simp [hi, hr, VmState.push] at h; obtain ⟨rfl, rfl⟩ := h
          exact ⟨rfl, key, _, s2.stack, hst, kv, _, hkv, by simp [remNext, hi, hr], rfl⟩
    | _ => simp at h

theorem foldl_values (f : List Entry × List Entry → Key → List Entry × List Entry)
    (hf : ∀ acc v, f acc (.value v) = (acc.1 ++ [keyEntry v], acc.2)) :
    ∀ (keys : List AV) (pre sks : List Entry),
      (keys.map Key.value).foldl f (pre, sks) = (pre ++ keys.map keyEntry, sks)
  | [], pre, sks => by simp
  | k :: ks, pre, sks => by
      simp only [List.map_cons, List.foldl_cons, hf]
      rw [foldl_values f hf ks]; simp

theorem filter_values (keys : List AV) (p : Key → Bool) (hp : ∀ v, p (.value v) = false) :
    (keys.map Key.value).filter p = [] := by
  induction keys with
  | nil => rfl
  | cons k ks ih => simp [List.filter, hp, ih]

theorem exec_idx (H : Hooks) {c pp : Bool} {kvs : List AV} {s s' : VmState} {k : Nat}
    (h : ROp.exec H s (.idx c pp (kvs.map Key.value)) = some (s', k)) :
    k = 0 ∧ ∃ curr rest, s.stack = curr :: rest ∧
      idxWalk c pp (kvs.map keyEntry) { s with stack := rest } curr = some s' := by
  simp only [ROp.exec, Option.bind_eq_bind] at h
  split at h; · simp at h
  rw [filter_values _ _ (fun _ => rfl)] at h
  simp only [List.length_nil, List.take_zero, List.drop_zero] at h
  rw [foldl_values _ (fun _ _ => rfl)] at h
  simp only [List.nil_append] at h
  obtain ⟨⟨curr, s1⟩, h1, h⟩ := bind_some_elim h
  obtain ⟨hk1, hc1⟩ := pop_eq h1
  obtain ⟨s2, h2, h⟩ := bind_some_elim h
  simp at h; obtain ⟨rfl, rfl⟩ := h
  simp only at hk1 hc1 h2
  refine ⟨rfl, curr, s1.stack, hk1, ?_⟩
  rw [← h2, hc1]

theorem exec_idxStack (H : Hooks) {kvs : List AV} {s s' : VmState} {k : Nat}
    (h : ROp.exec H s (.idx true false (kvs.map Key.value ++ [.stack])) = some (s', k)) :
    k = 0 ∧ ∃ sk curr rest, s.stack = sk :: curr :: rest ∧
      idxWalk true false (kvs.map keyEntry ++ [sk]) { s with stack := rest } curr = some s' := by
  simp only [ROp.exec, Option.bind_eq_bind] at h
  split at h; · simp at h
  rw [List.filter_append, filter_values _ _ (fun _ => rfl)] at h
  simp only [List.foldl_append] at h
  rw [foldl_values _ (fun _ _ => rfl)] at h
  obtain ⟨st, c0, r0⟩ := s
  rcases st with _ | ⟨sk, st⟩
  · simp [VmState.pop] at h
  · simp only [List.nil_append, List.filter_cons, List.filter_nil, List.length_singleton, ite_true,
      List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero, List.foldl_cons, List.foldl_nil] at h
    obtain ⟨⟨curr, s1⟩, h1, h⟩ := bind_some_elim h
    obtain ⟨hk1, hc1⟩ := pop_eq h1
    obtain ⟨s2, h2, h⟩ := bind_some_elim h
    simp at h; obtain ⟨rfl, rfl⟩ := h
    simp only at hk1 hc1 h2
    refine ⟨rfl, sk, curr, s1.stack, by rw [hk1], ?_⟩
    rw [← h2, hc1]

theorem exec_ins (H : Hooks) {c : Bool} {n : Nat} {s s' : VmState} {k : Nat}
    (h : ROp.exec H s (.ins c n) = some (s', k)) :
    k = 0 ∧ ∃ curr s1 cc s2 curr' cc', s.stack = curr :: s1.stack ∧ insLoop c n s1 curr cc = some (s2, curr', cc') ∧
      ∃ key, s'.stack = { curr' with key } :: s2.stack := by
  simp only [ROp.exec, Option.bind_eq_bind] at h
  split at h; · simp at h
  obtain ⟨⟨curr, s1⟩, h1, h⟩ := bind_some_elim h
  obtain ⟨hk1, _⟩ := pop_stack h1
  obtain ⟨⟨s2, curr', cc'⟩, h2, h⟩ := bind_some_elim h
  simp at h; obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, curr, s1, _, s2, curr', cc', hk1, h2, _, rfl⟩

/-! ## The tags are kept -/

section Sound
variable {π : List AV} {T : Option SV}

theorem FTag.Ok_val {t : FTag} {e e' : Entry} (h : e.val = e'.val) (ht : t.Ok π T e) : t.Ok π T e' := by
  cases t <;> simp_all [FTag.Ok]

theorem drop_cons_of_get {l : List AV} {d : Nat} {k : AV} (h : l[d]? = some k) : l.drop d = k :: l.drop (d + 1) := by
  have hd : d < l.length := by
    rcases Nat.lt_or_ge d l.length with h' | h'
    · exact h'
    · simp [List.getElem?_eq_none h'] at h
  rw [List.drop_eq_getElem_cons hd]
  simp [List.getElem?_eq_getElem hd] at h
  rw [h]

theorem key_cell {kt : FTag} {key : Entry} {kv k : AV} (hk : kt.Ok π T key) (ht : kt = .key kv)
    (hkv : key.val.asCell = some k) : k = kv := by
  subst ht; simp only [FTag.Ok] at hk; rw [hk] at hkv; simp [SV.asCell] at hkv; exact hkv.symm

theorem fwalk_ok {ct kt : FTag} {curr key : Entry} {k : AV} {w : SV}
    (hc : ct.Ok π T curr) (hk : kt.Ok π T key) (hkv : key.val.asCell = some k)
    (hs : svStep curr.val k = some w) (e : Entry) (he : e.val = w) : (fwalk π ct kt).Ok π T e := by
  unfold fwalk
  split
  · rename_i d kv
    split
    · rename_i hh
      obtain ⟨hd, hlt⟩ := hh
      have hk' := key_cell hk rfl hkv
      subst hk'
      refine ⟨hlt, ?_⟩
      obtain ⟨_, hw⟩ := hc
      rw [drop_cons_of_get hd] at hw
      simp only [svWalk, hs, Option.bind_eq_bind, Option.bind_some] at hw
      rw [he]; exact hw
    · trivial
  · trivial

theorem idxWalk_frame {c pp : Bool} : ∀ (keys : List Entry) (kts : List FTag) (s : VmState) (curr : Entry)
    (ct : FTag) (ts : List FTag) (s' : VmState),
    Agrees π T kts keys → ct.Ok π T curr → Agrees π T ts s.stack → idxWalk c pp keys s curr = some s' →
    Agrees π T (fidx π pp kts ct ts) s'.stack
  | [], [], s, curr, ct, ts, s', _, hc, hts, h => by
      simp [idxWalk, VmState.push] at h; subst h; exact ⟨hc, hts⟩
  | key :: keys, kt :: kts, s, curr, ct, ts, s', hk, hc, hts, h => by
      simp only [idxWalk, Option.bind_eq_bind] at h
      cases hkv : key.val.asCell with
      | none => simp [hkv] at h
      | some k =>
        simp only [hkv, Option.bind_some] at h
        cases hi : idxOne (if pp then (s.push curr).push { key with key := none } else s).cache curr k c with
        | none => simp [hi] at h
        | some r =>
          obtain ⟨cache, curr'⟩ := r
          simp only [hi, Option.bind_some] at h
          have hstep := idxOne_val hi
          have hts' : Agrees π T (if pp then kt :: ct :: ts else ts)
              ({ (if pp then (s.push curr).push { key with key := none } else s) with cache }).stack := by
            cases pp
            · exact hts
            · exact ⟨FTag.Ok_val (e := key) rfl hk.1, hc, hts⟩
          exact idxWalk_frame keys kts _ curr' (fwalk π ct kt) _ s' hk.2
            (fwalk_ok hc hk.1 hkv hstep curr' rfl) hts' h
  | [], _ :: _, _, _, _, _, _, hk, _, _, _ => hk.elim
  | _ :: _, [], _, _, _, _, _, hk, _, _, _ => hk.elim

/-- When a cached `ins` refuses to write. -/
def insBlocked (c : Bool) (s : VmState) (cont : Entry) (k : AV) : Bool :=
  c && !(s.cache.contains (cont.key.push k)) && !(match cont.val with | .array _ => true | _ => false)

theorem insLoop_succ (c : Bool) (n : Nat) (s : VmState) (curr : Entry) (cc : CTree) :
    insLoop c (n + 1) s curr cc = (s.pop).bind fun r => (r.2.pop).bind fun r' =>
      (r.1.val.asCell).bind fun k =>
        if insBlocked c r'.2 r'.1 k then none
        else (insNext r'.1.val k curr.val).bind fun next =>
          insLoop c n r'.2 { val := next, strong := curr.strong && r'.1.strong, key := curr.key }
            (insCache (r'.2.cache.get r'.1.key) k cc) := by
  rw [insLoop]
  simp only [Option.bind_eq_bind]
  cases hp : s.pop with
  | none => simp
  | some r =>
    obtain ⟨key, s1⟩ := r
    simp only [Option.bind_some]
    cases hp' : s1.pop with
    | none => simp
    | some r' =>
      obtain ⟨cont, s2⟩ := r'
      simp only [Option.bind_some]
      cases key.val.asCell with
      | none => simp
      | some k =>
        simp only [Option.bind_some]
        simp only [insBlocked]
        obtain ⟨cv, cs, ck⟩ := cont
        cases cv with
        | array es =>
          simp only [insNext]
          cases k.toU8 with
          | none => simp
          | some i => by_cases hi : i < es.length <;> simp [hi]
        | map m =>
          by_cases hc : (c && !s2.cache.contains (ck.push k)) = true <;> simp [insNext, hc]
        | bmt h leaves =>
          by_cases hc : (c && !s2.cache.contains (ck.push k)) = true
          · simp [hc]
          · simp only [insNext]
            simp only [Bool.not_eq_true] at hc
            simp only [hc, Bool.false_and, Bool.false_eq_true, ite_false]
            cases k.toU64 with
            | none => simp
            | some i =>
              by_cases hi : h < 64 ∧ 2 ^ h ≤ i
              · simp [hi]
              · simp only [hi, ite_false, Option.bind_some]
                cases curr.val.asCell with
                | none => simp
                | some c1 => cases hh : c1.toHash <;> simp [hi, hh]
        | null => by_cases hc : (c && !s2.cache.contains (ck.push k)) = true <;> simp [insNext, hc]
        | cell _ => by_cases hc : (c && !s2.cache.contains (ck.push k)) = true <;> simp [insNext, hc]

theorem pop_some {s : VmState} {e : Entry} {s' : VmState} (h : s.pop = some (e, s')) :
    s.stack = e :: s'.stack ∧ s'.cache = s.cache := by
  unfold VmState.pop at h
  split at h
  · rename_i e' es hs; simp at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨hs, rfl⟩
  · simp at h

/-- The writes of `ins` keep the tags. -/
theorem fput_ok {cont key : Entry} {kt ct ct' t : FTag} {k : AV} {x next : SV}
    (hcont : ct.Ok π T cont) (hk : kt.Ok π T key) (hkv : key.val.asCell = some k)
    (hx : t.Ok π T ⟨x, true, none⟩) (hn : insNext cont.val k x = some next)
    (hf : fput π ct kt t = some ct') (e : Entry) (he : e.val = next) : ct'.Ok π T e := by
  unfold fput at hf
  split at hf
  · rename_i d
    split at hf
    · rename_i kv j hkd
      have hk' := key_cell hk rfl hkv
      subst hk'
      obtain ⟨hdl, hw⟩ := hcont
      have hdrop := drop_cons_of_get hkd
      split at hf
      · rename_i hkj
        subst hkj
        split at hf
        · rename_i hh
          simp at hf; subst hf
          obtain ⟨rfl, hlt⟩ := hh
          refine ⟨hdl, ?_⟩
          obtain ⟨_, hxw⟩ := hx
          rw [hdrop] at hw ⊢
          have hne : π.drop (d + 1) ≠ [] := by simp; omega
          obtain ⟨r, rs, hrs⟩ := List.exists_cons_of_ne_nil hne
          rw [hrs] at hw hxw ⊢
          rw [he, insNext_same hn]
          simp only at hxw
          rw [hxw]
        · simp at hf
      · split at hf
        · rename_i hkj hat
          simp at hf; subst hf
          refine ⟨hdl, ?_⟩
          rw [hdrop] at hw ⊢
          simp only [svWalk, Option.bind_eq_bind] at hw ⊢
          rw [he, insNext_ne hat hn]; exact hw
        · simp at hf
    · simp at hf
  · simp at hf; subst hf; trivial

theorem fins_frame {c : Bool} : ∀ (n : Nat) (s : VmState) (curr : Entry) (cc : CTree) (ct : FTag) (ts : List FTag)
    (ct' : FTag) (ts' : List FTag) (s' : VmState) (curr' : Entry) (cc' : CTree),
    Agrees π T ts s.stack → ct.Ok π T curr → fins π n ct ts = some (ct', ts') →
    insLoop c n s curr cc = some (s', curr', cc') → ct'.Ok π T curr' ∧ Agrees π T ts' s'.stack
  | 0, s, curr, cc, ct, ts, ct', ts', s', curr', cc', hts, hc, hf, h => by
      simp [fins] at hf; simp [insLoop] at h
      obtain ⟨rfl, rfl⟩ := hf; obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨hc, hts⟩
  | n + 1, s, curr, cc, ct, ts, ct', ts', s', curr', cc', hts, hc, hf, h => by
      rw [insLoop_succ] at h
      cases hp1 : s.pop with
      | none => simp [hp1] at h
      | some r =>
        obtain ⟨key, s1⟩ := r
        cases hp2 : s1.pop with
        | none => simp [hp1, hp2] at h
        | some r' =>
          obtain ⟨cont, s2⟩ := r'
          obtain ⟨hs1, _⟩ := pop_some hp1
          obtain ⟨hs2, _⟩ := pop_some hp2
          rw [hs1, hs2] at hts
          match ts, hts with
          | kt :: cnt :: ts₀, hts =>
            simp only [fins, Option.bind_eq_bind] at hf
            cases hfp : fput π cnt kt ct with
            | none => simp [hfp] at hf
            | some c₁ =>
              simp only [hfp, Option.bind_some] at hf
              simp only [hp1, hp2, Option.bind_some] at h
              cases hkv : key.val.asCell with
              | none => simp [hkv] at h
              | some k =>
                simp only [hkv, Option.bind_some] at h
                cases hb : insBlocked c s2 cont k
                · simp only [hb] at h
                  cases hn : insNext cont.val k curr.val with
                  | none => simp [hn] at h
                  | some next =>
                    simp only [hn, Option.bind_some] at h
                    exact fins_frame n s2 _ _ c₁ ts₀ ct' ts' s' curr' cc' hts.2.2
                      (fput_ok hts.2.1 hts.1 hkv (FTag.Ok_val (e := curr) rfl hc) hn hfp _ rfl) hf h
                · simp [hb] at h

theorem frem_ok {cont key : Entry} {kt ct ct' : FTag} {k : AV} {next : SV}
    (hcont : ct.Ok π T cont) (hk : kt.Ok π T key) (hkv : key.val.asCell = some k)
    (hn : remNext cont.val k = some next) (hf : frem π ct kt = some ct') (e : Entry) (he : e.val = next) :
    ct'.Ok π T e := by
  unfold frem at hf
  split at hf
  · rename_i d
    split at hf
    · rename_i kv j hkd
      have hk' := key_cell hk rfl hkv
      subst hk'
      obtain ⟨hdl, hw⟩ := hcont
      split at hf
      · rename_i hat
        simp at hf; subst hf
        refine ⟨hdl, ?_⟩
        rw [drop_cons_of_get hkd] at hw ⊢
        simp only [svWalk, Option.bind_eq_bind] at hw ⊢
        rw [he, remNext_ne hat hn]; exact hw
      · simp at hf
    · simp at hf
  · simp at hf; subst hf; trivial

end Sound

/-! ## Operands as the executor evaluates them -/

/-- `r` is what the executor sends for `op` (operands evaluated, then converted). -/
def OpEvals (p : Prims) (env : Env) (op : Op Expr) (r : ROp) : Prop :=
  ∃ op', op.mapM (Expr.eval p env) = some op' ∧ Op.toR (Exec.blank op') = some r

theorem mapM_consts {p : Prims} {env : Env} : ∀ {xs : List Expr} {vs : List Fr},
    xs.mapM (fun | .const c => some (Fr.ofInt c) | _ => none) = some vs → xs.mapM (Expr.eval p env) = some vs
  | [], vs, h => by simpa using h
  | x :: xs, vs, h => by
      simp only [List.mapM_cons, Option.bind_eq_bind] at h
      obtain ⟨v, hv, h⟩ := bind_some_elim h
      obtain ⟨vs', hvs, h⟩ := bind_some_elim h
      simp at h; subst h
      have hx : x.eval p env = some v := by
        cases x <;> simp_all [Expr.eval]
      simp [List.mapM_cons, hx, mapM_consts hvs]

theorem constAV_eval {k : Aligned Expr} {kv : AV} (h : constAV k = some kv) {p : Prims} {env : Env}
    {k' : Aligned Fr} (hk : k.mapM (Expr.eval p env) = some k') : AV.ofAligned k' = some kv := by
  unfold constAV at h
  simp only [Option.bind_eq_bind] at h
  obtain ⟨vs, hvs, h⟩ := bind_some_elim h
  have := mapM_consts (p := p) (env := env) hvs
  unfold Aligned.mapM at hk
  simp only [this] at hk
  simp at hk; subst hk; exact h

theorem keyTag_ok {π : List AV} {T : Option SV} {k : Aligned Expr} {p : Prims} {env : Env} {k' : Aligned Fr}
    (hk : k.mapM (Expr.eval p env) = some k') {kv : AV} (hkv : AV.ofAligned k' = some kv) (e : Entry)
    (he : e.val = .cell kv) : (keyTag k).Ok π T e := by
  unfold keyTag
  cases hc : constAV k with
  | none => trivial
  | some kv' =>
    have := constAV_eval hc hk
    rw [hkv] at this; cases this
    exact he

theorem path_ok {π : List AV} {T : Option SV} {p : Prims} {env : Env} :
    ∀ {path : List (Aligned Expr)} {path' : List (Aligned Fr)} {kvs : List AV},
      path.mapM (fun k : Aligned Expr => k.mapM (Expr.eval p env)) = some path' →
      path'.mapM AV.ofAligned = some kvs → Agrees π T (path.map keyTag) (kvs.map keyEntry)
  | [], path', kvs, h1, h2 => by
      simp at h1; subst h1; simp at h2; subst h2; trivial
  | k :: ks, path', kvs, h1, h2 => by
      simp only [List.mapM_cons, Option.bind_eq_bind] at h1
      obtain ⟨k', hk', h1⟩ := bind_some_elim h1
      obtain ⟨ks', hks', h1⟩ := bind_some_elim h1
      simp at h1; subst h1
      simp only [List.mapM_cons, Option.bind_eq_bind] at h2
      obtain ⟨kv, hkv, h2⟩ := bind_some_elim h2
      obtain ⟨kvs', hkvs', h2⟩ := bind_some_elim h2
      simp at h2; subst h2
      exact ⟨keyTag_ok hk' hkv _ rfl, path_ok hks' hkvs'⟩

section Step
variable {π : List AV} {T : Option SV}

theorem fpopPush_ok {n : Nat} {ts ts' : List FTag} {st st' : List Entry} (hf : fpopPush n ts = some ts')
    (ha : Agrees π T ts st) (hs : ∃ x, st' = x :: st.drop n) : Agrees π T ts' st' := by
  unfold fpopPush at hf
  split at hf
  · simp at hf; subst hf
    obtain ⟨x, rfl⟩ := hs
    exact ⟨trivial, ha.drop n⟩
  · simp at hf

theorem fstep_sound (H : Hooks) {p : Prims} {env : Env} {op : Op Expr} {r : ROp} (hr : OpEvals p env op r)
    {ts ts' : List FTag} (hf : fstep π op ts = some ts') {s s' : VmState} {k : Nat}
    (hex : r.exec H s = some (s', k)) (ha : Agrees π T ts s.stack) :
    k = 0 ∧ Agrees π T ts' s'.stack := by
  obtain ⟨op', hop, hr⟩ := hr
  cases op with
  | lt =>
    simp [Op.mapM] at hop; subst hop; simp [Exec.blank, Op.toR] at hr; subst hr
    obtain ⟨hk, hs⟩ := exec_lt H hex; exact ⟨hk, fpopPush_ok hf ha hs⟩
  | eq =>
    simp [Op.mapM] at hop; subst hop; simp [Exec.blank, Op.toR] at hr; subst hr
    obtain ⟨hk, hs⟩ := exec_eq H hex; exact ⟨hk, fpopPush_ok hf ha hs⟩
  | and =>
    simp [Op.mapM] at hop; subst hop; simp [Exec.blank, Op.toR] at hr; subst hr
    obtain ⟨hk, hs⟩ := exec_and H hex; exact ⟨hk, fpopPush_ok hf ha hs⟩
  | or =>
    simp [Op.mapM] at hop; subst hop; simp [Exec.blank, Op.toR] at hr; subst hr
    obtain ⟨hk, hs⟩ := exec_or H hex; exact ⟨hk, fpopPush_ok hf ha hs⟩
  | add =>
    simp [Op.mapM] at hop; subst hop; simp [Exec.blank, Op.toR] at hr; subst hr
    obtain ⟨hk, hs⟩ := exec_add H hex; exact ⟨hk, fpopPush_ok hf ha hs⟩
  | sub =>
    simp [Op.mapM] at hop; subst hop; simp [Exec.blank, Op.toR] at hr; subst hr
    obtain ⟨hk, hs⟩ := exec_sub H hex; exact ⟨hk, fpopPush_ok hf ha hs⟩
  | member =>
    simp [Op.mapM] at hop; subst hop; simp [Exec.blank, Op.toR] at hr; subst hr
    obtain ⟨hk, hs⟩ := exec_member H hex; exact ⟨hk, fpopPush_ok hf ha hs⟩
  | concat n =>
    simp [Op.mapM] at hop; subst hop; simp [Exec.blank, Op.toR] at hr; subst hr
    obtain ⟨hk, hs⟩ := exec_concat H hex; exact ⟨hk, fpopPush_ok hf ha hs⟩
  | concatCached n =>
    simp [Op.mapM] at hop; subst hop; simp [Exec.blank, Op.toR] at hr; subst hr
    obtain ⟨hk, hs⟩ := exec_concat H hex; exact ⟨hk, fpopPush_ok hf ha hs⟩
  | type =>
    simp [Op.mapM] at hop; subst hop; simp [Exec.blank, Op.toR] at hr; subst hr
    obtain ⟨hk, hs⟩ := exec_type H hex; exact ⟨hk, fpopPush_ok hf ha hs⟩
  | size =>
    simp [Op.mapM] at hop; subst hop; simp [Exec.blank, Op.toR] at hr; subst hr
    obtain ⟨hk, hs⟩ := exec_size H hex; exact ⟨hk, fpopPush_ok hf ha hs⟩
  | neg =>
    simp [Op.mapM] at hop; subst hop; simp [Exec.blank, Op.toR] at hr; subst hr
    obtain ⟨hk, hs⟩ := exec_neg H hex; exact ⟨hk, fpopPush_ok hf ha hs⟩
  | root =>
    simp [Op.mapM] at hop; subst hop; simp [Exec.blank, Op.toR] at hr; subst hr
    obtain ⟨hk, hs⟩ := exec_root H hex; exact ⟨hk, fpopPush_ok hf ha hs⟩
  | addi i =>
    cases hx : Expr.eval p env i with
    | none => simp [Op.mapM, hx] at hop
    | some i' =>
    simp [Op.mapM, hx] at hop; subst hop
    cases hm : immOf i' with
    | none => simp [Exec.blank, Op.toR, hm] at hr
    | some imm =>
    simp [Exec.blank, Op.toR, hm] at hr; subst hr
    obtain ⟨hk, hs⟩ := exec_addi H hex; exact ⟨hk, fpopPush_ok hf ha hs⟩
  | subi i =>
    cases hx : Expr.eval p env i with
    | none => simp [Op.mapM, hx] at hop
    | some i' =>
    simp [Op.mapM, hx] at hop; subst hop
    cases hm : immOf i' with
    | none => simp [Exec.blank, Op.toR, hm] at hr
    | some imm =>
    simp [Exec.blank, Op.toR, hm] at hr; subst hr
    obtain ⟨hk, hs⟩ := exec_subi H hex; exact ⟨hk, fpopPush_ok hf ha hs⟩
  | popeq c a res =>
    cases hx : res.mapM (Expr.eval p env) with
    | none => simp [Op.mapM, hx] at hop
    | some res' =>
    simp [Op.mapM, hx] at hop; subst hop
    simp [Exec.blank, Op.toR] at hr; subst hr
    obtain ⟨hk, hs⟩ := exec_popeq H hex
    match ts, ha, hf with
    | _ :: ts₀, ha, hf =>
      simp [fstep] at hf; subst hf
      exact ⟨hk, by rw [hs]; exact ha.drop 1⟩
  | pop =>
    simp [Op.mapM] at hop; subst hop; simp [Exec.blank, Op.toR] at hr; subst hr
    obtain ⟨hk, hs⟩ := exec_pop H hex
    match ts, ha, hf with
    | _ :: ts₀, ha, hf =>
      simp [fstep] at hf; subst hf
      exact ⟨hk, by rw [hs]; exact ha.drop 1⟩
  | log =>
    simp [Op.mapM] at hop; subst hop; simp [Exec.blank, Op.toR] at hr; subst hr
    obtain ⟨hk, hs⟩ := exec_log H hex
    match ts, ha, hf with
    | _ :: ts₀, ha, hf =>
      simp [fstep] at hf; subst hf
      exact ⟨hk, by rw [hs]; exact ha.drop 1⟩
  | ckpt =>
    simp [Op.mapM] at hop; subst hop; simp [Exec.blank, Op.toR] at hr; subst hr
    obtain ⟨hk, rfl⟩ := exec_ckpt H hex
    simp [fstep] at hf; subst hf; exact ⟨hk, ha⟩
  | push st v =>
    cases hv' : v.mapM (Expr.eval p env) with
    | none => simp [Op.mapM, hv'] at hop
    | some v' =>
    simp [Op.mapM, hv'] at hop; subst hop
    cases hvv : AV.ofAligned v' with
    | none => simp [Exec.blank, Op.toR, hvv] at hr
    | some vv =>
    simp [Exec.blank, Op.toR, hvv] at hr; subst hr
    obtain ⟨hk, hs⟩ := exec_push H hex
    simp [fstep] at hf; subst hf
    exact ⟨hk, by rw [hs]; exact ⟨keyTag_ok hv' hvv _ rfl, ha⟩⟩
  | pushNull st =>
    simp [Op.mapM] at hop; subst hop; simp [Exec.blank, Op.toR] at hr; subst hr
    obtain ⟨hk, hs⟩ := exec_push H hex
    simp [fstep] at hf; subst hf
    exact ⟨hk, by rw [hs]; exact ⟨trivial, ha⟩⟩
  | pushState st v =>
    cases hv' : v.mapM (Expr.eval p env) with
    | none => simp [Op.mapM, hv'] at hop
    | some v' =>
    simp [Op.mapM, hv'] at hop; subst hop
    cases hsv : SV.ofLit v' with
    | none => simp [Exec.blank, Op.toR, hsv] at hr
    | some sv =>
    simp [Exec.blank, Op.toR, hsv] at hr; subst hr
    obtain ⟨hk, hs⟩ := exec_push H hex
    simp [fstep] at hf; subst hf
    exact ⟨hk, by rw [hs]; exact ⟨trivial, ha⟩⟩
  | dup n =>
    simp [Op.mapM] at hop; subst hop; simp [Exec.blank, Op.toR] at hr; subst hr
    obtain ⟨hk, e, he, hs⟩ := exec_dup H hex
    simp only [fstep] at hf
    cases ht : ts[n]? with
    | none => simp [ht] at hf
    | some t =>
      simp [ht] at hf; subst hf
      obtain ⟨e', he', hok⟩ := ha.get n ht
      rw [he] at he'; cases he'
      exact ⟨hk, by rw [hs]; exact ⟨hok, ha⟩⟩
  | swap n =>
    simp [Op.mapM] at hop; subst hop; simp [Exec.blank, Op.toR] at hr; subst hr
    obtain ⟨hk, top, oth, htop, hoth, hs⟩ := exec_swap H hex
    simp only [fstep, Option.bind_eq_bind] at hf
    obtain ⟨tt, htt, hf⟩ := bind_some_elim hf
    obtain ⟨to, hto, hf⟩ := bind_some_elim hf
    simp at hf; subst hf
    obtain ⟨e1, he1, hok1⟩ := ha.get 0 htt
    obtain ⟨e2, he2, hok2⟩ := ha.get (n + 1) hto
    rw [htop] at he1; cases he1
    rw [hoth] at he2; cases he2
    exact ⟨hk, by rw [hs]; exact (ha.set 0 hok2).set (n + 1) hok1⟩
  | idx c pp path =>
    cases hp' : path.mapM (fun k : Aligned Expr => k.mapM (Expr.eval p env)) with
    | none => simp [Op.mapM, hp'] at hop
    | some path' =>
    simp [Op.mapM, hp'] at hop; subst hop
    cases hkvs : path'.mapM AV.ofAligned with
    | none => simp [Exec.blank, Op.toR, hkvs] at hr
    | some kvs =>
    simp [Exec.blank, Op.toR, hkvs] at hr; subst hr
    obtain ⟨hk, curr, rest, hst, hw⟩ := exec_idx H hex
    match ts, ha, hf with
    | ct :: ts₀, ha, hf =>
      simp [fstep] at hf; subst hf
      rw [hst] at ha
      exact ⟨hk, idxWalk_frame _ _ _ curr ct ts₀ s' (path_ok hp' hkvs) ha.1 ha.2 hw⟩
  | idxStack pre =>
    cases hp' : pre.mapM (fun k : Aligned Expr => k.mapM (Expr.eval p env)) with
    | none => simp [Op.mapM, hp'] at hop
    | some pre' =>
    simp [Op.mapM, hp'] at hop; subst hop
    cases hkvs : pre'.mapM AV.ofAligned with
    | none => simp [Exec.blank, Op.toR, hkvs] at hr
    | some kvs =>
    simp [Exec.blank, Op.toR, hkvs] at hr; subst hr
    obtain ⟨hk, sk, curr, rest, hst, hw⟩ := exec_idxStack H hex
    match ts, ha, hf with
    | skt :: ct :: ts₀, ha, hf =>
      simp [fstep] at hf; subst hf
      rw [hst] at ha
      exact ⟨hk, idxWalk_frame _ _ _ curr ct ts₀ s' (Agrees.append (path_ok hp' hkvs) (show Agrees π T [skt] [sk] from ⟨ha.1, trivial⟩))
        ha.2.1 ha.2.2 hw⟩
  | ins c n =>
    simp [Op.mapM] at hop; subst hop; simp [Exec.blank, Op.toR] at hr; subst hr
    obtain ⟨hk, curr, s1, cc, s2, curr', cc', hst, hl, key, hs⟩ := exec_ins H hex
    match ts, ha, hf with
    | ct :: ts₀, ha, hf =>
      simp only [fstep] at hf
      cases hfi : fins π n ct ts₀ with
      | none => simp [hfi] at hf
      | some r =>
        obtain ⟨c', ts₁⟩ := r
        simp [hfi] at hf; subst hf
        rw [hst] at ha
        obtain ⟨hok, ha'⟩ := fins_frame n s1 curr cc ct ts₀ c' ts₁ s2 curr' cc' ha.2 ha.1 hfi hl
        exact ⟨hk, by rw [hs]; exact ⟨FTag.Ok_val (e := curr') rfl hok, ha'⟩⟩
  | rem c =>
    simp [Op.mapM] at hop; subst hop; simp [Exec.blank, Op.toR] at hr; subst hr
    obtain ⟨hk, key, cont, rest, hst, kv, next, hkv, hn, hs⟩ := exec_rem H hex
    match ts, ha, hf with
    | kt :: ct :: ts₀, ha, hf =>
      simp only [fstep] at hf
      cases hfr : frem π ct kt with
      | none => simp [hfr] at hf
      | some c' =>
        simp [hfr] at hf; subst hf
        rw [hst] at ha
        exact ⟨hk, by rw [hs]; exact ⟨frem_ok ha.2.1 ha.1 hkv hn hfr _ rfl, ha.2.2⟩⟩
  | branch n => simp [fstep] at hf
  | jmp n => simp [fstep] at hf

end Step

/-! ## Whole programs -/

/-- Each instruction of the program is what the executor sends for the one written. -/
def AllEval (p : Prims) (env : Env) : List (Op Expr) → List ROp → Prop
  | [], [] => True
  | op :: ops, r :: rs => OpEvals p env op r ∧ AllEval p env ops rs
  | _, _ => False

theorem AllEval.drop {p : Prims} {env : Env} : ∀ (n : Nat) {ops : List (Op Expr)} {rs : List ROp},
    AllEval p env ops rs → AllEval p env (ops.drop n) (rs.drop n)
  | 0, _, _, h => h
  | _ + 1, [], [], _ => trivial
  | n + 1, _ :: _, _ :: _, h => AllEval.drop n h.2
  | _ + 1, [], _ :: _, h => h.elim
  | _ + 1, _ :: _, [], h => h.elim

theorem request_allEval {p : Prims} {env : Env} : ∀ {ops : List (Op Expr)} {req : List (Op Fr)} {rops : List ROp},
    Exec.request p env ops = some req → req.mapM Op.toR = some rops → AllEval p env ops rops
  | [], req, rops, h1, h2 => by
      simp [Exec.request] at h1; subst h1; simp at h2; subst h2; trivial
  | op :: ops, req, rops, h1, h2 => by
      simp only [Exec.request, Option.bind_eq_bind] at h1
      obtain ⟨op', hop, h1⟩ := bind_some_elim h1
      obtain ⟨rest, hrest, h1⟩ := bind_some_elim h1
      simp at h1; subst h1
      simp only [List.mapM_cons, Option.bind_eq_bind] at h2
      obtain ⟨r, hr, h2⟩ := bind_some_elim h2
      obtain ⟨rs, hrs, h2⟩ := bind_some_elim h2
      simp at h2; subst h2
      exact ⟨⟨op', hop, hr⟩, request_allEval hrest hrs⟩

theorem fcheck_other {π : List AV} {fuel : Nat} {op : Op Expr} {rest : List (Op Expr)} {ts : List FTag}
    (hb : ∀ n, op ≠ .branch n) (hj : ∀ n, op ≠ .jmp n) (h : fcheck π (fuel + 1) (op :: rest) ts = true) :
    ∃ ts', fstep π op ts = some ts' ∧ fcheck π fuel rest ts' = true := by
  cases op
  case branch n => exact absurd rfl (hb n)
  case jmp n => exact absurd rfl (hj n)
  all_goals
    simp only [fcheck] at h
    split at h
    · rename_i ts' hts; exact ⟨ts', hts, h⟩
    · simp at h

theorem runR_cons (H : Hooks) (r : ROp) (rest : List ROp) (s : VmState) :
    runR H (r :: rest) s = (r.exec H s).bind fun x =>
      if x.2 > rest.length then none
      else if x.1.stack.length > maxStackHeight then none
      else runR H (rest.drop x.2) x.1 := by
  rw [runR]; simp only [Option.bind_eq_bind]; rfl

theorem fcheck_sound (H : Hooks) {π : List AV} {T : Option SV} {p : Prims} {env : Env} :
    ∀ (fuel : Nat) (ops : List (Op Expr)) (rops : List ROp) (ts : List FTag) (s s' : VmState),
      fcheck π fuel ops ts = true → AllEval p env ops rops → Agrees π T ts s.stack → runR H rops s = some s' →
      ∃ e rest, s'.stack = e :: rest ∧ (FTag.pre 0).Ok π T e
  | 0, _, _, _, _, _, hf, _, _, _ => by simp [fcheck] at hf
  | fuel + 1, [], rops, ts, s, s', hf, he, ha, hr => by
      cases rops with
      | cons => exact he.elim
      | nil =>
        simp [runR] at hr; subst hr
        simp only [fcheck] at hf
        match ts, ha, hf with
        | t :: ts₀, ha, hf =>
          simp at hf; subst hf
          match hst : s.stack, ha with
          | e :: es, ha => exact ⟨e, es, rfl, ha.1⟩
  | fuel + 1, op :: rest, rops, ts, s, s', hf, he, ha, hr => by
      cases rops with
      | nil => exact he.elim
      | cons r rrest =>
        obtain ⟨hr1, hrest⟩ := he
        rw [runR_cons] at hr
        obtain ⟨⟨s1, k⟩, hex, hr2⟩ := bind_some_elim hr
        simp only at hr2
        split at hr2; · simp at hr2
        split at hr2; · simp at hr2
        rename_i hk _
        by_cases hbr : ∃ n, op = .branch n
        · obtain ⟨n, rfl⟩ := hbr
          obtain ⟨op', hop, hr1⟩ := hr1
          simp [Op.mapM] at hop; subst hop; simp [Exec.blank, Op.toR] at hr1; subst hr1
          obtain ⟨hk', hs1⟩ := exec_branch H hex
          simp only [fcheck] at hf
          match ts, ha, hf with
          | _ :: ts₀, ha, hf =>
            simp only [Bool.and_eq_true] at hf
            have ha' : Agrees π T ts₀ s1.stack := by rw [hs1]; exact ha.drop 1
            rcases hk' with hk0 | hkn
            · rw [hk0] at hr2
              exact fcheck_sound H fuel rest rrest ts₀ s1 s' hf.1 hrest ha' (by simpa using hr2)
            · rw [hkn] at hr2
              exact fcheck_sound H fuel (rest.drop n) (rrest.drop n) ts₀ s1 s' hf.2 (hrest.drop n) ha' hr2
        · by_cases hjm : ∃ n, op = .jmp n
          · obtain ⟨n, rfl⟩ := hjm
            obtain ⟨op', hop, hr1⟩ := hr1
            simp [Op.mapM] at hop; subst hop; simp [Exec.blank, Op.toR] at hr1; subst hr1
            obtain ⟨hkn, hss⟩ := exec_jmp H hex
            rw [hkn, hss] at hr2
            simp only [fcheck] at hf
            exact fcheck_sound H fuel (rest.drop n) (rrest.drop n) ts s s' hf (hrest.drop n) ha hr2
          · have hb : ∀ n, op ≠ .branch n := fun n h => hbr ⟨n, h⟩
            have hj : ∀ n, op ≠ .jmp n := fun n h => hjm ⟨n, h⟩
            obtain ⟨ts', hfs, hf⟩ := fcheck_other hb hj hf
            obtain ⟨rfl, ha'⟩ := fstep_sound H hr1 hfs hex ha
            exact fcheck_sound H fuel rest rrest ts' s1 s' hf hrest ha' (by simpa using hr2)

/-- **The frame theorem.** If `frameKeeps π ops`, a successful request of `ops`
    (any operand values, any ledger state) leaves the contract state's part at
    `π` exactly as it was. -/
theorem frame_ledgerOracle (H : Hooks) {π : List AV} {ops : List (Op Expr)} (hk : frameKeeps π ops = true)
    {p : Prims} {env : Env} {req : List (Op Fr)} (hreq : Exec.request p env ops = some req)
    {q q' : LedgerState} {xs : List Fr} (h : ledgerOracle H req q = some (xs, q')) :
    svWalk q'.state π = svWalk q.state π := by
  simp only [frameKeeps, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hk
  obtain ⟨⟨⟨hne, _⟩, _⟩, hf⟩ := hk
  unfold ledgerOracle at h
  simp only [Option.bind_eq_bind] at h
  obtain ⟨rops, hrops, h⟩ := bind_some_elim h
  obtain ⟨⟨reads, q₁⟩, hq, h⟩ := bind_some_elim h
  obtain ⟨vals, _, h⟩ := bind_some_elim h
  simp at h; obtain ⟨_, rfl⟩ := h
  unfold query at hq
  simp only [Option.bind_eq_bind] at hq
  obtain ⟨s, hs, hq⟩ := bind_some_elim hq
  have hlen : 0 < π.length := by
    cases π with
    | nil => exact absurd rfl hne
    | cons => simp
  have hinit : Agrees π (svWalk q.state π) [.pre 0, .other, .other] q.vm.stack := by
    rw [vm_eq]; exact ⟨⟨hlen, by simp⟩, trivial, trivial, trivial⟩
  obtain ⟨e, rest, hst, hok⟩ := fcheck_sound H _ ops rops _ q.vm s hf (request_allEval hreq hrops) hinit hs
  rw [hst] at hq
  match rest, hq with
  | [eff, ctx], hq =>
    simp only at hq
    split at hq
    · obtain ⟨eff', _, hq⟩ := bind_some_elim hq
      simp at hq; obtain ⟨_, rfl⟩ := hq
      simpa using hok.2
    · simp at hq

/-! ## Reads below a frame -/

theorem svWalk_append (v : SV) : ∀ (xs ys : List AV), svWalk v (xs ++ ys) = (svWalk v xs).bind (svWalk · ys)
  | [], ys => by simp [svWalk]
  | x :: xs, ys => by
      simp only [List.cons_append, svWalk, Option.bind_eq_bind]
      cases svStep v x with
      | none => rfl
      | some w => simp only [Option.bind_some]; exact svWalk_append w xs ys

/-- The keys of an evaluated path begin with its constant prefix. -/
theorem constPrefix_keys {p : Prims} {env : Env} : ∀ (n : Nat) {path : List (Aligned Expr)}
    {path' : List (Aligned Fr)} {keys : List AV},
    path.mapM (fun k : Aligned Expr => k.mapM (Expr.eval p env)) = some path' →
    path'.mapM AV.ofAligned = some keys → ∃ rest, keys = constPrefix n path ++ rest
  | 0, _, _, keys, _, _ => ⟨keys, by simp [constPrefix]⟩
  | n + 1, [], path', keys, h1, h2 => ⟨keys, by simp [constPrefix]⟩
  | n + 1, k :: ks, path', keys, h1, h2 => by
      simp only [List.mapM_cons, Option.bind_eq_bind] at h1
      obtain ⟨k', hk', h1⟩ := bind_some_elim h1
      obtain ⟨ks', hks', h1⟩ := bind_some_elim h1
      simp at h1; subst h1
      simp only [List.mapM_cons, Option.bind_eq_bind] at h2
      obtain ⟨kv, hkv, h2⟩ := bind_some_elim h2
      obtain ⟨kvs, hkvs, h2⟩ := bind_some_elim h2
      simp at h2; subst h2
      simp only [constPrefix]
      cases hc : constAV k with
      | none => exact ⟨kv :: kvs, rfl⟩
      | some kv' =>
        have := constAV_eval hc hk'
        rw [hkv] at this; cases this
        obtain ⟨rest, hr⟩ := constPrefix_keys n hks' hkvs
        exact ⟨rest, by simp [hr]⟩

/-- A read of the contract state along a path whose constant prefix is unchanged answers the same. -/
theorem readSpec_frame {p : Prims} {env : Env} (n : Nat) {path : List (Aligned Expr)} {path' : List (Aligned Fr)}
    (hp : path.mapM (fun k : Aligned Expr => k.mapM (Expr.eval p env)) = some path') (a : List Zkir.AlignAtom)
    {q q' : LedgerState} (hw : svWalk q'.state (constPrefix n path) = svWalk q.state (constPrefix n path)) :
    readSpec 0 path' a q' = readSpec 0 path' a q := by
  unfold readSpec
  cases hk : path'.mapM AV.ofAligned with
  | none => rfl
  | some keys =>
    obtain ⟨rest, rfl⟩ := constPrefix_keys n hp hk
    simp only [Option.bind_some, LedgerState.comp, svWalk_append, hw, Option.bind_eq_bind]

end Damp.Ledger
