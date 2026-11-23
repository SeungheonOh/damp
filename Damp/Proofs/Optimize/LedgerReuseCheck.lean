/-
`Circuit.ledgerReuse` and `Circuit.ledgerDeadStore` keep the ledger-statement
check passing: every statement they emit is a statement of the original
circuit or a binding.
-/
import Damp.Proofs.Optimize.LedgerCheck
import Damp.Optimize.LedgerReuse
import Damp.Optimize.LedgerDeadStore

namespace Damp.IR
open LedgerWF

theorem mem_bindReads {rs : List Var} {vals : List Expr} {s : Stmt} (h : s ∈ bindReads rs vals) :
    ∃ v hint e, s = .bind v hint e := by
  simp only [bindReads, List.mem_map] at h
  obtain ⟨⟨r, e⟩, _, rfl⟩ := h
  exact ⟨r, _, e, rfl⟩

theorem mem_ledgerReuseGo : ∀ (fs : List LFact) (l : List Stmt) (s : Stmt), s ∈ ledgerReuseGo fs l →
    s ∈ l ∨ ∃ v hint e, s = .bind v hint e
  | _, [], s, h => by simp [ledgerReuseGo] at h
  | fs, st :: rest, s, h => by
      have ih := fun fs => mem_ledgerReuseGo fs rest s
      unfold ledgerReuseGo at h
      split at h
      all_goals first
        | (rcases List.mem_cons.mp h with rfl | h
           · exact Or.inl (List.mem_cons_self ..)
           · rcases ih _ h with h | h
             · exact Or.inl (List.mem_cons_of_mem _ h)
             · exact Or.inr h)
        | skip
      -- the ledger case
      rename_i g rs ops
      split at h
      · split at h
        · rcases List.mem_append.mp h with h | h
          · exact Or.inr (mem_bindReads h)
          · rcases ih _ h with h | h
            · exact Or.inl (List.mem_cons_of_mem _ h)
            · exact Or.inr h
        · rcases List.mem_cons.mp h with rfl | h
          · exact Or.inl (List.mem_cons_self ..)
          · rcases ih _ h with h | h
            · exact Or.inl (List.mem_cons_of_mem _ h)
            · exact Or.inr h
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inl (List.mem_cons_self ..)
        · rcases ih _ h with h | h
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · exact Or.inr h

/-- `Circuit.ledgerReuse` keeps ledger statements well formed. -/
theorem Circuit.ledgerReuse_checkLedger : Pass.KeepsLedger Circuit.ledgerReuse := by
  intro c h
  rw [Circuit.checkLedger_ok_iff] at h ⊢
  intro s hs
  simp only [Circuit.ledgerReuse, List.toList_toArray] at hs
  rcases mem_ledgerReuseGo [] _ s hs with hs | ⟨v, hint, e, rfl⟩
  · exact h s hs
  · rfl

theorem mem_deadStoreGo : ∀ (l : List Stmt) (s : Stmt), s ∈ deadStoreGo l → s ∈ l
  | [], s, h => by simp [deadStoreGo] at h
  | st :: rest, s, h => by
      unfold deadStoreGo at h
      split at h
      · split at h
        · exact List.mem_cons_of_mem _ (mem_deadStoreGo rest s h)
        · rcases List.mem_cons.mp h with rfl | h
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (mem_deadStoreGo rest s h)
      · rcases List.mem_cons.mp h with rfl | h
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (mem_deadStoreGo rest s h)

/-- `Circuit.ledgerDeadStore` keeps ledger statements well formed. -/
theorem Circuit.ledgerDeadStore_checkLedger : Pass.KeepsLedger Circuit.ledgerDeadStore := by
  intro c h
  rw [Circuit.checkLedger_ok_iff] at h ⊢
  intro s hs
  simp only [Circuit.ledgerDeadStore, List.toList_toArray] at hs
  exact h s (mem_deadStoreGo _ s hs)

end Damp.IR
