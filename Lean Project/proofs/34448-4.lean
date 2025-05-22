import Init.Data.List.Sublist
import Init.Data.List.Pairwise

open List
open Nat

example {a : α} {l : List α} : Nodup (a :: l) ↔ a ∉ l ∧ Nodup l := by
  constructor
  · intro h
    apply And.intro
    · intro hmem
      exact h (Or.inl rfl) (mem_cons_self _ _)
    · exact nodup_of_cons_nodup h
  · rintro ⟨hmem, hnodup⟩
    exact nodup_cons_of_nodup_of_not_mem hnodup hmem

/- ACTUAL PROOF OF List.nodup_cons -/

example {a : α} {l : List α} : Nodup (a :: l) ↔ a ∉ l ∧ Nodup l := by
  simp only [Nodup, pairwise_cons, forall_mem_ne]