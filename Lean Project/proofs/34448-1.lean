import Init.Data.List.Sublist
import Init.Data.List.Pairwise

open List
open Nat

example {a : α} {l : List α} : Nodup (a :: l) ↔ a ∉ l ∧ Nodup l := by
  constructor
  · intro h
    apply And.intro
    · intro hmem
      apply h
      · exact Or.inl rfl
      · exact hmem
    · exact nodup_of_cons_nodup h
  · intro h
    apply nodup_cons
    · exact h.right
    · intro y hy mem
      cases mem
      · rw [hmem] at hy
        exact hy rfl
      · exact h.left y hy mem

/- ACTUAL PROOF OF List.nodup_cons -/

example {a : α} {l : List α} : Nodup (a :: l) ↔ a ∉ l ∧ Nodup l := by
  simp only [Nodup, pairwise_cons, forall_mem_ne]