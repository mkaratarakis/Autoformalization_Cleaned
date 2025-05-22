import Init.Data.List.Sublist
import Init.Data.List.Pairwise

open List
open Nat

example {a : α} {l : List α} : Nodup (a :: l) ↔ a ∉ l ∧ Nodup l := by
  constructor
  · intro h
    apply And.intro
    · intro hmem
      exact h (Or.inl rfl) (mem_of_mem_cons_of_ne _ _ hmem)
    · exact nodup_of_cons_nodup h
  · rintro ⟨hmem, hnodup⟩
    apply nodup_cons
    · exact hnodup
    · intro y hy mem
      cases mem
      · exfalso
        exact hmem (by rwa [hy])
      · exact ne_of_mem_of_nodup mem hnodup

/- ACTUAL PROOF OF List.nodup_cons -/

example {a : α} {l : List α} : Nodup (a :: l) ↔ a ∉ l ∧ Nodup l := by
  simp only [Nodup, pairwise_cons, forall_mem_ne]