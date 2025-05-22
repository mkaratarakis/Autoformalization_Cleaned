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
      · apply mem_cons_of_mem
        assumption
    · apply Pairwise.nodup_cons_of_nodup_of_not_mem
      · assumption
      · intro x hx hxl
        apply h
        · exact Or.inr hx
        · assumption
  · rintro ⟨hmem, hnodup⟩
    apply Pairwise.nodup_cons
    · assumption
    · intro x hx hxl
      cases hxl
      · exfalso
        exact hmem (by rwa [hx])
      · exact ne_of_mem_of_nodup hxl hnodup

/- ACTUAL PROOF OF List.nodup_cons -/

example {a : α} {l : List α} : Nodup (a :: l) ↔ a ∉ l ∧ Nodup l := by
  simp only [Nodup, pairwise_cons, forall_mem_ne]