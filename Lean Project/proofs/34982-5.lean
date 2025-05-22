import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]
variable [BEq α]

example {a : α} {l l'} :
    l <+ a :: l' ↔ l <+ l' ∨ ∃ r, l = a :: r ∧ r <+ l' := by
  constructor
  · intro h
    cases h
    · right
      use l'
      constructor
      · rfl
      · apply Sublist.cons₂
        exact h
    · left
      exact h
  · intro h
    cases h
    · apply Sublist.cons₂
      exact h
    · rcases h with ⟨r, rfl, hr⟩
      apply Sublist.cons
      exact hr

/- ACTUAL PROOF OF List.sublist_cons_iff -/

example {a : α} {l l'} :
    l <+ a :: l' ↔ l <+ l' ∨ ∃ r, l = a :: r ∧ r <+ l' := by
  constructor
  · intro h
    cases h with
    | cons _ h => exact Or.inl h
    | cons₂ _ h => exact Or.inr ⟨_, rfl, h⟩
  · rintro (h | ⟨r, rfl, h⟩)
    · exact h.cons _
    · exact h.cons₂ _