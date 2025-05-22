import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat

example {f : α → β → γ} {l l'} : zipWith f l l' = [] ↔ l = [] ∨ l' = [] := by
  constructor
  · intro h
    cases l <;> cases l' <;> try {contradiction}
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr rfl
  · intro h
    cases h <;> simp [zipWith]
    · rfl
    · rfl

/- ACTUAL PROOF OF List.zipWith_eq_nil_iff -/

example {f : α → β → γ} {l l'} : zipWith f l l' = [] ↔ l = [] ∨ l' = [] := by
  cases l <;> cases l' <;> simp