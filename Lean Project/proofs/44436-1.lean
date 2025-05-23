import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b : Int} : a.natAbs = b.natAbs ↔ a = b ∨ a = -b := by
  constructor
  · intro h
    by_cases h1 : a ≥ 0
    · by_cases h2 : b ≥ 0
      · have : a = a.natAbs := Int.natAbs_of_nonneg h1
        have : b = b.natAbs := Int.natAbs_of_nonneg h2
        rw [this, this] at h
        exact Or.inl h
      · have : b = -b.natAbs := (not_le.1 h2).natAbs_eq_neg
        have : a = a.natAbs := Int.natAbs_of_nonneg h1
        rw [this, this] at h
        exact Or.inr h.symm
    · by_cases h2 : b ≥ 0
      · have : a = -a.natAbs := (not_le.1 h1).natAbs_eq_neg
        have : b = b.natAbs := Int.natAbs_of_nonneg h2
        rw [this, this] at h
        exact Or.inr h.symm
      · have : a = -a.natAbs := (not_le.1 h1).natAbs_eq_neg
        have : b = -b.natAbs := (not_le.1 h2).natAbs_eq_neg
        rw [this, this] at h
        exact Or.inl h.symm
  · intro h
    by_cases h1 : a = b
    · rw [h1]
      exact Int.natAbs_eq_natAbs
    · rw [h1] at h
      exact Int.natAbs_eq_natAbs_neg h

/- ACTUAL PROOF OF Int.natAbs_eq_natAbs_iff -/

example {a b : Int} : a.natAbs = b.natAbs ↔ a = b ∨ a = -b := by
  constructor <;> intro h
  · cases Int.natAbs_eq a with
    | inl h₁ | inr h₁ =>
      cases Int.natAbs_eq b with
      | inl h₂ | inr h₂ => rw [h₁, h₂]; simp [h]
  · cases h with (subst a; try rfl)
    | inr h => rw [Int.natAbs_neg]