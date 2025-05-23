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
      · rw [Int.natAbs_of_nonneg] at h
        rw [Int.natAbs_of_nonneg] at h
        exact Or.inl h
      · rw [Int.natAbs_of_nonneg] at h
        rw [Int.natAbs_of_nonpos (not_le.mp h2)] at h
        exact Or.inr (Int.neg_inj.mp h)
    · by_cases h2 : b ≥ 0
      · rw [Int.natAbs_of_nonpos (not_le.mp h1)] at h
        rw [Int.natAbs_of_nonneg] at h
        exact Or.inr (Int.neg_inj.mp h)
      · rw [Int.natAbs_of_nonpos (not_le.mp h1)] at h
        rw [Int.natAbs_of_nonpos (not_le.mp h2)] at h
        exact Or.inl (Int.neg_inj.mp h)
  · intro h
    by_cases h1 : a = b
    · rw [h1]
      rfl
    · rw [h1] at h
      rw [h]
      rfl

/- ACTUAL PROOF OF Int.natAbs_eq_natAbs_iff -/

example {a b : Int} : a.natAbs = b.natAbs ↔ a = b ∨ a = -b := by
  constructor <;> intro h
  · cases Int.natAbs_eq a with
    | inl h₁ | inr h₁ =>
      cases Int.natAbs_eq b with
      | inl h₂ | inr h₂ => rw [h₁, h₂]; simp [h]
  · cases h with (subst a; try rfl)
    | inr h => rw [Int.natAbs_neg]