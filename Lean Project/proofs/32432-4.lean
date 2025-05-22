import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example {a b c : Nat} : max a b < c ↔ a < c ∧ b < c := by
  constructor
  · intro h
    apply And.intro
    · exact Nat.lt_of_le_of_lt (le_max_left _ _) h
    · exact Nat.lt_of_le_of_lt (le_max_right _ _) h
  · intro h
    cases h with
    | intro h₁ h₂ =>
      exact Nat.lt_of_lt_of_le (max_lt h₁ h₂) (le_refl _)

/- ACTUAL PROOF OF Nat.max_lt -/

example {a b c : Nat} : max a b < c ↔ a < c ∧ b < c := by
  rw [← Nat.succ_le, ← Nat.succ_max_succ a b]; exact Nat.max_le