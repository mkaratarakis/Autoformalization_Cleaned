import Init.ByCases
example (a b : Nat) : min a b = min b a := by
  by_cases h₁ : a ≤ b
  · by_cases h₂ : b ≤ a
    · have h₃ : a = b := Nat.le_antisymm h₁ h₂
      rw [h₃]
    · rw [if_pos h₁]
      rw [if_neg h₂]
  · by_cases h₃ : b ≤ a
    · rw [if_neg h₁]
      rw [if_pos h₃]
    · rw [if_neg h₁]
      rw [if_neg h₃]

/- ACTUAL PROOF OF Nat.min_comm -/

example (a b : Nat) : min a b = min b a := by
  match Nat.lt_trichotomy a b with
  | .inl h => simp [Nat.min_def, h, Nat.le_of_lt, Nat.not_le_of_lt]
  | .inr (.inl h) => simp [Nat.min_def, h]
  | .inr (.inr h) => simp [Nat.min_def, h, Nat.le_of_lt, Nat.not_le_of_lt]