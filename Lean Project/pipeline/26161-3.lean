import Init.ByCases
example (a b : Nat) : min a b = min b a := by
  by_cases h₁ : a ≤ b
  · by_cases h₂ : b ≤ a
    · have h₃ : a = b := Nat.le_antisymm h₁ h₂
      rw [h₃]
      rfl
  by_cases h₃ : b ≤ a
   · rw [min_def, if_pos h₁]
      rw [min_def, if_pos h₃]
      rfl
  rw [min_def, if_neg h₁]
  rw [min_def, if_neg h₃]
  rfl

/- ACTUAL PROOF OF Nat.min_comm -/

example (a b : Nat) : min a b = min b a := by
  match Nat.lt_trichotomy a b with
  | .inl h => simp [Nat.min_def, h, Nat.le_of_lt, Nat.not_le_of_lt]
  | .inr (.inl h) => simp [Nat.min_def, h]
  | .inr (.inr h) => simp [Nat.min_def, h, Nat.le_of_lt, Nat.not_le_of_lt]