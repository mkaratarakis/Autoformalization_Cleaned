import Init.ByCases
example (a b : Nat) : min a b = min b a := by
  by_cases h₁ : a ≤ b
  · by_cases h₂ : b ≤ a
    · have h₃ : a = b := Nat.le_antisymm h₁ h₂
      rw [h₃]
      rfl
    · have h₄ : b < a := (not_le_of_lt h₂).mp h₂
      rw [min_eq_left h₁]
      rw [min_eq_right h₄]
      rfl
  · by_cases h₃ : b ≤ a
    · have h₄ : a < b := (not_le_of_lt h₁).mp h₁
      rw [min_eq_right h₄]
      rw [min_eq_left h₃]
      rfl
    · have h₅ : a = b := Nat.le_antisymm h₃ h₁
      rw [h₅]
      rfl

/- ACTUAL PROOF OF Nat.min_comm -/

example (a b : Nat) : min a b = min b a := by
  match Nat.lt_trichotomy a b with
  | .inl h => simp [Nat.min_def, h, Nat.le_of_lt, Nat.not_le_of_lt]
  | .inr (.inl h) => simp [Nat.min_def, h]
  | .inr (.inr h) => simp [Nat.min_def, h, Nat.le_of_lt, Nat.not_le_of_lt]