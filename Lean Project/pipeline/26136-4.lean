import Init.ByCases
example (a b : Nat) : min a b ≤ b := by
  by_cases h : a ≤ b
  · rw [Nat.min_eq_left h]
    exact h
  · rw [Nat.min_eq_right (not_le.mp h)]
    exact Nat.le_refl b

/- ACTUAL PROOF OF Nat.min_le_right -/

example (a b : Nat) : min a b ≤ b := by
  by_cases (a <= b) <;> simp [Nat.min_def, *]