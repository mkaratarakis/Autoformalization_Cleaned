import Init.ByCases
example (a b : Nat) : min a b ≤ b := by
  by_cases h : a ≤ b
  · exact h
  · exact (not_le.1 h).le

/- ACTUAL PROOF OF Nat.min_le_right -/

example (a b : Nat) : min a b ≤ b := by
  by_cases (a <= b) <;> simp [Nat.min_def, *]