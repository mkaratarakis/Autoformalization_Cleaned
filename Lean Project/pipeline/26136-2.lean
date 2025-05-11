import Init.ByCases
example (a b : Nat) : min a b ≤ b := by
  by_cases h : a ≤ b
  · exact Nat.le_trans (Nat.min_eq_left h) h
  · exact Nat.min_eq_right h

/- ACTUAL PROOF OF Nat.min_le_right -/

example (a b : Nat) : min a b ≤ b := by
  by_cases (a <= b) <;> simp [Nat.min_def, *]