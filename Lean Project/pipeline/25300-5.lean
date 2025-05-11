import Init.BinderPredicates
example (a ↔ b) := by
  cases b <;> simp [Bool.iff_eq]

/- ACTUAL PROOF OF Bool.eq_iff_iff -/

example {a b : Bool} : a = b ↔ (a ↔ b) := by
  cases b <;> simp