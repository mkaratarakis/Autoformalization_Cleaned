import Init.BinderPredicates
example (a ↔ b) := by
intro h
cases b
· left
  rfl
· right
  rfl

/- ACTUAL PROOF OF Bool.eq_iff_iff -/

example {a b : Bool} : a = b ↔ (a ↔ b) := by
  cases b <;> simp