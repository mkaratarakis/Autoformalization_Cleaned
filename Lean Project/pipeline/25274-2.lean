import Init.BinderPredicates
example
example : {b : Bool} → b = false ↔ b ≠ true := by
  constructor
  · intro h
    cases b <;> simp [h]
  · intro h
    cases b <;> simp [h]

/- ACTUAL PROOF OF Bool.eq_false_iff -/

example : {b : Bool} → b = false ↔ b ≠ true := by
  decide