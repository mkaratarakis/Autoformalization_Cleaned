import Init.BinderPredicates
example
example : {b : Bool} → b = false ↔ b ≠ true := by
  constructor
  · intro h
    cases b
    · contradiction
    · rfl
  · intro h
    cases b
    · contradiction
    · rfl

/- ACTUAL PROOF OF Bool.eq_false_iff -/

example : {b : Bool} → b = false ↔ b ≠ true := by
  decide