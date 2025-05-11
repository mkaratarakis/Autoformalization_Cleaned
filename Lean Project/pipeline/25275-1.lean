import Init.BinderPredicates
example
example : {b : Bool} → b ≠ false ↔ b = true := by
  constructor
  · intro h
    cases b
    · contradiction
    · rfl
  · intro h
    rw [h]
    trivial

/- ACTUAL PROOF OF Bool.ne_false_iff -/

example : {b : Bool} → b ≠ false ↔ b = true := by
  decide