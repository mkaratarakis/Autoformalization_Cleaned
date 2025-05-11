import Init.BinderPredicates
example (b = true)]  : decide (b = true)  =  b := by
  cases b
  · -- Case 1: b = false
    apply rfl
  · -- Case 2: b = true
    apply rfl

/- ACTUAL PROOF OF Bool.decide_eq_true -/

example {b : Bool} [Decidable (b = true)]  : decide (b = true)  =  b := by
  cases b <;> simp