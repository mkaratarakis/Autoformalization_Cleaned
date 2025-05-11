import Init.BinderPredicates
example (b = true)]  : decide (b = true)  =  b := by
  cases b <;> simp <;> rfl

/- ACTUAL PROOF OF Bool.decide_eq_true -/

example {b : Bool} [Decidable (b = true)]  : decide (b = true)  =  b := by
  cases b <;> simp