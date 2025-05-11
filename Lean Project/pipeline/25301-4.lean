import Init.BinderPredicates
example (true = b)]  : decide (true  = b) =  b := by
  cases b
  · exact rfl
  · exact rfl

/- ACTUAL PROOF OF Bool.decide_true_eq -/

example {b : Bool} [Decidable (true = b)]  : decide (true  = b) =  b := by
  cases b <;> simp