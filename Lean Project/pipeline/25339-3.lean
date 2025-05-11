import Init.BinderPredicates
example (b : Bool) : (true = b) = (b = true) := by
  cases b
  · -- Case 1: b = false
    apply Eq.symm
    apply Eq.symm
    rfl
  · -- Case 2: b = true
    rfl

/- ACTUAL PROOF OF Bool.true_eq -/

example (b : Bool) : (true = b) = (b = true) := by
  cases b <;> simp