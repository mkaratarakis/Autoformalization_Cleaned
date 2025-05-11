import Init.BinderPredicates
example (b : Bool) : (true = b) = (b = true) := by
  cases b
  · -- Case 1: b = false
    exact (Propext (Iff.intro (by simp) (by simp)))
  · -- Case 2: b = true
    rfl

/- ACTUAL PROOF OF Bool.true_eq -/

example (b : Bool) : (true = b) = (b = true) := by
  cases b <;> simp