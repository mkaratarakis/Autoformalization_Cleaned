import Init.BinderPredicates
import Init.Data.Bool

open Bool


example (b : Bool) : (false = b) = (b = false) := by
  cases b
  · -- Case: b = false
    rfl
  · -- Case: b = true
    rw [Bool.false_ne_true]
    rfl

/- ACTUAL PROOF OF Bool.false_eq -/

example (b : Bool) : (false = b) = (b = false) := by
  cases b <;> simp