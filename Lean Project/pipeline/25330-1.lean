import Init.BinderPredicates
import Init.Data.Bool

open Bool


example (b : Bool) : (false = b) = (b = false) := by
  cases b
  · -- Case: b = false
    show false = false = false = false
    rfl
  · -- Case: b = true
    show false = true = true = false
    rw [false_ne_true]
    rw [false_ne_true]

/- ACTUAL PROOF OF Bool.false_eq -/

example (b : Bool) : (false = b) = (b = false) := by
  cases b <;> simp