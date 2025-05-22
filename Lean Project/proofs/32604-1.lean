import Init.Core
import Init.SimpLemmas

open Bool


example (b : Bool) : (¬(b = true)) = (b = false) := by
  cases b
  · show (¬(false = true)) = (false = false)
    rw [not_false_eq_true]
    rw [false_eq_false]
  · show (¬(true = true)) = (true = false)
    rw [not_true_eq_true]
    rw [true_ne_false]

/- ACTUAL PROOF OF Bool.not_eq_true -/

example (b : Bool) : (¬(b = true)) = (b = false) := by
  cases b <;> decide