import Init.Core
import Init.SimpLemmas

open Bool


example (b : Bool) : (¬(b = false)) = (b = true) := by
  cases b <;> simp [not_eq_true, eq_true]

/- ACTUAL PROOF OF Bool.not_eq_false -/

example (b : Bool) : (¬(b = false)) = (b = true) := by
  cases b <;> decide