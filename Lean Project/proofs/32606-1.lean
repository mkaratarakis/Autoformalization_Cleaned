import Init.Core
import Init.SimpLemmas

open Bool


example (b : Bool) : ((!b) = true) = (b = false) := by
  cases b <;> simp [not_false_eq_true, not_true_eq_false, true_eq_false_eq_false]

/- ACTUAL PROOF OF Bool.not_eq_true' -/

example (b : Bool) : ((!b) = true) = (b = false) := by
  cases b <;> simp