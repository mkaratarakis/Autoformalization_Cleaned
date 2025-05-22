import Init.Core
import Init.SimpLemmas

open Bool


example (b : Bool) : ((!b) = true) = (b = false) := by
  cases b <;> simp

/- ACTUAL PROOF OF Bool.not_eq_true' -/

example (b : Bool) : ((!b) = true) = (b = false) := by
  cases b <;> simp