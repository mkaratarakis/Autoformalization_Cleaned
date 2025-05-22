import Init.Core
import Init.SimpLemmas

open Bool


example (b : Bool) : (false || b) = b := by
  cases b
  · simp [or_false_left]
  · simp [or_true_right]

/- ACTUAL PROOF OF Bool.false_or -/

example (b : Bool) : (false || b) = b := by
  cases b <;> rfl