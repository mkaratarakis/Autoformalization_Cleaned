import Init.Core
import Init.SimpLemmas

open Bool


example (b : Bool) : (b && b) = b := by
  cases b
  · simp
  · simp

/- ACTUAL PROOF OF Bool.and_self -/

example (b : Bool) : (b && b) = b := by
  cases b <;> rfl