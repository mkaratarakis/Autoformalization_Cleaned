import Init.Core
import Init.SimpLemmas

open Bool


example (b : Bool) : (b && false) = false := by
  cases b
  · simp
  · simp

/- ACTUAL PROOF OF Bool.and_false -/

example (b : Bool) : (b && false) = false := by
  cases b <;> rfl