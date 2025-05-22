import Init.Core
import Init.SimpLemmas

open Bool


example (b : Bool) : (false && b) = false := by
  cases b <;> simp

/- ACTUAL PROOF OF Bool.false_and -/

example (b : Bool) : (false && b) = false := by
  cases b <;> rfl