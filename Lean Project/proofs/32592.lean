import Init.Core
import Init.SimpLemmas

open Bool


example (b : Bool) : (b || b) = b := by
  cases b
  · simp
  · simp

/- ACTUAL PROOF OF Bool.or_self -/

example (b : Bool) : (b || b) = b := by
  cases b <;> rfl