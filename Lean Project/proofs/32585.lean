import Init.Core
import Init.SimpLemmas

open Bool


example (b : Bool) : (false || b) = b := by
  cases b
  · rfl
  · rfl

/- ACTUAL PROOF OF Bool.false_or -/

example (b : Bool) : (false || b) = b := by
  cases b <;> rfl