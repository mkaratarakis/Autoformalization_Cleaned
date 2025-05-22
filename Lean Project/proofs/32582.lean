import Init.Core
import Init.SimpLemmas

open Bool


example (b : Bool) : (true || b) = true := by
  cases b
  · simp
  · simp

/- ACTUAL PROOF OF Bool.true_or -/

example (b : Bool) : (true || b) = true := by
  cases b <;> rfl