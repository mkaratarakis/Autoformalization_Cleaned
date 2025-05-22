import Init.Core
import Init.SimpLemmas

open Bool


example (b : Bool) : (¬(b = false)) = (b = true) := by
  cases b <;> simp [bne, beq, not_eq]

/- ACTUAL PROOF OF Bool.not_eq_false -/

example (b : Bool) : (¬(b = false)) = (b = true) := by
  cases b <;> decide