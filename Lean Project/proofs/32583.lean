import Init.Core
import Init.SimpLemmas

open Bool


example (b : Bool) : (true && b) = b := by
  cases b
  . simp
  . simp

/- ACTUAL PROOF OF Bool.true_and -/

example (b : Bool) : (true && b) = b := by
  cases b <;> rfl