import Init.Core
import Init.SimpLemmas

open Bool


example (b : Bool) : (b && true) = b := by
  cases b <;> rfl

/- ACTUAL PROOF OF Bool.and_true -/

example (b : Bool) : (b && true) = b := by
  cases b <;> rfl