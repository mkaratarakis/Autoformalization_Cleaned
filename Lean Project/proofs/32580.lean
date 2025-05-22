import Init.Core
import Init.SimpLemmas

open Bool


example (b : Bool) : (b || false) = b := by
  cases b <;> rfl

/- ACTUAL PROOF OF Bool.or_false -/

example (b : Bool) : (b || false) = b := by
  cases b <;> rfl