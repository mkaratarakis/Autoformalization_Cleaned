import Init.Core
import Init.SimpLemmas




example (b : Bool) : (b == false) = !b := by
  cases b <;> rfl

/- ACTUAL PROOF OF beq_false -/

example (b : Bool) : (b == false) = !b := by
  cases b <;> rfl