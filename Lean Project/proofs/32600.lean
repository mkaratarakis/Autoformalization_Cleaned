import Init.Core
import Init.SimpLemmas




example (b : Bool) : (b == true)  =  b := by
  cases b
  case false =>
    simp
  case true =>
    simp

/- ACTUAL PROOF OF beq_true -/

example (b : Bool) : (b == true)  =  b := by
  cases b <;> rfl