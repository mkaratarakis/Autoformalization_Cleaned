import Init.Core
import Init.SimpLemmas




example (b : Bool) : (b == false) = !b := by
  cases b <;> simp [Bool.beq_ff_eq_true, Bool.not_eq_ff]

/- ACTUAL PROOF OF beq_false -/

example (b : Bool) : (b == false) = !b := by
  cases b <;> rfl