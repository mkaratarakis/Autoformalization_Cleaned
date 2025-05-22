import Init.BinderPredicates
import Init.Data.Bool

open Bool


example {b : Bool} [Decidable (false = b)] : decide (false = b) = !b := by
  cases b <;> simp

/- ACTUAL PROOF OF Bool.decide_false_eq -/

example {b : Bool} [Decidable (false = b)] : decide (false = b) = !b := by
  cases b <;> simp