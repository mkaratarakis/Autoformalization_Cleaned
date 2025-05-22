import Init.BinderPredicates
import Init.Data.Bool

open Bool


example {b : Bool} [Decidable (b = false)] : decide (b = false) = !b := by
  unfold decide
  cases h : b <;> simp [h]

/- ACTUAL PROOF OF Bool.decide_eq_false -/

example {b : Bool} [Decidable (b = false)] : decide (b = false) = !b := by
  cases b <;> simp