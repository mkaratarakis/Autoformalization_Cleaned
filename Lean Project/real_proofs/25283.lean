import Init.BinderPredicates
import Init.Data.Bool

open Bool



example {b : Bool} [Decidable (b = false)] : decide (b = false) = !b := by
  cases b <;> simp