import Init.BinderPredicates
import Init.Data.Bool

open Bool



example {b : Bool} [Decidable (false = b)] : decide (false = b) = !b := by
  cases b <;> simp