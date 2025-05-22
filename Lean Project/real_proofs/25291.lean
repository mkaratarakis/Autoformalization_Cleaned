import Init.BinderPredicates
import Init.Data.Bool

open Bool



example {b : Bool} [Decidable (b = true)]  : decide (b = true)  =  b := by
  cases b <;> simp