import Init.BinderPredicates
import Init.Data.Bool

open Bool



example {b : Bool} [Decidable (true = b)]  : decide (true  = b) =  b := by
  cases b <;> simp