import Init.BinderPredicates
import Init.Data.Bool

open Bool


example {b : Bool} [Decidable (true = b)]  : decide (true  = b) =  b := by
  cases b <;> rfl

/- ACTUAL PROOF OF Bool.decide_true_eq -/

example {b : Bool} [Decidable (true = b)]  : decide (true  = b) =  b := by
  cases b <;> simp