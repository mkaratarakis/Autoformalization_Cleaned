import Init.BinderPredicates
import Init.Data.Bool

open Bool


example {b : Bool} [Decidable (b = true)]  : decide (b = true)  =  b := by
  cases b
  case false =>
    -- In this case, b = false
    -- We need to show that decide (false = true) = false
    simp [decide]
  case true =>
    -- In this case, b = true
    -- We need to show that decide (true = true) = true
    simp [decide]

/- ACTUAL PROOF OF Bool.decide_eq_true -/

example {b : Bool} [Decidable (b = true)]  : decide (b = true)  =  b := by
  cases b <;> simp