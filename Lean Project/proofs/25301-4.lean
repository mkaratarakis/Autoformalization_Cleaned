import Init.BinderPredicates
import Init.Data.Bool

open Bool


example {b : Bool} [Decidable (true = b)]  : decide (true  = b) =  b := by
  cases b
  · exact decide_eq_false (show Decidable (true = false) by apply isFalse)
  · exact decide_eq_true (show Decidable (true = true) by apply isTrue)

/- ACTUAL PROOF OF Bool.decide_true_eq -/

example {b : Bool} [Decidable (true = b)]  : decide (true  = b) =  b := by
  cases b <;> simp