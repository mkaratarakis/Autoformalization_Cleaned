import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀b, (true  == b) =  b := by

intro b
cases b
case true =>
  show true == true = true
  rfl
case false =>
  show true == false = false
  rfl

/- ACTUAL PROOF OF Bool.true_beq -/

example : ∀b, (true  == b) =  b := by
  decide