import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀b, (true  == b) =  b := by

intro b
cases b
case tt =>
  show true == true = true
  rfl
case ff =>
  show true == false = false
  rfl

/- ACTUAL PROOF OF Bool.true_beq -/

example : ∀b, (true  == b) =  b := by
  decide