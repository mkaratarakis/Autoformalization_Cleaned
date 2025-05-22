import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀b, (true  == b) =  b := by

intro b
cases b
· exact rfl
· exact rfl

/- ACTUAL PROOF OF Bool.true_beq -/

example : ∀b, (true  == b) =  b := by
  decide