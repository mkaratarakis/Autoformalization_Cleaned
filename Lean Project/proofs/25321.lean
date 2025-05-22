import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(b : Bool), (false != b) =  b := by
intro b
cases b
· rfl
· rfl

/- ACTUAL PROOF OF Bool.false_bne -/

example : ∀(b : Bool), (false != b) =  b := by
  decide