import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(a b : Bool), ((a != b) != b) = a := by
intro a b
cases a <;> cases b <;> rfl

/- ACTUAL PROOF OF Bool.bne_self_right -/

example : ∀(a b : Bool), ((a != b) != b) = a := by
  decide