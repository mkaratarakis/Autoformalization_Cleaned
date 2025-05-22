import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(a b : Bool), (a == (a == b)) = b := by
  intro a b
  cases a <;> cases b <;> rfl

/- ACTUAL PROOF OF Bool.beq_self_left -/

example : ∀(a b : Bool), (a == (a == b)) = b := by
  decide