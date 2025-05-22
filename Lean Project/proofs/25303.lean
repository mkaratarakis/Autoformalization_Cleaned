import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(a b : Bool), ((a || b) || b) = (a || b) := by
  intros a b
  cases a <;> cases b <;> rfl

/- ACTUAL PROOF OF Bool.or_self_right -/

example : ∀(a b : Bool), ((a || b) || b) = (a || b) := by
  decide