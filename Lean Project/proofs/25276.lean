import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(a b : Bool), (a && (a && b)) = (a && b) := by
  intros a b
  cases a <;> cases b <;> rfl

/- ACTUAL PROOF OF Bool.and_self_left -/

example : ∀(a b : Bool), (a && (a && b)) = (a && b) := by
  decide