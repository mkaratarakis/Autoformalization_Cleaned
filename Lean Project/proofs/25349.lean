import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(a b : Bool), (a != (a != b)) = b := by
  intros a b
  cases a <;> cases b <;> rfl

/- ACTUAL PROOF OF Bool.bne_self_left -/

example : ∀(a b : Bool), (a != (a != b)) = b := by
  decide