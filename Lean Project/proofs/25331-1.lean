import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x : Bool), ((!x) == x) = false := by
  intros x
  cases x
  . refl
  . refl

/- ACTUAL PROOF OF Bool.not_beq_self -/

example : ∀ (x : Bool), ((!x) == x) = false := by
  decide