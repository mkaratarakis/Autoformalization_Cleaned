import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x y z : Bool), ((x || y) || z) = ((x || z) || y) := by
  intros x y z
  cases x <;> cases y <;> cases z <;> rfl

/- ACTUAL PROOF OF Bool.or_right_comm -/

example : ∀ (x y z : Bool), ((x || y) || z) = ((x || z) || y) := by
  decide