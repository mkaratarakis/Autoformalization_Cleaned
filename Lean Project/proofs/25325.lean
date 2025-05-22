import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x y : Bool), (x || y) = (y || x) := by
intro x y
cases x <;> cases y <;> rfl

/- ACTUAL PROOF OF Bool.or_comm -/

example : ∀ (x y : Bool), (x || y) = (y || x) := by
  decide