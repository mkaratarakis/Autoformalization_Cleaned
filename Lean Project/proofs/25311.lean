import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x y : Bool), (!(x && y)) = (!x || !y) := by
  intros x y
  cases x <;> cases y <;> rfl

/- ACTUAL PROOF OF Bool.not_and -/

example : ∀ (x y : Bool), (!(x && y)) = (!x || !y) := by
  decide