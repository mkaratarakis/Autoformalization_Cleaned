import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x y : Bool), (!(x || y)) = (!x && !y) := by
  -- Proceed with proof
  intros x y
  cases x <;> cases y <;> rfl

/- ACTUAL PROOF OF Bool.not_or -/

example : ∀ (x y : Bool), (!(x || y)) = (!x && !y) := by
  decide