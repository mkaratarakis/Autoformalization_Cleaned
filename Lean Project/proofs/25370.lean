import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x y : Bool), xor (!x) y = !(xor x y) := by
  intro x y
  cases x <;> cases y <;> rfl

/- ACTUAL PROOF OF Bool.not_xor -/

example : ∀ (x y : Bool), xor (!x) y = !(xor x y) := by
  decide