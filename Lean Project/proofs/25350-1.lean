import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x y z : Bool), xor (xor x y) z = xor (xor x z) y := by
  intros x y z
  fin_cases x <;> fin_cases y <;> fin_cases z <;> rfl

/- ACTUAL PROOF OF Bool.xor_right_comm -/

example : ∀ (x y z : Bool), xor (xor x y) z = xor (xor x z) y := by
  decide