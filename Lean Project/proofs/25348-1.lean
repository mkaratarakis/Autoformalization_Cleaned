import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x y z : Bool), xor x (xor y z) = xor y (xor x z) := by
  intros x y z
  fin_cases [x, y, z]
  all_goals {
    repeat {
      unfold xor
      rfl
    }
  }

/- ACTUAL PROOF OF Bool.xor_left_comm -/

example : ∀ (x y z : Bool), xor x (xor y z) = xor y (xor x z) := by
  decide