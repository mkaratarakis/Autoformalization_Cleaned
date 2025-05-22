import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x y z : Bool), xor x (xor y z) = xor y (xor x z) := by
  intros x y z
  by_cases hx : x = true
  · by_cases hy : y = true
    · by_cases hz : z = true
      · simp [hx, hy, hz]
    · simp [hx, hy]
  · by_cases hy : y = true
    · by_cases hz : z = true
      · simp [hx, hy, hz]
    · simp [hx, hy]
  · by_cases hy : y = true
    · by_cases hz : z = true
      · simp [hx, hy, hz]
    · simp [hx, hy]
  · by_cases hz : z = true
    · simp [hx, hz]
    · simp [hx, hz]

/- ACTUAL PROOF OF Bool.xor_left_comm -/

example : ∀ (x y z : Bool), xor x (xor y z) = xor y (xor x z) := by
  decide