import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x y z : Bool), xor (xor x y) z = xor (xor x z) y := by
  intros x y z
  by_cases hx : x
  · by_cases hy : y
    · by_cases hz : z
      · simp [hx, hy, hz]
      simp [hx, hy, hz]
    · by_cases hz : z
      · simp [hx, hy, hz]
      simp [hx, hy, hz]
  · by_cases hy : y
    · by_cases hz : z
      · simp [hx, hy, hz]
      simp [hx, hy, hz]
    · by_cases hz : z
      · simp [hx, hy, hz]
      simp [hx, hy, hz]

/- ACTUAL PROOF OF Bool.xor_right_comm -/

example : ∀ (x y z : Bool), xor (xor x y) z = xor (xor x z) y := by
  decide