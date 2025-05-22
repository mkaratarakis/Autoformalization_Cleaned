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
      exact dec_trivial
  · by_cases hy : y = true
    · by_cases hz : z = true
      · simp [hx, hy, hz]
        exact dec_trivial
    · simp [hx, hy]
      exact dec_trivial
  · by_cases hy : y = true
    · by_cases hz : z = true
      · simp [hx, hy, hz]
        exact dec_trivial
    · simp [hx, hy]
      exact dec_trivial
  · by_cases hz : z = true
    · simp [hx, hz]
      exact dec_trivial
    · simp [hx, hz]
      exact dec_trivial

/- ACTUAL PROOF OF Bool.xor_left_comm -/

example : ∀ (x y z : Bool), xor x (xor y z) = xor y (xor x z) := by
  decide