import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x y z : Bool), xor x (xor y z) = xor y (xor x z) := by
  intros x y z
  by_cases hx : x = tt
  · by_cases hy : y = tt
    · by_cases hz : z = tt
      · simp [hx, hy, hz]
        rfl
      · simp [hx, hy, hz]
        rfl
    · by_cases hz : z = tt
      · simp [hx, hy, hz]
        rfl
      · simp [hx, hy, hz]
        rfl
  · by_cases hy : y = tt
    · by_cases hz : z = tt
      · simp [hx, hy, hz]
        rfl
      · simp [hx, hy, hz]
        rfl
    · by_cases hz : z = tt
      · simp [hx, hy, hz]
        rfl
      · simp [hx, hy, hz]
        rfl

/- ACTUAL PROOF OF Bool.xor_left_comm -/

example : ∀ (x y z : Bool), xor x (xor y z) = xor y (xor x z) := by
  decide