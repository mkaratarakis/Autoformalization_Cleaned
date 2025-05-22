import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x y z : Bool), (x != y) = (x != z) ↔ y = z := by
  intros x y z
  by_cases hx : x = tt
  · by_cases hy : y = tt
    · by_cases hz : z = tt
      · simp [hx, hy, hz]
    · simp [hx, hy, hz]
  · by_cases hz : z = tt
    · simp [hx, hy, hz]
    · simp [hx, hy, hz]
  · by_cases hy : y = tt
    · by_cases hz : z = tt
      · simp [hx, hy, hz]
    · simp [hx, hy, hz]
  · by_cases hz : z = tt
    · simp [hx, hy, hz]
    · simp [hx, hy, hz]

/- ACTUAL PROOF OF Bool.bne_left_inj -/

example : ∀ (x y z : Bool), (x != y) = (x != z) ↔ y = z := by
  decide