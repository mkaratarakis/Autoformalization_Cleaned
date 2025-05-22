import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x y z : Bool), (x && y || z) = ((x || z) && (y || z)) := by
intro x y z
by_cases hx : x
. by_cases hy : y
  . simp [hx, hy]
  . simp [hx, hy]
. by_cases hy : y
  . simp [hx, hy]
  . simp [hx, hy]

/- ACTUAL PROOF OF Bool.or_and_distrib_right -/

example : ∀ (x y z : Bool), (x && y || z) = ((x || z) && (y || z)) := by
  decide