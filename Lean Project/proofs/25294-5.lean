import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x y z : Bool), ((x || y) && z) = (x && z || y && z) := by
intro x y z
by_cases h: x = true
. simp [h]
  split <;> simp
. by_cases h': y = true
  . simp [h']
    split <;> simp
  . simp [h']
    split <;> simp
  . simp [h']
    split <;> simp

/- ACTUAL PROOF OF Bool.and_or_distrib_right -/

example : ∀ (x y z : Bool), ((x || y) && z) = (x && z || y && z) := by
  decide