import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x y z : Bool), ((x || y) && z) = (x && z || y && z) := by
intro x y z
by_cases h: x = true
. simp [h]
  by_cases h₁: y = true
  . simp [h₁]
    simp
  . simp [h₁]
    simp
. simp [h]
  by_cases h₂: y = true
  . simp [h₂]
    simp
  . simp [h₂]
    simp

/- ACTUAL PROOF OF Bool.and_or_distrib_right -/

example : ∀ (x y z : Bool), ((x || y) && z) = (x && z || y && z) := by
  decide