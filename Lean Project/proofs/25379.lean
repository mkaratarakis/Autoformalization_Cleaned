import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x y z : Bool), (x || y && z) = ((x || y) && (x || z)) := by
  intros x y z
  by_cases h : x
  · simp [h]
  · simp [h]
    by_cases h' : y
    · simp [h']
    · simp [h']

/- ACTUAL PROOF OF Bool.or_and_distrib_left -/

example : ∀ (x y z : Bool), (x || y && z) = ((x || y) && (x || z)) := by
  decide