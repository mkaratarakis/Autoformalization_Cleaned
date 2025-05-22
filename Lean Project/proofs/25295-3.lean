import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(a b : Bool), ((a && b) = a) ↔ (a → b) := by
intro a b
apply Iff.intro
(fun h => by
  by_cases ha : a
  · rw [ha] at h
    simp [ha] at h
    exact h
  · simp [ha] at h)
(fun h => by
  by_cases ha : a
  · rw [ha]
    simp [ha]
    exact h
  · simp [ha])

/- ACTUAL PROOF OF Bool.and_iff_left_iff_imp -/

example : ∀(a b : Bool), ((a && b) = a) ↔ (a → b) := by
  decide