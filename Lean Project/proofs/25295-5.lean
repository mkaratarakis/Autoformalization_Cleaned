import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(a b : Bool), ((a && b) = a) ↔ (a → b) := by
intro a b
apply Iff.intro
  (fun h => by
    by_cases ha : a
    · simp [ha] at h
      exact h
    · simp [ha])
  (fun h => by
    by_cases ha : a
    · simp [ha]
      exact h
    · simp [ha])

/- ACTUAL PROOF OF Bool.and_iff_left_iff_imp -/

example : ∀(a b : Bool), ((a && b) = a) ↔ (a → b) := by
  decide