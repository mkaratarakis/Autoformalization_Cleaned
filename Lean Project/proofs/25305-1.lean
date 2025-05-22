import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(a b : Bool), ((a || b) = b) ↔ (a → b) := by
  intro a b
  by_cases ha: a = true
  · -- Case where a = true
    simp [ha]
    constructor
    · intro h
      simp [Bool.bor] at h
      exact h
    · intro h
      simp [Bool.bor, h]
  · -- Case where a = false
    simp [ha]
    constructor
    · intro h
      simp [Bool.bor] at h
      exact h
    · intro h
      simp [Bool.bor, h]

/- ACTUAL PROOF OF Bool.or_iff_right_iff_imp -/

example : ∀(a b : Bool), ((a || b) = b) ↔ (a → b) := by
  decide