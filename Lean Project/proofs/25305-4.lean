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
      apply True.intro
    · intro h
      rw [h]
      rfl
  · -- Case where a ≠ true
    simp [ha]
    constructor
    · intro h
      exact h
    · intro h
      exact Iff.intro (fun hb => hb) (fun hb => hb)

/- ACTUAL PROOF OF Bool.or_iff_right_iff_imp -/

example : ∀(a b : Bool), ((a || b) = b) ↔ (a → b) := by
  decide