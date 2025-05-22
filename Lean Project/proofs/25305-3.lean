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
      apply Iff.intro
      · intro hb
        exact hb
      · intro hb
        exact hb
    · intro h
      apply False.elim

/- ACTUAL PROOF OF Bool.or_iff_right_iff_imp -/

example : ∀(a b : Bool), ((a || b) = b) ↔ (a → b) := by
  decide