import Init.BinderPredicates
import Init.Data.Bool

open Bool


example :
    ∀ {m x y : Bool}, (m && x) = (m && y) ∧ (m || x) = (m || y) ↔ x = y := by
  intro m x y
  apply Iff.intro
  · intro h
    cases m <;> simp [*] at h
    · exact h.left
    · exact h.right
  · intro h
    constructor
    · rw [h]
    · rw [h]

/- ACTUAL PROOF OF Bool.and_or_inj_left_iff -/

example :
    ∀ {m x y : Bool}, (m && x) = (m && y) ∧ (m || x) = (m || y) ↔ x = y := by
  decide