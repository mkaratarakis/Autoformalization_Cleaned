import Init.BinderPredicates
import Init.Data.Bool

open Bool


example :
    ∀ {m x y : Bool}, (x && m) = (y && m) ∧ (x || m) = (y || m) ↔ x = y := by
  intro m x y
  apply Iff.intro
  · intro h
    cases h
    case intro h₁ h₂ =>
    cases m <;> simp [*] at *
    any_goals simp [*]
  · intro h
    simp [h]

/- ACTUAL PROOF OF Bool.and_or_inj_right_iff -/

example :
    ∀ {m x y : Bool}, (x && m) = (y && m) ∧ (x || m) = (y || m) ↔ x = y := by
  decide