import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(b : Bool), (b = false ∨ b = true) ↔ True := by
  intro b
  apply Iff.intro
  · intro h
    cases h
    · exact True.intro
    · exact True.intro
  · intro h
    cases b
    · left
      exact rfl
    · right
      exact rfl

/- ACTUAL PROOF OF Bool.eq_false_or_eq_true_self -/

example : ∀(b : Bool), (b = false ∨ b = true) ↔ True := by
  decide