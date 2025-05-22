import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : (b : Bool) → b = true ∨ b = false := by
  intro b
  cases b
  . left
    refl
  . right
    refl

/- ACTUAL PROOF OF Bool.eq_false_or_eq_true -/

example : (b : Bool) → b = true ∨ b = false := by
  decide