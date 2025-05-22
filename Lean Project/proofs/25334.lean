import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(b : Bool), ((!b) = b) ↔ False := by
  intro b
  cases b
  · simp
  · simp

/- ACTUAL PROOF OF Bool.not_eq_self -/

example : ∀(b : Bool), ((!b) = b) ↔ False := by
  decide