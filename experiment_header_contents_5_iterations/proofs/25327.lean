import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(b : Bool), (b = (!b)) ↔ False := by
  intro b
  cases b <;> simp [*] at *

/- ACTUAL PROOF OF Bool.eq_not_self -/

example : ∀(b : Bool), (b = (!b)) ↔ False := by
  decide