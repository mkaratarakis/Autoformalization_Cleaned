import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(b : Bool), (b = (!b)) ↔ False := by
  intro b
  cases b <;> simp [not_true_eq_false, not_false_eq_true]

/- ACTUAL PROOF OF Bool.eq_not_self -/

example : ∀(b : Bool), (b = (!b)) ↔ False := by
  decide