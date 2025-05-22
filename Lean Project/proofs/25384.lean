import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(b:Bool), (b = true → b = false) ↔ (b = false) := by
  intro b
  cases b <;> simp

/- ACTUAL PROOF OF Bool.eq_true_imp_eq_false -/

example : ∀(b:Bool), (b = true → b = false) ↔ (b = false) := by
  decide