import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x : Bool), (x && !x) = false := by
intro x
cases x
case false =>
simp
case true =>
rw [not_eq_false]
apply and_false

/- ACTUAL PROOF OF Bool.and_not_self -/

example : ∀ (x : Bool), (x && !x) = false := by
  decide