import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x : Bool), (x && !x) = false := by
intro x
cases x
case tt =>
simp
case ff =>
simp

/- ACTUAL PROOF OF Bool.and_not_self -/

example : ∀ (x : Bool), (x && !x) = false := by
  decide