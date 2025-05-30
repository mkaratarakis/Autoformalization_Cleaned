import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x : Bool), (!x || x) = true := by
intro x
cases x
case true =>
  simp
  rfl
case false =>
  simp [bor]
  rfl

/- ACTUAL PROOF OF Bool.not_or_self -/

example : ∀ (x : Bool), (!x || x) = true := by
  decide