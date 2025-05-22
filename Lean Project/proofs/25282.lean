import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x : Bool), (!x && x) = false := by
  intro x
  cases x <;> simp [not, and]

/- ACTUAL PROOF OF Bool.not_and_self -/

example : ∀ (x : Bool), (!x && x) = false := by
  decide