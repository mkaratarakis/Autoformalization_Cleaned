import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x : Bool), (!x || x) = true := by
  intro x
  cases x
  . simp [true]
  . simp [false]

/- ACTUAL PROOF OF Bool.not_or_self -/

example : ∀ (x : Bool), (!x || x) = true := by
  decide