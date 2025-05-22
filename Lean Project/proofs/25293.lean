import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x : Bool), (x || !x) = true := by
  intro x
  cases x
  . simp
  . simp

/- ACTUAL PROOF OF Bool.or_not_self -/

example : ∀ (x : Bool), (x || !x) = true := by
  decide