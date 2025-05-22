import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀ (x : Bool), (x   == !x) = false := by
  intro x
  cases x
  . simp
  . simp

/- ACTUAL PROOF OF Bool.beq_not_self -/

example : ∀ (x : Bool), (x   == !x) = false := by
  decide