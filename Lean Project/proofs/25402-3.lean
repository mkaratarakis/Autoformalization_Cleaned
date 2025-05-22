import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(c f : Bool), cond c false f = (!c && f) := by
  intros c f
  cases c
  case true =>
    simp
    rfl
  case false =>
    simp
    rfl

/- ACTUAL PROOF OF Bool.cond_false_left -/

example : ∀(c f : Bool), cond c false f = (!c && f) := by
  decide