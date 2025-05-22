import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(c f : Bool), cond c false f = (!c && f) := by
  intros c f
  cases c
  case true =>
    simp
    exact rfl
  case false =>
    have : !false = true := by simp
    simp
    exact rfl

/- ACTUAL PROOF OF Bool.cond_false_left -/

example : ∀(c f : Bool), cond c false f = (!c && f) := by
  decide