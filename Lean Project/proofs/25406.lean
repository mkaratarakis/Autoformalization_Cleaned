import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(c t : Bool), cond c t true  = (!c || t) := by
  intro c t
  cases c <;> simp

/- ACTUAL PROOF OF Bool.cond_true_right -/

example : ∀(c t : Bool), cond c t true  = (!c || t) := by
  decide