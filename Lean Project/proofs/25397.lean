import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : ∀(c f : Bool), cond c true f  = ( c || f) := by
  intro c f
  cases c
  · simp [cond, or]
  · simp [cond, or]

/- ACTUAL PROOF OF Bool.cond_true_left -/

example : ∀(c f : Bool), cond c true f  = ( c || f) := by
  decide