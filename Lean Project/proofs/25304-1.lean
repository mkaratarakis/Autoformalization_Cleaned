import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : (false = true) = False := by
  unfold false true False
  rfl

/- ACTUAL PROOF OF Bool.false_eq_true -/

example : (false = true) = False := by
  simp