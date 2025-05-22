import Init.BinderPredicates
import Init.Data.Bool

open Bool


example : (false = true) = False := by
  apply Eq.symm
  rw [false_eq_true]

/- ACTUAL PROOF OF Bool.false_eq_true -/

example : (false = true) = False := by
  simp