import Init.Data.Array.Lemmas
import Init.Data.List.Impl

open List


example : @dropLast = @dropLastTR := by
  funext l
  exact dropLastTR_eq_dropLast l

/- ACTUAL PROOF OF List.dropLast_eq_dropLastTR -/

example : @dropLast = @dropLastTR := by
  funext α l; simp [dropLastTR]