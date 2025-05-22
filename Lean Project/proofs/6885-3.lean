import Init.Data.Array.Lemmas
import Init.Data.List.Impl

open List


example : @dropLast = @dropLastTR := by
  funext l
  cases l
  · simp [dropLast, dropLastTR]
  · simp [dropLast, dropLastTR]
    apply dropLast_eq_dropLastTR

/- ACTUAL PROOF OF List.dropLast_eq_dropLastTR -/

example : @dropLast = @dropLastTR := by
  funext α l; simp [dropLastTR]