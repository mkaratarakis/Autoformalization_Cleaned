import Init.Data.Array.Lemmas
import Init.Data.List.Impl

open List


example : @dropLast = @dropLastTR := by
  funext l
  cases l
  · rfl
  · simp only [dropLast, dropLastTR, dropLast_cons]
    unfold dropLastTR
    simp

/- ACTUAL PROOF OF List.dropLast_eq_dropLastTR -/

example : @dropLast = @dropLastTR := by
  funext α l; simp [dropLastTR]