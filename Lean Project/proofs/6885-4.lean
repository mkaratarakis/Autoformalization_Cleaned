import Init.Data.Array.Lemmas
import Init.Data.List.Impl

open List


example : @dropLast = @dropLastTR := by
  funext l
  simp [dropLast, dropLastTR]
  induction l <;> simp [*, dropLast, dropLastTR]
  repeat rw [dropLast_cons]

/- ACTUAL PROOF OF List.dropLast_eq_dropLastTR -/

example : @dropLast = @dropLastTR := by
  funext α l; simp [dropLastTR]