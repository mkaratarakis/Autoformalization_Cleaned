import Init.Data.Array.Lemmas
import Init.Data.List.Impl

open List


example : @List.length = @List.lengthTR := by
  funext α as
  show as.length = as.lengthTR
  rw [lengthTR]
  rw [length_add_eq_lengthTRAux]
  rfl

/- ACTUAL PROOF OF List.length_eq_lengthTR -/

example : @List.length = @List.lengthTR := by
  apply funext; intro α; apply funext; intro as
  simp [lengthTR, ← length_add_eq_lengthTRAux]