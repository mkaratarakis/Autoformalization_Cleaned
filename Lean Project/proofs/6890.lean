import Init.Data.Array.Lemmas
import Init.Data.List.Impl

open List


example : @filter = @filterTR := by
  funext α p as
  rw [filterTR]
  rw [filterTR_loop_eq]
  rfl

/- ACTUAL PROOF OF List.filter_eq_filterTR -/

example : @filter = @filterTR := by
  apply funext; intro α; apply funext; intro p; apply funext; intro as
  simp [filterTR, filterTR_loop_eq]