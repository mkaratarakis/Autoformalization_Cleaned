import Init.Data.Array.Lemmas
import Init.Data.List.Impl

open List


example : @dropLast = @dropLastTR := by
  funext l
  induction l
  case nil => simp [dropLast, dropLastTR]
  case cons =>
    simp [dropLast, dropLastTR]
    have h : List.dropLastTR l_ih = List.dropLast l_ih := h
    rw [h]

/- ACTUAL PROOF OF List.dropLast_eq_dropLastTR -/

example : @dropLast = @dropLastTR := by
  funext α l; simp [dropLastTR]