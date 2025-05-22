import Init.Data.Array.Lemmas
import Init.Data.List.Impl

open List



example : @dropLast = @dropLastTR := by
  funext α l; simp [dropLastTR]