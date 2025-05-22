import Init.Data.Array.Lemmas
import Init.Data.List.Impl

open List



example : @leftpad = @leftpadTR := by
  funext α n a l; simp [leftpad, leftpadTR, replicateTR_loop_eq]