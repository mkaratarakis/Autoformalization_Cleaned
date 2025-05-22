import Init.Data.Array.Lemmas
import Init.Data.List.Impl

open List


example : @leftpad = @leftpadTR := by
  funext α n a l
  dsimp only [leftpad, leftpadTR]
  rw [replicateTR_loop_eq]
  rfl

/- ACTUAL PROOF OF List.leftpad_eq_leftpadTR -/

example : @leftpad = @leftpadTR := by
  funext α n a l; simp [leftpad, leftpadTR, replicateTR_loop_eq]