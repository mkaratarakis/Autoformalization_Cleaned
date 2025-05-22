import Init.Core
import Init.SimpLemmas




example [DecidableEq α] (a : α) : (a != a) = false := by
  rw [Ne.def]
  simp

/- ACTUAL PROOF OF bne_self_eq_false' -/

example [DecidableEq α] (a : α) : (a != a) = false := by
  simp