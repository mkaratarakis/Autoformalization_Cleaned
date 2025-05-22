import Init.Core
import Init.SimpLemmas




example [DecidableEq α] (a : α) : (a == a) = true := by
  simp

/- ACTUAL PROOF OF beq_self_eq_true' -/

example [DecidableEq α] (a : α) : (a == a) = true := by
  simp