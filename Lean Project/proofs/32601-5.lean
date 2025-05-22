import Init.Core
import Init.SimpLemmas




example [DecidableEq α] (a : α) : (a != a) = false := by
  rw [not_eq_iff_eq_false]
  rfl

/- ACTUAL PROOF OF bne_self_eq_false' -/

example [DecidableEq α] (a : α) : (a != a) = false := by
  simp