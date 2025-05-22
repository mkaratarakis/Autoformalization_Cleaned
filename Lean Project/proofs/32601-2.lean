import Init.Core
import Init.SimpLemmas




example [DecidableEq α] (a : α) : (a != a) = false := by
  simp [Ne.def, Bool.beq_iff_eq, Bool.not_eq_iff]

/- ACTUAL PROOF OF bne_self_eq_false' -/

example [DecidableEq α] (a : α) : (a != a) = false := by
  simp