import Init.Core
import Init.SimpLemmas




example [BEq α] [LawfulBEq α] (a : α) : (a != a) = false := by
simp [BEq.beq, Bool.not_eq_false]

/- ACTUAL PROOF OF bne_self_eq_false -/

example [BEq α] [LawfulBEq α] (a : α) : (a != a) = false := by
  simp [bne]