import Init.Core
import Init.SimpLemmas




example [BEq α] [LawfulBEq α] (a : α) : (a != a) = false := by
rw [Ne.def]
simp [BEq.beq]

/- ACTUAL PROOF OF bne_self_eq_false -/

example [BEq α] [LawfulBEq α] (a : α) : (a != a) = false := by
  simp [bne]