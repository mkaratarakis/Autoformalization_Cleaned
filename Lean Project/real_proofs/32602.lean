import Init.Core
import Init.SimpLemmas





example [BEq α] [LawfulBEq α] (a : α) : (a != a) = false := by
  simp [bne]