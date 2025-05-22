import Init.Core
import Init.SimpLemmas





example [DecidableEq α] (a : α) : (a == a) = true := by
  simp