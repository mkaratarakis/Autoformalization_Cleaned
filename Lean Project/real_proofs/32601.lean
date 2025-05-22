import Init.Core
import Init.SimpLemmas





example [DecidableEq α] (a : α) : (a != a) = false := by
  simp