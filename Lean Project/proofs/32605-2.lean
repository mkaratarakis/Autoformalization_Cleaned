import Init.Core
import Init.SimpLemmas

open Bool


example (a b : Bool) : (a == b) = (a = b) := by
  cases a <;> cases b <;> norm_num

/- ACTUAL PROOF OF Bool.beq_to_eq -/

example (a b : Bool) : (a == b) = (a = b) := by
  simp