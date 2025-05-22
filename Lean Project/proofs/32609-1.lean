import Init.Core
import Init.SimpLemmas

open Bool


example (a b : Bool) : (!(a == b)) = ¬(a = b) := by
  unfold not
  rw [beq_iff_eq]
  rw [not_eq]
  rfl

/- ACTUAL PROOF OF Bool.not_beq_to_not_eq -/

example (a b : Bool) : (!(a == b)) = ¬(a = b) := by
  simp