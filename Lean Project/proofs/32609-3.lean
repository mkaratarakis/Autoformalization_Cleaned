import Init.Core
import Init.SimpLemmas

open Bool


example (a b : Bool) : (!(a == b)) = ¬(a = b) := by
  unfold not
  by_cases h : a == b
  · simp [h]
    exact (Bool.not_eq_true).2 h
  · simp [h]
    rfl

/- ACTUAL PROOF OF Bool.not_beq_to_not_eq -/

example (a b : Bool) : (!(a == b)) = ¬(a = b) := by
  simp