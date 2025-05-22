import Init.Core
import Init.SimpLemmas

open Bool


example (a b : Bool) : (!(a == b)) = ¬(a = b) := by
  unfold not
  by_cases h : a == b
  · simp [h]
    rw [not_true_eq_false]
    exact h
  · simp [h]
    rw [not_false_eq_true]
    exact h

/- ACTUAL PROOF OF Bool.not_beq_to_not_eq -/

example (a b : Bool) : (!(a == b)) = ¬(a = b) := by
  simp