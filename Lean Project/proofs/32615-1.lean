import Init.Core
import Init.SimpLemmas

open Bool


example (a b : Bool) : ((a && b) = true) = (a = true ∧ b = true) := by
  cases a <;> cases b <;> simp [Bool.band_eq_true]

/- ACTUAL PROOF OF Bool.and_eq_true -/

example (a b : Bool) : ((a && b) = true) = (a = true ∧ b = true) := by
  cases a <;> cases b <;> decide