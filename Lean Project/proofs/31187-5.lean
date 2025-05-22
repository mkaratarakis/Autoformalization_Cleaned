import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example (a b : Nat) : ((!(a == b)) = true) = ¬(a = b) := by
  constructor
  · intro h
    simp only [Ne.def, Bool.not_eq_true] at h
    exact h
  · intro h
    simp only [Ne.def, Bool.not_eq_true]
    exact h

/- ACTUAL PROOF OF Nat.not_beq_eq_true_eq -/

example (a b : Nat) : ((!(a == b)) = true) = ¬(a = b) := by
  simp