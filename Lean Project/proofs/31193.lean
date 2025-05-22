import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example (a b : Nat) : ((a == b) = true) = (a = b) := by
  rw [beq_iff_eq]

/- ACTUAL PROOF OF Nat.beq_eq_true_eq -/

example (a b : Nat) : ((a == b) = true) = (a = b) := by
  simp