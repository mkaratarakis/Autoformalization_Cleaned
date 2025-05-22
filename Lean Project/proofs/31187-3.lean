import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example (a b : Nat) : ((!(a == b)) = true) = ¬(a = b) := by
  simp only [Bool.not_eq_true, Ne.def]
  exact Iff.rfl

/- ACTUAL PROOF OF Nat.not_beq_eq_true_eq -/

example (a b : Nat) : ((!(a == b)) = true) = ¬(a = b) := by
  simp