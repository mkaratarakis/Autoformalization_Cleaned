import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example (n m k : Nat) : (n + m) * k = n * k + m * k := by
  rw [← Nat.mul_add]
  rw [Nat.add_comm m n]
  rw [Nat.mul_add]

/- ACTUAL PROOF OF Nat.right_distrib -/

example (n m k : Nat) : (n + m) * k = n * k + m * k := by
  rw [Nat.mul_comm, Nat.left_distrib]; simp [Nat.mul_comm]