import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example (n m k : Nat) : (n + m) * k = n * k + m * k := by
  rw [mul_comm]
  rw [mul_add]
  rw [mul_comm n k]
  rw [mul_comm m k]

/- ACTUAL PROOF OF Nat.right_distrib -/

example (n m k : Nat) : (n + m) * k = n * k + m * k := by
  rw [Nat.mul_comm, Nat.left_distrib]; simp [Nat.mul_comm]