import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example (n m k : Nat) : n * (m * k) = m * (n * k) := by
  apply Eq.symm
  apply mul_left_comm

/- ACTUAL PROOF OF Nat.mul_left_comm -/

example (n m k : Nat) : n * (m * k) = m * (n * k) := by
  rw [← Nat.mul_assoc, Nat.mul_comm n m, Nat.mul_assoc]