import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example (n m k : Nat) : n + (m + k) = m + (n + k) := by
  rw [← Nat.add_assoc n m k]
  rw [Nat.add_comm n m]
  rw [Nat.add_assoc]

/- ACTUAL PROOF OF Nat.add_left_comm -/

example (n m k : Nat) : n + (m + k) = m + (n + k) := by
  rw [← Nat.add_assoc, Nat.add_comm n m, Nat.add_assoc]