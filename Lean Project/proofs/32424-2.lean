import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (n m k) : succ n - m - succ k = n - m - k := by
  rw [Nat.sub_sub, Nat.sub_sub]
  rw [Nat.add_succ, Nat.sub_succ]
  rw [Nat.add_assoc]
  rw [Nat.add_comm]
  rw [Nat.add_succ]
  rw [Nat.sub_add]
  rw [Nat.sub_sub]

/- ACTUAL PROOF OF Nat.succ_sub_sub_succ -/

example (n m k) : succ n - m - succ k = n - m - k := by
  rw [Nat.sub_sub, Nat.sub_sub, add_succ, succ_sub_succ]