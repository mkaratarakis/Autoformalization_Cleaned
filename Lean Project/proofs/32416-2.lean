import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (n m : Nat) : n - m + min n m = n := by
  rw [min_def]
  split_ifs with h
  · simp
  · simp
  · simp

/- ACTUAL PROOF OF Nat.sub_add_min_cancel -/

example (n m : Nat) : n - m + min n m = n := by
  rw [Nat.sub_eq_sub_min, Nat.sub_add_cancel (Nat.min_le_left ..)]