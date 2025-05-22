import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (n m : Nat) : n - m + min n m = n := by
  rw [min_def]
  split_ifs
  · simp
  · simp [Nat.sub_eq_zero_of_le (Nat.le_min_left _ _)]
  · simp [Nat.sub_eq_zero_of_le (Nat.le_min_right _ _)]

/- ACTUAL PROOF OF Nat.sub_add_min_cancel -/

example (n m : Nat) : n - m + min n m = n := by
  rw [Nat.sub_eq_sub_min, Nat.sub_add_cancel (Nat.min_le_left ..)]