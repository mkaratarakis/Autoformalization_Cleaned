import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Dist

open Nat


example (n m : ℕ) : n ≤ dist n m + m := by
  rw [dist_comm]
  unfold dist
  split_ifs with h
  · -- Case 1: m ≥ n
    rw [dif_pos h]
    apply Nat.le_add_left
  · -- Case 2: m < n
    rw [dif_neg h]
    linarith

/- ACTUAL PROOF OF Nat.dist_tri_left' -/

example (n m : ℕ) : n ≤ dist n m + m := by
  rw [dist_comm]; apply dist_tri_left