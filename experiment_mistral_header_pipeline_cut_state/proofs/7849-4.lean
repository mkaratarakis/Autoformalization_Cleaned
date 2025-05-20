import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Dist

open Nat


example (n m : ℕ) : n ≤ dist n m + m := by
  rw [dist_comm]
  by_cases h : n ≤ m
  · rw [dist_eq_sub_of_le h]
    exact Nat.le_add_left _ _
  · push_neg at h
    rw [dist_eq_sub_of_le_right (not_lt.mp h)]
    exact Nat.le_add_left _ _

/- ACTUAL PROOF OF Nat.dist_tri_left' -/

example (n m : ℕ) : n ≤ dist n m + m := by
  rw [dist_comm]; apply dist_tri_left