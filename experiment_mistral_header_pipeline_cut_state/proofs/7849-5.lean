import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Dist

open Nat


example (n m : ℕ) : n ≤ dist n m + m := by
  rw [dist_comm]
  by_cases h : n ≤ m
  · rw [dist_eq_sub_of_le h]
    calc
      n ≤ m := h
      _ ≤ m - n + m := by linarith
  · push_neg at h
    rw [dist_eq_sub_of_le_right h]
    calc
      n = n + 0 := by linarith
      _ ≤ n - m + m := by linarith

/- ACTUAL PROOF OF Nat.dist_tri_left' -/

example (n m : ℕ) : n ≤ dist n m + m := by
  rw [dist_comm]; apply dist_tri_left