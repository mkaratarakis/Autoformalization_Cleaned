import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Dist

open Nat


example (n m : ℕ) : n ≤ m + dist n m := by
  rw [dist_comm]
  by_cases h : m ≤ n
  · rw [dist_eq_sub_of_le h]
    exact Nat.le_add_right n (n - m)
  · rw [dist_eq_sub_of_le_right (le_of_not_le h)]
    calc
      n = m + (n - m) := (add_tsub_cancel_of_le (le_of_not_le h)).symm
      _ ≤ m + (m - n + (n - m)) := by simp

    rwa [add_tsub_cancel_of_le]

/- ACTUAL PROOF OF Nat.dist_tri_right' -/

example (n m : ℕ) : n ≤ m + dist n m := by
  rw [dist_comm]; apply dist_tri_right