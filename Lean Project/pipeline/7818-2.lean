import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Dist

open Nat


example (n m : ℕ) : n ≤ m + dist n m := by
  rw [dist_comm]
  by_cases h : m ≤ n
  · rw [dist_eq_sub_of_le h]
    exact le_add_right n
  · rw [dist_eq_sub_of_le (not_le.mp h)]
    calc
      n = m + (n - m) := (add_tsub_cancel_of_le (not_le.mp h)).symm
      _ ≤ m + (m - n + (n - m)) :=
        add_le_add_left (le_add_right _ _) _

    rwa [add_tsub_cancel_of_le]

/- ACTUAL PROOF OF Nat.dist_tri_right' -/

example (n m : ℕ) : n ≤ m + dist n m := by
  rw [dist_comm]; apply dist_tri_right