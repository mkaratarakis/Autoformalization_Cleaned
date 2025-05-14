import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Dist

open Nat


example (n m : ℕ) : n ≤ m + dist n m := by
  rw [dist_comm]
  by_cases h : m ≤ n
  · rw [dist_eq_sub_of_le h]
    exact Nat.le_add_right _ _
  · rw [dist_eq_sub_of_le_right h]
    calc
      n = m + (n - m) := (Nat.add_sub_cancel_left _ _).symm
      _ ≤ m + (m - n + (n - m)) :=
        Nat.add_le_add_left (Nat.le_add_right _ _) _

    rwa [add_tsub_cancel_of_le]

/- ACTUAL PROOF OF Nat.dist_tri_right' -/

example (n m : ℕ) : n ≤ m + dist n m := by
  rw [dist_comm]; apply dist_tri_right