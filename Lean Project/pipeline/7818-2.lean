import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Dist

open Nat


example (n m : ℕ) : n ≤ m + dist n m := by
  rw [dist_comm]
  by_cases h : m ≤ n
  · rw [dist_eq_sub_of_le h]
    exact le_add_right _ _
  · rw [dist_eq_sub_of_le_right (le_of_not_ge h)]
    exact Nat.le_add_right _ _

/- ACTUAL PROOF OF Nat.dist_tri_right' -/

example (n m : ℕ) : n ≤ m + dist n m := by
  rw [dist_comm]; apply dist_tri_right