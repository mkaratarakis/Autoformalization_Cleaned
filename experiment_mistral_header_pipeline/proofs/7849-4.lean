import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Dist

open Nat


example (n m : ℕ) : n ≤ dist n m + m := by
  obtain h | h := le_total n m
  · -- Case 1: n ≤ m
    rw [dist_eq_sub_of_le h]
    linarith
  · -- Case 2: m ≤ n
    rw [dist_eq_sub_of_le_right h]
    linarith

/- ACTUAL PROOF OF Nat.dist_tri_left' -/

example (n m : ℕ) : n ≤ dist n m + m := by
  rw [dist_comm]; apply dist_tri_left