import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Dist

open Nat


example (n m : ℕ) : n ≤ m + dist n m := by
  rw [dist_comm]
  cases h : le_total m n with
  | inl h =>
    rw [dist_eq_zero_of_le h]
    exact Nat.le_add_left _ _
  | inr h =>
    have : m + dist m n = n := by rw [dist_eq_sub_of_lt h]; simp
    rw [this]
    exact Nat.le_refl _

/- ACTUAL PROOF OF Nat.dist_tri_right' -/

example (n m : ℕ) : n ≤ m + dist n m := by
  rw [dist_comm]; apply dist_tri_right