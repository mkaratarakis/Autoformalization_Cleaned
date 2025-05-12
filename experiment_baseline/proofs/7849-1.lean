import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Dist

open Nat


example (n m : ℕ) : n ≤ dist n m + m := by
  rw [dist_comm]
  cases h : le_total n m with
  | inl h =>
    rw [dist_eq_zero_of_le h]
    exact le_add_of_nonneg_right (n := n) (m := m)
  | inr h =>
    rw [dist_eq_abs_sub, abs_of_nonneg (Nat.sub_nonneg_of_le h)]
    rw [Nat.sub_add_cancel h]
    exact le_refl n

/- ACTUAL PROOF OF Nat.dist_tri_left' -/

example (n m : ℕ) : n ≤ dist n m + m := by
  rw [dist_comm]; apply dist_tri_left