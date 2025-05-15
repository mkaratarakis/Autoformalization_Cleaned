import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Dist

open Nat


example (n m : ℕ) : n ≤ dist n m + m := by
  rw [dist_comm]
  unfold dist
  cases le_total n m with
  | inl h =>
    rw [dist_eq_sub_of_le h]
    apply Nat.le_add_left
  | inr h =>
    rw [dist_eq_sub_of_le_right h]
    apply Nat.le_add_right

/- ACTUAL PROOF OF Nat.dist_tri_left' -/

example (n m : ℕ) : n ≤ dist n m + m := by
  rw [dist_comm]; apply dist_tri_left