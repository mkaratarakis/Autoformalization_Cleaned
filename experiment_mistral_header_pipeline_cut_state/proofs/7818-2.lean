import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Dist

open Nat


example (n m : ℕ) : n ≤ m + dist n m := by
  rw [dist_comm]
  cases le_total n m with
  | inl h =>
    rw [dist_eq_sub_of_le h]
    apply Nat.le_add_of_nonneg_of_le
    · rw [Nat.dist_eq_sub_of_le h]
      exact Nat.sub_nonneg_of_le h
    · exact h
  | inr h =>
    rw [dist_eq_sub_of_le_right h]
    exact le_rfl

/- ACTUAL PROOF OF Nat.dist_tri_right' -/

example (n m : ℕ) : n ≤ m + dist n m := by
  rw [dist_comm]; apply dist_tri_right