import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Dist

open Nat


example (n k m : ℕ) : dist (n * k) (m * k) = dist n m * k := by
  rw [dist, dist]
  rw [Nat.sub_eq_add_neg, Nat.sub_eq_add_neg, Nat.sub_eq_add_neg, Nat.sub_eq_add_neg]
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_neg, Nat.mul_neg]
  rw [←Nat.add_assoc, ←Nat.add_assoc, Nat.add_comm (m * k), Nat.add_comm (n * k)]
  rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm (m * k), Nat.add_comm (n * k)]
  rw [Nat.mul_add]
  rfl

/- ACTUAL PROOF OF Nat.dist_mul_right -/

example (n k m : ℕ) : dist (n * k) (m * k) = dist n m * k := by
  rw [dist, dist, right_distrib, tsub_mul n, tsub_mul m]