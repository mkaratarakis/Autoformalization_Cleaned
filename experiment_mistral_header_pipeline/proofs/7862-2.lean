import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Dist

open Nat


example (n k m : ℕ) : dist (n * k) (m * k) = dist n m * k := by
  rw [dist, dist]
  simp only [mul_sub, add_comm, add_left_comm, add_assoc]
  rw [mul_add]

/- ACTUAL PROOF OF Nat.dist_mul_right -/

example (n k m : ℕ) : dist (n * k) (m * k) = dist n m * k := by
  rw [dist, dist, right_distrib, tsub_mul n, tsub_mul m]