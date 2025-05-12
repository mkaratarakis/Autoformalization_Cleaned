import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Dist

open Nat


example (n k m : ℕ) : dist (n * k) (m * k) = dist n m * k := by
  rw [dist, dist]
  rw [mul_sub_right_distrib]
  rw [← add_mul]
  rw [add_comm]

/- ACTUAL PROOF OF Nat.dist_mul_right -/

example (n k m : ℕ) : dist (n * k) (m * k) = dist n m * k := by
  rw [dist, dist, right_distrib, tsub_mul n, tsub_mul m]