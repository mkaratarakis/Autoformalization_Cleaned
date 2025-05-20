import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Dist

open Nat


example (n k m : ℕ) : dist (n * k) (m * k) = dist n m * k := by
  rw [dist]
  rw [dist]
  rw [mul_sub_left_distrib, mul_sub_left_distrib]
  rw [←mul_add]
  rfl

/- ACTUAL PROOF OF Nat.dist_mul_right -/

example (n k m : ℕ) : dist (n * k) (m * k) = dist n m * k := by
  rw [dist, dist, right_distrib, tsub_mul n, tsub_mul m]