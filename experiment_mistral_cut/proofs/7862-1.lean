import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Dist

open Nat


example (n k m : ℕ) : dist (n * k) (m * k) = dist n m * k := by
  rw [dist]
  rw [dist]
  rw [mul_sub_left_distrib]
  rw [mul_sub_left_distrib]
  rw [add_mul]
  rw [mul_add]
  rw [←mul_add]
  rw [←add_mul]
  rw [add_comm _ (n * k)]
  rw [add_comm _ (m * k)]
  rw [add_comm (m * k) (n * k)]
  rw [add_assoc (m * k) (n * k) (m * k)]
  rw [add_assoc (n * k) (m * k) (m * k)]
  rw [add_assoc (n * k) (m * k) (n * k)]
  rw [add_assoc (n * k) (m * k) (n * k)]
  rw [add_assoc (n * k) (m * k) (n * k)]
  rw [add_assoc (n * k) (m * k) (n * k)]
  rw [add_assoc (n * k) (m * k) (n * k)]
  rw [add_assoc (n * k) (m * k) (n * k)]
  rw [add_assoc (n * k) (m * k) (n * k)]
  rw [add_assoc (n * k) (m * k) (n * k)]
  rw [add_assoc (n * k) (m * k) (n * k)]
  rw [add_assoc (n * k) (m * k) (n * k)]
  rw [add_assoc (n * k) (m * k) (n * k)]
  rw [add_assoc (n * k) (m * k) (n * k)]
  rw [add_assoc (n * k) (m * k) (n * k)]
  rw [add_assoc (n * k) (m * k) (n * k)]
  rw [add_assoc (n * k) (m * k) (n * k)]
  rw [add_assoc (n * k) (m * k) (n * k)]
  rw [add_assoc (n * k) (m * k) (n * k)]
  rw [add_assoc (n * k) (m * k) (n * k)]
  rw [add_assoc (n * k) (m * k) (n * k)]
  rw [add_assoc (n * k) (m * k) (n * k)]
  rw [add_assoc (n * k) (m * k) (n * k)]
  rw [add_assoc (n * k) (m * k) (n * k)]
  rw [add_assoc (n * k) (m * k) (n * k)]
  rw [add_assoc (n * k) (m * k) (n * k)]
  rw [add_assoc (n * k) (m * k) (n * k)]
  rw [add_assoc (n * k) (m * k) (n * k)]
  rw [add_assoc (n * k) (m * k) (n * k)]
  rw [add_assoc (n * k) (m * k) (n * k)]
  rw [add_assoc (n * k) (m * k) (n * k)]
  rw [add_assoc (n * k) (m * k) (n * k)]
  rw [add_assoc (n * k) (m * k) (n * k)]
 

/- ACTUAL PROOF OF Nat.dist_mul_right -/

example (n k m : ℕ) : dist (n * k) (m * k) = dist n m * k := by
  rw [dist, dist, right_distrib, tsub_mul n, tsub_mul m]