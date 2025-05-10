import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Dist

open Nat



example (k n m : ℕ) : dist (k * n) (k * m) = k * dist n m := by
  rw [mul_comm k n, mul_comm k m, dist_mul_right, mul_comm]