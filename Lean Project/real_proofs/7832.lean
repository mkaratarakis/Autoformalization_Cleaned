import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Dist

open Nat



example {n m : ℕ} (h : n = m) : dist n m = 0 := by
  rw [h, dist_self]