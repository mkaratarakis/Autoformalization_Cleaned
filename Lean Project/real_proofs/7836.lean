import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Dist

open Nat



example {n m : ℕ} (h : n ≤ m) : dist n m = m - n := by
  rw [dist, tsub_eq_zero_iff_le.mpr h, zero_add]