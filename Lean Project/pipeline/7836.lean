import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Dist

open Nat


example {n m : ℕ} (h : n ≤ m) : dist n m = m - n := by
  rw [dist]
  rw [tsub_eq_zero_iff_le.2 h]
  rw [zero_add]

/- ACTUAL PROOF OF Nat.dist_eq_sub_of_le -/

example {n m : ℕ} (h : n ≤ m) : dist n m = m - n := by
  rw [dist, tsub_eq_zero_iff_le.mpr h, zero_add]