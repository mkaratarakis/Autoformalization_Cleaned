import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Dist

open Nat


example (n : ℕ) : dist n n = 0 := by
  rw [dist_eq_sub]
  exact Nat.sub_self n

/- ACTUAL PROOF OF Nat.dist_self -/

example (n : ℕ) : dist n n = 0 := by
  simp [dist, tsub_self]