import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Dist

open Nat


example (n : ℕ) : dist n n = 0 := by
  rw [dist]
  rw [sub_self]
  rw [sub_self]
  rw [add_zero]

/- ACTUAL PROOF OF Nat.dist_self -/

example (n : ℕ) : dist n n = 0 := by
  simp [dist, tsub_self]