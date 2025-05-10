import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Dist

open Nat



example (n m : ℕ) : dist n m = dist m n := by
  simp [dist, add_comm]