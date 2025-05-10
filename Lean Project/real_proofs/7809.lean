import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Dist

open Nat



example (n : ℕ) : dist n n = 0 := by
  simp [dist, tsub_self]