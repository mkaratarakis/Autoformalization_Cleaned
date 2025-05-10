import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Dist

open Nat



example (n m : ℕ) : m ≤ n + dist n m := by
  rw [add_comm]; apply dist_tri_left