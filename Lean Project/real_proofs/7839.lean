import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Dist

open Nat



example {n m : ℕ} (h : m ≤ n) : dist n m = n - m := by
  rw [dist_comm]; apply dist_eq_sub_of_le h