import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Dist

open Nat



example {i j : Nat} : dist (succ i) (succ j) = dist i j := by
  simp [dist, succ_sub_succ]