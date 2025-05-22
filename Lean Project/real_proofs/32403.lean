import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat



example {n m : Nat} (h : m ≤ n) : m + (n - m) = n := by
  rw [Nat.add_comm, Nat.sub_add_cancel h]