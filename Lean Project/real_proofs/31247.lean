import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat



example (n m k : Nat) : n * (m - k) = n * m - n * k := by
  rw [Nat.mul_comm, Nat.mul_sub_right_distrib, Nat.mul_comm m n, Nat.mul_comm n k]