import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat



example (n) : n * 2 = n + n := by
  rw [Nat.mul_succ, Nat.mul_one]