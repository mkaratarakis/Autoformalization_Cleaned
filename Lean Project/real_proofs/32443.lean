import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat



example (a b) : succ a * succ b = a * b + a + b + 1 := by
  rw [succ_mul, mul_succ]; rfl