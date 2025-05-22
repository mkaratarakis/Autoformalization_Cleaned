import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat



example (n m k : Nat) : n * m * k = n * k * m := by
  rw [Nat.mul_assoc, Nat.mul_comm m, ← Nat.mul_assoc]