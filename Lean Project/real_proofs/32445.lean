import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat



example (a b : Nat) : (a + 1) * (b + 1) = a * b + a + b + 1 := by
  rw [add_one_mul, mul_add_one]; rfl