import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (a b : Nat) : (a + 1) * (b + 1) = a * b + a + b + 1 := by
  rw [Nat.mul_succ, Nat.mul_succ, Nat.one_mul, Nat.add_assoc, Nat.add_assoc]
  simp

/- ACTUAL PROOF OF Nat.add_one_mul_add_one -/

example (a b : Nat) : (a + 1) * (b + 1) = a * b + a + b + 1 := by
  rw [add_one_mul, mul_add_one]; rfl