import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (a b) : succ a * succ b = a * b + a + b + 1 := by
  rw [succ_eq_add_one, succ_eq_add_one, Nat.mul_add, Nat.add_mul, Nat.add_assoc, Nat.add_comm (a * b) b, Nat.add_assoc, Nat.add_comm (a * b + a) 1]

/- ACTUAL PROOF OF Nat.succ_mul_succ -/

example (a b) : succ a * succ b = a * b + a + b + 1 := by
  rw [succ_mul, mul_succ]; rfl