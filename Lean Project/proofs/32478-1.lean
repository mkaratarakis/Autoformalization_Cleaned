import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (a m n : Nat) : a ^ (m * n) = (a ^ m) ^ n := by
  induction n with
  | zero =>
    simp [Nat.zero_mul, pow_zero]
  | succ n ih =>
    simp [Nat.mul_succ, pow_succ, ih, Nat.mul_add]

/- ACTUAL PROOF OF Nat.pow_mul -/

example (a m n : Nat) : a ^ (m * n) = (a ^ m) ^ n := by
  induction n with
  | zero => rw [Nat.mul_zero, Nat.pow_zero, Nat.pow_zero]
  | succ _ ih => rw [Nat.mul_succ, Nat.pow_add, Nat.pow_succ, ih]