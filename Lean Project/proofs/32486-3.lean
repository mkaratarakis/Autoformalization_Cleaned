import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (a m n : Nat) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero =>
    rw [Nat.add_zero]
    rw [Nat.pow_zero]
    rw [Nat.mul_one]
  | succ n ih =>
    rw [Nat.add_succ]
    rw [Nat.pow_succ]
    rw [ih]
    rw [←Nat.mul_assoc]

/- ACTUAL PROOF OF Nat.pow_add -/

example (a m n : Nat) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero => rw [Nat.add_zero, Nat.pow_zero, Nat.mul_one]
  | succ _ ih => rw [Nat.add_succ, Nat.pow_succ, Nat.pow_succ, ih, Nat.mul_assoc]