import Init.Omega
import Init.Data.Nat.Mod

open Nat


example {x b k : Nat} :
    x % b ^ (k + 1) = x % b ^ k + b ^ k * ((x / b ^ k) % b) := by
  rw [Nat.pow_succ]
  show x % (b ^ k * b) = x % b ^ k + b ^ k * (x / b ^ k % b)
  rw [Nat.mod_eq_of_lt]
  · apply Nat.mul_lt_mul_of_pos_left
    exact Nat.pow_pos (Nat.zero_lt_succ _) _
  rw [Nat.mod_mul_div]
  rfl

/- ACTUAL PROOF OF Nat.mod_pow_succ -/

example {x b k : Nat} :
    x % b ^ (k + 1) = x % b ^ k + b ^ k * ((x / b ^ k) % b) := by
  rw [Nat.pow_succ, Nat.mod_mul]