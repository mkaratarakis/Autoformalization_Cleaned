import Init.Omega
import Init.Data.Nat.Mod

open Nat


example {x b k : Nat} :
    x % b ^ (k + 1) = x % b ^ k + b ^ k * ((x / b ^ k) % b) := by
  rw [Nat.pow_succ]
  show x % (b ^ k * b) = x % b ^ k + b ^ k * (x / b ^ k % b)
  rw [Nat.mod_eq_of_lt]
  · rw [Nat.mul_lt_mul_left (Nat.zero_lt_succ _)]
    exact Nat.pow_lt_pow (Nat.zero_lt_succ _) k
  rw [Nat.mul_mod_right]

/- ACTUAL PROOF OF Nat.mod_pow_succ -/

example {x b k : Nat} :
    x % b ^ (k + 1) = x % b ^ k + b ^ k * ((x / b ^ k) % b) := by
  rw [Nat.pow_succ, Nat.mod_mul]