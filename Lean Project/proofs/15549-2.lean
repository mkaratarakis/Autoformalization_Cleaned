import Init.Omega
import Init.Data.Nat.Mod

open Nat


example {x b k : Nat} :
    x % b ^ (k + 1) = x % b ^ k + b ^ k * ((x / b ^ k) % b) := by
  rw [Nat.pow_succ]
  rw [Nat.mul_mod]

/- ACTUAL PROOF OF Nat.mod_pow_succ -/

example {x b k : Nat} :
    x % b ^ (k + 1) = x % b ^ k + b ^ k * ((x / b ^ k) % b) := by
  rw [Nat.pow_succ, Nat.mod_mul]