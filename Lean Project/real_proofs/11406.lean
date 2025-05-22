import Init.Data.Nat.Dvd
import Init.NotationExtra
import Init.RCases
import Init.Data.Nat.Gcd

open Nat



example (m n : Nat) : gcd (n * m) n = n := by
  rw [Nat.mul_comm, gcd_mul_left_left]