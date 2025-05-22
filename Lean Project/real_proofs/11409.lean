import Init.Data.Nat.Dvd
import Init.NotationExtra
import Init.RCases
import Init.Data.Nat.Gcd

open Nat



example (m n : Nat) : gcd n (n * m) = n := by
  rw [gcd_comm, gcd_mul_right_left]