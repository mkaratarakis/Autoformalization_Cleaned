import Init.Omega
import Init.Data.Nat.Mod

open Nat



example (m n k : Nat) : m % (k * n) / n = m / n % k := by
  rw [Nat.mul_comm k n, mod_mul_right_div_self]