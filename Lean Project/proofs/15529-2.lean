import Init.Omega
import Init.Data.Nat.Mod

open Nat


example (m n k : Nat) : m % (k * n) / n = m / n % k := by
  rw [Nat.mul_comm]
  exact Nat.div_mod_div _ _ _

/- ACTUAL PROOF OF Nat.mod_mul_left_div_self -/

example (m n k : Nat) : m % (k * n) / n = m / n % k := by
  rw [Nat.mul_comm k n, mod_mul_right_div_self]