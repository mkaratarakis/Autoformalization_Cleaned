import Init.Omega
import Init.Data.Nat.Mod

open Nat


example (m n k : Nat) : m % (k * n) / n = m / n % k := by
  rw [Nat.mul_comm]
  rw [Nat.mod_eq_of_lt]
  · exact Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_pos_left _ _)
  rw [Nat.div_mod]

/- ACTUAL PROOF OF Nat.mod_mul_left_div_self -/

example (m n k : Nat) : m % (k * n) / n = m / n % k := by
  rw [Nat.mul_comm k n, mod_mul_right_div_self]