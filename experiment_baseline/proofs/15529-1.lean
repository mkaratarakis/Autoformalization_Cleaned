import Init.Omega
import Init.Data.Nat.Mod

open Nat


example (m n k : Nat) : m % (k * n) / n = m / n % k := by
  simp [Nat.mul_comm, Nat.mod_def, Nat.div_def]
  rw [Nat.div_mod, Nat.div_mod]
  simp

/- ACTUAL PROOF OF Nat.mod_mul_left_div_self -/

example (m n k : Nat) : m % (k * n) / n = m / n % k := by
  rw [Nat.mul_comm k n, mod_mul_right_div_self]