import Init.Omega
import Init.Data.Nat.Mod

open Nat


example (m n k : Nat) : m % (k * n) / n = m / n % k := by
  rcases Nat.eq_zero_or_pos n with (rfl | hn); simp [mod_zero]
  rcases Nat.eq_zero_or_pos k with (rfl | hk); simp [mod_zero]
  conv => rhs; rw [← mod_add_div m (k * n)]
  rw [Nat.mul_assoc, add_mul_div_left _ _ hn, add_mul_mod_self_left,
    mod_eq_of_lt (Nat.div_lt_of_lt_mul (mod_lt _ (Nat.mul_pos hn hk)))]

/- ACTUAL PROOF OF Nat.mod_mul_left_div_self -/

example (m n k : Nat) : m % (k * n) / n = m / n % k := by
  rw [Nat.mul_comm k n, mod_mul_right_div_self]