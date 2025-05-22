import Init.Data.Nat.Gcd
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Lcm

open Nat

example (m n : Nat) : gcd m n * lcm m n = m * n := by
  rw [← lcm_mul_gcd_eq m n]
  rfl

/- ACTUAL PROOF OF Nat.gcd_mul_lcm -/

example (m n : Nat) : gcd m n * lcm m n = m * n := by
  rw [lcm, Nat.mul_div_cancel' (Nat.dvd_trans (gcd_dvd_left m n) (Nat.dvd_mul_right m n))]