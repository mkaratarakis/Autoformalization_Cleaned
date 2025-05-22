import Init.Data.Nat.Gcd
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Lcm

open Nat


example (m n : Nat) : gcd m n * lcm m n = m * n := by
  let d := gcd m n
  let l := lcm m n
  have hlcm: l = m * n / d := by
    rw [← mul_div_assoc]
    rfl
  calc
    d * l = d * (m * n / d) := by rw [hlcm]
    _ = m * n := by rw [mul_div_cancel_left _ (ne_of_gt (gcd_pos m n))]

/- ACTUAL PROOF OF Nat.gcd_mul_lcm -/

example (m n : Nat) : gcd m n * lcm m n = m * n := by
  rw [lcm, Nat.mul_div_cancel' (Nat.dvd_trans (gcd_dvd_left m n) (Nat.dvd_mul_right m n))]