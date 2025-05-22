import Init.Data.Nat.Dvd
import Init.NotationExtra
import Init.RCases
import Init.Data.Nat.Gcd

open Nat


example (m n : Nat) : gcd n (m * n) = n := by
  rw [gcd_comm]
  have h : n ∣ m * n := by
    exact dvd_mul_right n m
  exact gcd_eq_right_of_dvd_right h

/- ACTUAL PROOF OF Nat.gcd_mul_left_right -/

example (m n : Nat) : gcd n (m * n) = n := by
  rw [gcd_comm, gcd_mul_left_left]