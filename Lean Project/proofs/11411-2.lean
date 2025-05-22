import Init.Data.Nat.Dvd
import Init.NotationExtra
import Init.RCases
import Init.Data.Nat.Gcd

open Nat


example (m n : Nat) : gcd n (m * n) = n := by
  rw [gcd_comm]
  have h : n ∣ m * n := by
    use m
    rfl
  have h' : m * n ∣ m * n := by
    dvd_refl
  rw [greatest_common_divisor]
  exact n

/- ACTUAL PROOF OF Nat.gcd_mul_left_right -/

example (m n : Nat) : gcd n (m * n) = n := by
  rw [gcd_comm, gcd_mul_left_left]