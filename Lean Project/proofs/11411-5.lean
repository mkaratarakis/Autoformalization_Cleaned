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
  rw [Nat.gcd_rec]
  rfl

/- ACTUAL PROOF OF Nat.gcd_mul_left_right -/

example (m n : Nat) : gcd n (m * n) = n := by
  rw [gcd_comm, gcd_mul_left_left]