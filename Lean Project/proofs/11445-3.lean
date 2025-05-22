import Init.Data.Nat.Dvd
import Init.NotationExtra
import Init.RCases
import Init.Data.Nat.Gcd

open Nat


example (m n : Nat) : gcd (gcd m n) m = gcd m n := by
  rw [gcd_comm]
  rw [gcd_rec]
  rfl

/- ACTUAL PROOF OF Nat.gcd_gcd_self_left_left -/

example (m n : Nat) : gcd (gcd m n) m = gcd m n := by
  rw [gcd_comm m n, gcd_gcd_self_left_right]