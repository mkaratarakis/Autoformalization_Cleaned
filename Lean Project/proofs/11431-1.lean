import Init.Data.Nat.Dvd
import Init.NotationExtra
import Init.RCases
import Init.Data.Nat.Gcd

open Nat


example (m n : Nat) : gcd (gcd n m) m = gcd n m := by
  rw [gcd.comm (gcd n m) m]
  rw [gcd.assoc]
  rw [gcd.comm]
  rfl

/- ACTUAL PROOF OF Nat.gcd_gcd_self_left_right -/

example (m n : Nat) : gcd (gcd n m) m = gcd n m := by
  rw [gcd_comm, gcd_gcd_self_right_right]