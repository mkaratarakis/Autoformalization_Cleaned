import Init.Data.Nat.Dvd
import Init.NotationExtra
import Init.RCases
import Init.Data.Nat.Gcd

open Nat



example (m n : Nat) : gcd m (gcd n m) = gcd n m := by
  rw [gcd_comm n m, gcd_gcd_self_right_left]