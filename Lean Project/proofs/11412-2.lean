import Init.Data.Nat.Dvd
import Init.NotationExtra
import Init.RCases
import Init.Data.Nat.Gcd

open Nat


example {m n : Nat} (H : gcd m n = 0) : n = 0 := by
  rw [gcd_zero_left] at H
  exact H

/- ACTUAL PROOF OF Nat.eq_zero_of_gcd_eq_zero_right -/

example {m n : Nat} (H : gcd m n = 0) : n = 0 := by
  rw [gcd_comm] at H
  exact eq_zero_of_gcd_eq_zero_left H