import Init.Data.Nat.Dvd
import Init.NotationExtra
import Init.RCases
import Init.Data.Nat.Gcd

open Nat


example {m n : Nat} (H : n ∣ m) : gcd m n = n := by
  rw [gcd_comm]
  exact dvd_gcd H

/- ACTUAL PROOF OF Nat.gcd_eq_right -/

example {m n : Nat} (H : n ∣ m) : gcd m n = n := by
  rw [gcd_comm, gcd_eq_left H]