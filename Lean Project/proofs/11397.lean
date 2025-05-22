import Init.Data.Nat.Dvd
import Init.NotationExtra
import Init.RCases
import Init.Data.Nat.Gcd

open Nat


example (y : Nat) : gcd 0 y = y := by
  rw [gcd_zero_left]

/- ACTUAL PROOF OF Nat.gcd_zero_left -/

example (y : Nat) : gcd 0 y = y := by
  rw [gcd]; rfl