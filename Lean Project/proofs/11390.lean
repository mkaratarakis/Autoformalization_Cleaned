import Init.Data.Nat.Dvd
import Init.NotationExtra
import Init.RCases
import Init.Data.Nat.Gcd

open Nat


example (x y : Nat) : gcd (x + 1) y = gcd (y % (x + 1)) (x + 1) := by
  rw [gcd_rec]
  rfl

/- ACTUAL PROOF OF Nat.gcd_add_one -/

example (x y : Nat) : gcd (x + 1) y = gcd (y % (x + 1)) (x + 1) := by
  rw [gcd]; rfl