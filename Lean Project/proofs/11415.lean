import Init.Data.Nat.Dvd
import Init.NotationExtra
import Init.RCases
import Init.Data.Nat.Gcd

open Nat


example (x y : Nat) : gcd (succ x) y = gcd (y % succ x) (succ x) := by
  rw [gcd_rec]
  rw [gcd_rec]
  rfl

/- ACTUAL PROOF OF Nat.gcd_succ -/

example (x y : Nat) : gcd (succ x) y = gcd (y % succ x) (succ x) := by
  rw [gcd]; rfl