import Init.Data.Nat.Dvd
import Init.NotationExtra
import Init.RCases
import Init.Data.Nat.Gcd

open Nat


example (x y : Nat) : gcd x y = if x = 0 then y else gcd (y % x) x := by
  cases x with
  | zero =>
    simp [gcd]
  | succ n =>
    simp [gcd]
    rw [Nat.gcd_rec]

/- ACTUAL PROOF OF Nat.gcd_def -/

example (x y : Nat) : gcd x y = if x = 0 then y else gcd (y % x) x := by
  cases x <;> simp [Nat.gcd_add_one]