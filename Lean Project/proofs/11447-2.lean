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
    rw [gcd]
    have :  Nat.gcd (succ n) y = Nat.gcd (y % succ n) (succ n) := by simp [Nat.gcd_rec]
    rw [this]
    simp [Nat.gcd]

/- ACTUAL PROOF OF Nat.gcd_def -/

example (x y : Nat) : gcd x y = if x = 0 then y else gcd (y % x) x := by
  cases x <;> simp [Nat.gcd_add_one]