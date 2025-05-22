import Init.Data.Nat.Dvd
import Init.NotationExtra
import Init.RCases
import Init.Data.Nat.Gcd

open Nat



example (x y : Nat) : gcd (succ x) y = gcd (y % succ x) (succ x) := by
  rw [gcd]; rfl