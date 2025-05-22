import Init.Data.Nat.Dvd
import Init.NotationExtra
import Init.RCases
import Init.Data.Nat.Gcd

open Nat



example (y : Nat) : gcd 0 y = y := by
  rw [gcd]; rfl