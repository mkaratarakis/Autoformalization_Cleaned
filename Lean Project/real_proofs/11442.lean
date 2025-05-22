import Init.Data.Nat.Dvd
import Init.NotationExtra
import Init.RCases
import Init.Data.Nat.Gcd

open Nat



example (n : Nat) : gcd n n = n := by
  cases n <;> simp [gcd_succ]