import Init.Data.Nat.Dvd
import Init.NotationExtra
import Init.RCases
import Init.Data.Nat.Gcd

open Nat


example (m n k : Nat) : gcd m (n + k * m) = gcd m n := by
  rw [gcd_rec]
  have : (n + k * m) % m = n % m := by simp [Nat.add_mul_mod_self]
  rw [this]
  rw [gcd_rec]

/- ACTUAL PROOF OF Nat.gcd_add_mul_self -/

example (m n k : Nat) : gcd m (n + k * m) = gcd m n := by
  simp [gcd_rec m (n + k * m), gcd_rec m n]