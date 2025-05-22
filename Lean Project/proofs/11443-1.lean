import Init.Data.Nat.Dvd
import Init.NotationExtra
import Init.RCases
import Init.Data.Nat.Gcd

open Nat


example (m n k : Nat) : gcd m (n + k * m) = gcd m n := by
  rw [gcd_rec]
  rw [add_mul_mod_self]
  rw [gcd_rec]
  rfl

/- ACTUAL PROOF OF Nat.gcd_add_mul_self -/

example (m n k : Nat) : gcd m (n + k * m) = gcd m n := by
  simp [gcd_rec m (n + k * m), gcd_rec m n]