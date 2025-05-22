import Init.Data.Nat.Dvd
import Init.NotationExtra
import Init.RCases
import Init.Data.Nat.Gcd

open Nat


example (n : Nat) : gcd n n = n := by
  cases n with
  | zero =>
    show gcd 0 0 = 0
    rw [gcd_zero_left]
  | succ k =>
    calc
      gcd (succ k) (succ k)
        = gcd ((succ k) % (succ k)) (succ k) := by rw [gcd_mod]
      _ = gcd 0 (succ k) := by rw [mod_self]
      _ = succ k := by rw [gcd_zero_right]

/- ACTUAL PROOF OF Nat.gcd_self -/

example (n : Nat) : gcd n n = n := by
  cases n <;> simp [gcd_succ]