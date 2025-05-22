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
        = gcd 0 (succ k) := by rw [gcd_eq_right_of_dvd (dvd_refl (succ k))]
      _ = succ k := by rw [gcd_zero_right]

/- ACTUAL PROOF OF Nat.gcd_self -/

example (n : Nat) : gcd n n = n := by
  cases n <;> simp [gcd_succ]