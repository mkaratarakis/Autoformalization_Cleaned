import Init.Data.Nat.Dvd
import Init.NotationExtra
import Init.RCases
import Init.Data.Nat.Gcd

open Nat


example {m n : Nat} (H : gcd m n = 0) : n = 0 := by
  cases n with
  | zero => exact rfl
  | succ _ =>
    have : m.gcd (succ n) = 0 := H
    exact Nat.not_succ_eq_zero_iff.mp this

/- ACTUAL PROOF OF Nat.eq_zero_of_gcd_eq_zero_right -/

example {m n : Nat} (H : gcd m n = 0) : n = 0 := by
  rw [gcd_comm] at H
  exact eq_zero_of_gcd_eq_zero_left H