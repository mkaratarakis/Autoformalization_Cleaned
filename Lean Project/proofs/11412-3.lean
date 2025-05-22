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
    rw [gcd_rec (n+1) m] at this
    rw [Nat.min_rec_rec] at this
    cases this
    case inl h => exact Nat.noConfusion h
    case inr h => exact Nat.noConfusion h

/- ACTUAL PROOF OF Nat.eq_zero_of_gcd_eq_zero_right -/

example {m n : Nat} (H : gcd m n = 0) : n = 0 := by
  rw [gcd_comm] at H
  exact eq_zero_of_gcd_eq_zero_left H