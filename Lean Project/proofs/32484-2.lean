import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (m n : Nat) : m % n / n = 0 := by
  cases n with
  | zero =>
    rw [zero_div]
    simp
  | succ k =>
    rw [Nat.mod_lt (le_of_lt_succ (zero_le _))]
    exact Nat.div_eq_zero_of_lt (Nat.mod_lt m (succ k))

/- ACTUAL PROOF OF Nat.mod_div_self -/

example (m n : Nat) : m % n / n = 0 := by
  cases n
  · exact (m % 0).div_zero
  · case succ n => exact Nat.div_eq_of_lt (m.mod_lt n.succ_pos)