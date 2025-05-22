import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (m n : Nat) : m % n / n = 0 := by
  cases n with
  | zero =>
    rw [zero_mod]
    simp
  | succ k =>
    rw [succ_mod, Nat.div_eq_zero_iff]
    apply lt_succ_self

/- ACTUAL PROOF OF Nat.mod_div_self -/

example (m n : Nat) : m % n / n = 0 := by
  cases n
  · exact (m % 0).div_zero
  · case succ n => exact Nat.div_eq_of_lt (m.mod_lt n.succ_pos)