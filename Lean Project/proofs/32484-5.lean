import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (m n : Nat) : m % n / n = 0 := by
  cases n with
  | zero =>
    rw [mod_zero]
    exact div_by_zero _
  | succ k =>
    have h : m % (succ k) < succ k := Nat.mod_lt _ _
    rw [Nat.div_eq_zero_of_lt h]

/- ACTUAL PROOF OF Nat.mod_div_self -/

example (m n : Nat) : m % n / n = 0 := by
  cases n
  · exact (m % 0).div_zero
  · case succ n => exact Nat.div_eq_of_lt (m.mod_lt n.succ_pos)