import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (a m n : Nat) : a ^ (m + n) = a ^ n * a ^ m := by
  induction n with
  | zero =>
    simp
  | succ d h =>
    rw [pow_succ, pow_succ, h]

/- ACTUAL PROOF OF Nat.pow_add' -/

example (a m n : Nat) : a ^ (m + n) = a ^ n * a ^ m := by
  rw [← Nat.pow_add, Nat.add_comm]