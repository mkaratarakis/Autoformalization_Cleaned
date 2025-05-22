import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (a m n : Nat) : a ^ (m + n) = a ^ n * a ^ m := by
  rw [← pow_add]
  rw [add_comm]
  rfl

/- ACTUAL PROOF OF Nat.pow_add' -/

example (a m n : Nat) : a ^ (m + n) = a ^ n * a ^ m := by
  rw [← Nat.pow_add, Nat.add_comm]