import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example {m n : Nat} : m ^ (n + 1) = m * m ^ n := by
  rw [Nat.pow_succ']
  rfl

/- ACTUAL PROOF OF Nat.pow_add_one' -/

example {m n : Nat} : m ^ (n + 1) = m * m ^ n := by
  rw [Nat.pow_add_one, Nat.mul_comm]