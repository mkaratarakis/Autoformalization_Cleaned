import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (m n k : Nat) : m - n - k = m - k - n := by
  rw [sub_sub, sub_sub]
  rw [add_comm]
  rfl

/- ACTUAL PROOF OF Nat.sub_right_comm -/

example (m n k : Nat) : m - n - k = m - k - n := by
  rw [Nat.sub_sub, Nat.sub_sub, Nat.add_comm]