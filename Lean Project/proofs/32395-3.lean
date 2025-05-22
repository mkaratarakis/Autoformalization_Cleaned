import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example : 0 < k → n < k + n := by
  intro h
  exact lt_add_of_pos_right n h

/- ACTUAL PROOF OF Nat.lt_add_of_pos_left -/

example : 0 < k → n < k + n := by
  rw [Nat.add_comm]; exact Nat.lt_add_of_pos_right