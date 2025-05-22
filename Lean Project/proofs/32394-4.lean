import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example {n : Nat} : n + k < n + m → k < m := by
  intros h
  exact Nat.sub_lt_self_iff_lt_add.mp (Nat.sub_lt h (Nat.le_add_right n k))

/- ACTUAL PROOF OF Nat.lt_of_add_lt_add_left -/

example {n : Nat} : n + k < n + m → k < m := by
  rw [Nat.add_comm n, Nat.add_comm n]; exact Nat.lt_of_add_lt_add_right