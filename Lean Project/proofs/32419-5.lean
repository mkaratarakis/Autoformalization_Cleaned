import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (n m k l : Nat) :
    (n + l) - m - (k + l) = n - m - k := by
  rw [sub_sub_eq_sub_add]
  rw [add_right_comm m l]
  rw [add_assoc]
  rw [add_tsub_assoc_of_le (add_le_add_right (le_add_left_of_sub_le (le_of_eq (add_right_comm k l).symm)))]
  rw [add_comm]
  rw [add_right_comm m k]
  rw [add_tsub_assoc_of_le (add_le_add_left (le_of_eq (add_right_comm k l).symm))]
  rw [add_comm]
  rw [add_right_comm m k]

/- ACTUAL PROOF OF Nat.add_sub_sub_add_right -/

example (n m k l : Nat) :
    (n + l) - m - (k + l) = n - m - k := by
  rw [Nat.sub_sub, Nat.sub_sub, ←Nat.add_assoc, Nat.add_sub_add_right]