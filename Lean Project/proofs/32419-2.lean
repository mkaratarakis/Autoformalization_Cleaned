import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (n m k l : Nat) :
    (n + l) - m - (k + l) = n - m - k := by
  rw [sub_eq_add_neg, sub_eq_add_neg, ←add_assoc, add_right_comm l k, add_right_comm l m, add_neg_cancel_left]

/- ACTUAL PROOF OF Nat.add_sub_sub_add_right -/

example (n m k l : Nat) :
    (n + l) - m - (k + l) = n - m - k := by
  rw [Nat.sub_sub, Nat.sub_sub, ←Nat.add_assoc, Nat.add_sub_add_right]