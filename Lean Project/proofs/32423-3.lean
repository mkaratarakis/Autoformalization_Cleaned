import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example {n m k : Nat} (h : k ≤ n) : n + m - k = n - k + m := by
  have h' : k ≤ n + m := Nat.le_add_right n k m
  rw [show n + m - k = n + m + -k from (add_sub_assoc n m k).symm]
  rw [add_comm (n - k) k]
  rw [sub_add_cancel n k]

/- ACTUAL PROOF OF Nat.sub_add_comm -/

example {n m k : Nat} (h : k ≤ n) : n + m - k = n - k + m := by
  rw [Nat.sub_eq_iff_eq_add (Nat.le_trans h (Nat.le_add_right ..))]
  rwa [Nat.add_right_comm, Nat.sub_add_cancel]