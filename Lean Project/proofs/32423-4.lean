import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example {n m k : Nat} (h : k ≤ n) : n + m - k = n - k + m := by
  rw [add_sub_assoc']
  rw [add_comm (n - k)]
  rw [sub_add_cancel]

/- ACTUAL PROOF OF Nat.sub_add_comm -/

example {n m k : Nat} (h : k ≤ n) : n + m - k = n - k + m := by
  rw [Nat.sub_eq_iff_eq_add (Nat.le_trans h (Nat.le_add_right ..))]
  rwa [Nat.add_right_comm, Nat.sub_add_cancel]