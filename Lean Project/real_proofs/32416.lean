import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat



example (n m : Nat) : n - m + min n m = n := by
  rw [Nat.sub_eq_sub_min, Nat.sub_add_cancel (Nat.min_le_left ..)]