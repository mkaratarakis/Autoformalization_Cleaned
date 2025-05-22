import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat



example : n < k + n → 0 < k := by
  rw [Nat.add_comm]; exact Nat.pos_of_lt_add_right