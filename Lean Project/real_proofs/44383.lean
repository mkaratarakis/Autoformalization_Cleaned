import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat


example : 0 < natAbs a ↔ a ≠ 0 := by
  rw [Nat.pos_iff_ne_zero, Ne, natAbs_eq_zero]