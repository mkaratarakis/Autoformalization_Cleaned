import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat


example : natAbs a = n ↔ (a - n) * (a + n) = 0 := by
  rw [natAbs_eq_iff, Int.mul_eq_zero, ← Int.sub_neg, Int.sub_eq_zero, Int.sub_eq_zero]