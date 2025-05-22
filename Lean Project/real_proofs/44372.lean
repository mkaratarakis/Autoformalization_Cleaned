import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat


example {a : Int} (H : a ≤ 0) : (natAbs a : Int) = -a := by
  rw [← natAbs_neg, natAbs_of_nonneg (Int.neg_nonneg_of_nonpos H)]