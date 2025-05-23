import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a : Int} (h : 0 ≤ a) : -a ≤ 0 := by
  exact le_trans (neg_nonneg_of_nonneg h) (neg_zero 0).le

/- ACTUAL PROOF OF Int.neg_nonpos_of_nonneg -/

example {a : Int} (h : 0 ≤ a) : -a ≤ 0 := by
  have : -a ≤ -0 := Int.neg_le_neg h
  rwa [Int.neg_zero] at this