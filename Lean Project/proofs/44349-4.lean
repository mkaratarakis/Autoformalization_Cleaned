import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a : Int} (h : 0 ≤ a) : -a ≤ 0 := by
  have h1 : 0 ≤ -a := by
    apply neg_nonneg
    exact h
  exact le_of_eq (neg_nonpos.2 h1).mp (neg_zero 0).le

/- ACTUAL PROOF OF Int.neg_nonpos_of_nonneg -/

example {a : Int} (h : 0 ≤ a) : -a ≤ 0 := by
  have : -a ≤ -0 := Int.neg_le_neg h
  rwa [Int.neg_zero] at this