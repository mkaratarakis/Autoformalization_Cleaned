import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a : Int} (h : a ≤ 0) : 0 ≤ -a := by
  exact Int.neg_nonneg_of_nonpos h

/- ACTUAL PROOF OF Int.neg_nonneg_of_nonpos -/

example {a : Int} (h : a ≤ 0) : 0 ≤ -a := by
  have : -0 ≤ -a := Int.neg_le_neg h
  rwa [Int.neg_zero] at this