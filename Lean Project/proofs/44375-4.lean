import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b : Int} (h : a ≤ -b) : b ≤ -a := by
  have h1 : b = - -b := neg_neg b
  rw [h1]
  apply neg_le_neg
  exact h

/- ACTUAL PROOF OF Int.le_neg_of_le_neg -/

example {a b : Int} (h : a ≤ -b) : b ≤ -a := by
  have h := Int.neg_le_neg h
  rwa [Int.neg_neg] at h