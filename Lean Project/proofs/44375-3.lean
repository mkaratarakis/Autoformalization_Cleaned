import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b : Int} (h : a ≤ -b) : b ≤ -a := by
  have : -b ≤ a := le_of_neg_le_neg h
  exact neg_le.mp this

/- ACTUAL PROOF OF Int.le_neg_of_le_neg -/

example {a b : Int} (h : a ≤ -b) : b ≤ -a := by
  have h := Int.neg_le_neg h
  rwa [Int.neg_neg] at h