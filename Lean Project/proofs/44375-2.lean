import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b : Int} (h : a ≤ -b) : b ≤ -a := by
  have h1 : -(-b) = b := neg_neg b
  have h2 := Int.neg_le_neg_left h
  rw [h1] at h2
  exact h2

/- ACTUAL PROOF OF Int.le_neg_of_le_neg -/

example {a b : Int} (h : a ≤ -b) : b ≤ -a := by
  have h := Int.neg_le_neg h
  rwa [Int.neg_neg] at h