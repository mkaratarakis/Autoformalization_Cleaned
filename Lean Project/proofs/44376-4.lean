import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b : Int} (h : -a ≤ b) : -b ≤ a := by
  have h' : b ≤ -a := by
    apply le_of_not_lt
    intro hb
    apply not_lt_of_ge h
    exact hb
  exact neg_le_of_le h'

/- ACTUAL PROOF OF Int.neg_le_of_neg_le -/

example {a b : Int} (h : -a ≤ b) : -b ≤ a := by
  have h := Int.neg_le_neg h
  rwa [Int.neg_neg] at h