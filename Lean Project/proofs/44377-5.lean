import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b : Int} (h : -a < b) : -b < a := by
  have h1 : -b < -(-a) := by
    apply neg_lt_neg_of_lt
    exact h
  rw [neg_neg] at h1
  exact h1

/- ACTUAL PROOF OF Int.neg_lt_of_neg_lt -/

example {a b : Int} (h : -a < b) : -b < a := by
  have h := Int.neg_lt_neg h
  rwa [Int.neg_neg] at h