import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b : Int} (h : a < -b) : b < -a := by
  have h1 : -(-b) = b := by simp
  rw [h1] at h
  exact h

/- ACTUAL PROOF OF Int.lt_neg_of_lt_neg -/

example {a b : Int} (h : a < -b) : b < -a := by
  have h := Int.neg_lt_neg h
  rwa [Int.neg_neg] at h