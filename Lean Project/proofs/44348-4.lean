import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a : Int} (h : a < 0) : 0 < -a := by
  have h1 := neg_lt_neg h
  have h2 := neg_zero
  rw [h2] at h1
  exact h1

/- ACTUAL PROOF OF Int.neg_pos_of_neg -/

example {a : Int} (h : a < 0) : 0 < -a := by
  have : -0 < -a := Int.neg_lt_neg h
  rwa [Int.neg_zero] at this