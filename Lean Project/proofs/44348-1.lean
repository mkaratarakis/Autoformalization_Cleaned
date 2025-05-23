import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a : Int} (h : a < 0) : 0 < -a := by
  have : -0 < -a := neg_lt_neg_left h
  rw [neg_zero] at this
  exact this

/- ACTUAL PROOF OF Int.neg_pos_of_neg -/

example {a : Int} (h : a < 0) : 0 < -a := by
  have : -0 < -a := Int.neg_lt_neg h
  rwa [Int.neg_zero] at this