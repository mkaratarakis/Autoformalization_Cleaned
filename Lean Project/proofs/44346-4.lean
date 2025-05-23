import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a : Int} (h : 0 < a) : -a < 0 := by
  have : -a + a < 0 + a := add_left_neg h
  simpa using this

/- ACTUAL PROOF OF Int.neg_neg_of_pos -/

example {a : Int} (h : 0 < a) : -a < 0 := by
  have : -a < -0 := Int.neg_lt_neg h
  rwa [Int.neg_zero] at this