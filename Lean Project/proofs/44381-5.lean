import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example (a : Int) {b : Int} (h : 0 < b) : a < b + a := by
  exact add_lt_add_right h a

/- ACTUAL PROOF OF Int.lt_add_of_pos_left -/

example (a : Int) {b : Int} (h : 0 < b) : a < b + a := by
  have : 0 + a < b + a := Int.add_lt_add_right h a
  rwa [Int.zero_add] at this