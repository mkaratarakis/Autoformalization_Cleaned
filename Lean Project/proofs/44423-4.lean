import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : a < b + c) : -b + a < c := by
  have h1 : a + -b < c := by
      linarith

/- ACTUAL PROOF OF Int.neg_add_lt_left_of_lt_add -/

example {a b c : Int} (h : a < b + c) : -b + a < c := by
  rw [Int.add_comm]
  exact Int.sub_left_lt_of_lt_add h