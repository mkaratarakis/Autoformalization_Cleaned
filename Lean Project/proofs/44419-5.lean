import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : a < c - b) : a + b < c := by
  have : a < c - b := h
  have : a + b < c - b + b := Int.add_lt_add_right this b
  rwa [add_sub_cancel] at this

/- ACTUAL PROOF OF Int.add_lt_of_lt_sub_right -/

example {a b c : Int} (h : a < c - b) : a + b < c := by
  have h := Int.add_lt_add_right h b
  rwa [Int.sub_add_cancel] at h