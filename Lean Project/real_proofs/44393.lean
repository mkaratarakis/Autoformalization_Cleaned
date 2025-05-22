import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat


example {a b : Int} (h : a < b) : a - b < 0 := by
  have h := Int.add_lt_add_right h (-b)
  rwa [Int.add_right_neg] at h