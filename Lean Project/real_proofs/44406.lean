import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat


example {a b c : Int} (h : b < -a + c) : a + b < c := by
  have h := Int.add_lt_add_left h a
  rwa [Int.add_neg_cancel_left] at h