import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat


example {a b c : Int} (h : a < b + c) : -c + a < b := by
  rw [Int.add_comm] at h
  exact Int.neg_add_lt_left_of_lt_add h