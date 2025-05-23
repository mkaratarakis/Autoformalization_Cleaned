import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : a < b + c) : -c + a < b := by
  rw [Int.add_comm b c] at h
  have h' : a - c < b := by
    simp [Int.sub_eq_add_neg]
    exact Int.add_lt_add_left h _
  rwa [Int.sub_eq_add_neg, Int.add_comm]

/- ACTUAL PROOF OF Int.neg_add_lt_right_of_lt_add -/

example {a b c : Int} (h : a < b + c) : -c + a < b := by
  rw [Int.add_comm] at h
  exact Int.neg_add_lt_left_of_lt_add h