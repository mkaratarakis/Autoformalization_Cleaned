import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : -b + a < c) : a < b + c := by
  have : a < b + c := by
    rw [← neg_add_rev] at h
    exact Int.add_lt_add_right h b
  exact this

/- ACTUAL PROOF OF Int.lt_add_of_neg_add_lt_left -/

example {a b c : Int} (h : -b + a < c) : a < b + c := by
  rw [Int.add_comm] at h
  exact Int.lt_add_of_sub_left_lt h