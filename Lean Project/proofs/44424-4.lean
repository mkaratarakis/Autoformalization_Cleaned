import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b c : Int} (h : -c + a < b) : a < b + c := by
  have h1 : a < b + c := by
    apply add_lt_add_right
    exact h

/- ACTUAL PROOF OF Int.lt_add_of_neg_add_lt_right -/

example {a b c : Int} (h : -c + a < b) : a < b + c := by
  rw [Int.add_comm] at h
  exact Int.lt_add_of_sub_right_lt h